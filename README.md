# setoid-universe

A universe for proof-relevant setoids, only using Coq's indexed inductive types.

-------

The most straightforward definition would require complicated stuff such as
"double induction-recursion" or "recursive-recursive functions", but we use a
bunch of tricks to make it work with indexed inductive types only.

As a result, we get a shallow embedding of an observational type theory that
supports:
- Pi-types, Sigma-types, W-types, Integers
- Impredicative propositions
- Equality proofs in Prop that compute
- Propositional UIP (but not definitional UIP!)
- Function extensionality, proposition extensionality
- Large elimination of the accessibility predicate
- Quotients

In other words, we have the full CIC augmented with extensionality principles
and quotients. I think that all the expected beta/eta equalities hold by
definition, but I haven't checked thoroughly.

-------

Alternatively, we can put the equalities in Type, which provides us with
unique choice/function comprehension at the cost of losing impredicative
quantification. Tradeoffs...