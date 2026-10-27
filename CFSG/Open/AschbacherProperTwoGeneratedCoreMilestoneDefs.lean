module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open Matrix

@[expose] noncomputable def properTwoGenCoreGamma {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    (k : ℕ) : Subgroup G :=
  ⨆ (Q : Subgroup G) (_ : Q ≤ S) (_ : k ≤ pRank 2 Q), Subgroup.normalizer (Q : Set G)

@[expose] def properTwoGenCoreJ1Gens : Set (Matrix (Fin 7) (Fin 7) (ZMod 11)) :=
  {!![0, 7, 9, 9, 10, 7, 9;
      7, 0, 1, 4, 3, 3, 4;
      9, 1, 2, 8, 3, 6, 2;
      9, 4, 8, 10, 1, 6, 0;
      10, 3, 3, 1, 8, 9, 1;
      7, 3, 6, 6, 9, 1, 3;
      9, 4, 2, 0, 1, 3, 0],
    !![5, 7, 1, 8, 5, 8, 2;
      10, 4, 10, 0, 3, 3, 8;
      5, 10, 8, 9, 1, 2, 1;
      2, 3, 3, 6, 1, 2, 9;
      7, 4, 7, 2, 10, 7, 3;
      3, 9, 0, 4, 2, 3, 5;
      3, 4, 3, 3, 9, 4, 9]}

@[expose] def properTwoGenCoreJ1 : Subgroup (GL (Fin 7) (ZMod 11)) :=
  Subgroup.closure {A | (A : Matrix (Fin 7) (Fin 7) (ZMod 11)) ∈ properTwoGenCoreJ1Gens}

end CFSG.Open
