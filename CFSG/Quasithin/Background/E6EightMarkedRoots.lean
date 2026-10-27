module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.Quasithin.E6

variable (K : Type) [Field K]

@[expose] def sp4LongRoot : Subgroup ↥(CFSG.Open.StatedSp 2 K) :=
  Subgroup.closure {element | ∃ parameter : K,
    ((element : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.of fun row column => (if row = column then 1 else 0) +
        (if row = Sum.inl 0 ∧ column = Sum.inr 0 then parameter else 0)}

@[expose] def sp4ShortRoot : Subgroup ↥(CFSG.Open.StatedSp 2 K) :=
  Subgroup.closure {element | ∃ parameter : K,
    ((element : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.of fun row column => (if row = column then 1 else 0) +
        (if row = Sum.inl 0 ∧ column = Sum.inl 1 then parameter else 0) -
        (if row = Sum.inr 1 ∧ column = Sum.inr 0 then parameter else 0)}

@[expose] def IsMarkedSp4Root {H : Type} [Group H]
    (n : ℕ) (ambient root : Subgroup H) : Prop :=
  root ≤ ambient ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
    Nat.card K = 2 ^ n ∧
    ∃ marking : ↥ambient ≃* ↥(CFSG.Open.StatedSp 2 K),
      ∃ conjugator : ↥(CFSG.Open.StatedSp 2 K),
        (root.subgroupOf ambient).map marking.toMonoidHom =
          (sp4LongRoot K).map (MulAut.conj conjugator).toMonoidHom ∨
        (root.subgroupOf ambient).map marking.toMonoidHom =
          (sp4ShortRoot K).map (MulAut.conj conjugator).toMonoidHom

end CFSG.Quasithin.E6
