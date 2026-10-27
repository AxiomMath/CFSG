module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel

public section

open scoped commutatorElement Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] def H91Clause3 (n : ℕ) (T : Subgroup (MulAut (PairN n))) (v₁ : PairN n) : Prop :=
      (Mg n ⊓ centSub (Subgroup.zpowers v₁) = twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁)) ∧
        (∃ E : Subgroup (MulAut (PairN n)), CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (n - 1) ∧
          IsExtOf (Mg n ⊓ centSub (Subgroup.zpowers v₁)) E (GL (Fin (n - 1)) (ZMod 2))) ∧
        commOn (V1n n) (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁))) = V1n n ∧
        commOn (V2n n) (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁))) =
          V2n n ⊓ perpN n (Subgroup.zpowers v₁) ∧
        (V2n n ⊓ perpN n (Subgroup.zpowers v₁)).relIndex (V2n n) = 2 ∧
        InducesOn (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁)))
          (commOn (V2n n) (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers v₁)))) ⊥
          (Multiplicative (Fin (n - 1) → ZMod 2)) (natSub (n - 1) (ZMod 2) ⊤) ∧
        T ⊓ stabSub (V1n n) = T ⊓ centSub (Subgroup.zpowers v₁) ∧
        IsSylowIn 2 (T ⊓ stabSub (V1n n)) (Mg n ⊓ centSub (Subgroup.zpowers v₁)))

@[expose] def H91Clause4 (n : ℕ) (T : Subgroup (MulAut (PairN n))) (v₁ v₂ : PairN n) : Prop :=
          v₁ * v₂ ∈ Oorb n 2 ∧
          (∃ S : Subgroup (MulAut (PairN n)),
            IsSylowIn 2 S (Mg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ∧
            S ⊓ Lg n = T ⊓ centSub (Subgroup.zpowers (v₁ * v₂)) ∧
            ∃ t ∈ S, t ∉ Lg n ∧ t ^ 2 = 1 ∧ t v₁ = v₂ ∧ t v₂ = v₁ ∧
            Mg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂)) =
              Subgroup.zpowers t ⊔ twoResidual (Lg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ∧
            Nonempty (↥(Mg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) ≃*
              MulAut (GL (Fin (n - 1)) (ZMod 2))) ∧
            twoResidual (Lg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))) =
              twoResidual (Mg n ⊓ centSub (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
            IsSylowIn 2 (T ⊓ centSub (Subgroup.zpowers (v₁ * v₂)))
              (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))))) ∧
          (V1n n = Subgroup.zpowers v₁ ⊔ (V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
            Subgroup.zpowers v₁ ⊓ (V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) = ⊥ ∧
            V2n n = Subgroup.zpowers v₂ ⊔ (V2n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ∧
            Subgroup.zpowers v₂ ⊓ (V2n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) = ⊥) ∧
          InducesOn (twoResidual (Lg n ⊓ centSub (Subgroup.zpowers (v₁ * v₂))))
            (V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)) ⊥
            (Multiplicative (Fin (n - 1) → ZMod 2)) (natSub (n - 1) (ZMod 2) ⊤) ∧
          ((∀ w ∈ V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), w ≠ 1 →
              ∃ w' ∈ V2n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), polarN n w w' ≠ 0) ∧
            (∀ w' ∈ V2n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), w' ≠ 1 →
              ∃ w ∈ V1n n ⊓ perpN n (Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂), polarN n w w' ≠ 0))

end CFSG.ASVolI.ChH
