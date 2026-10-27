module

public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Fact10_2_7Six : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Mb L₁ L₂ : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W) (τ : MulAut W),
      W₁ ⊔ W₂ = ⊤ → L₁ ≤ Mb → L₂ ≤ Mb →
      Mb ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)) →
      L₂ ≤ Subgroup.centralizer (L₁ : Set (MulAut W)) →
      (∀ x ∈ L₁, ∀ w ∈ W₂, x w = w) → (∀ x ∈ L₂, ∀ w ∈ W₁, x w = w) →
      DirectSumOfCopies L₁ W₁ ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 →
      τ ∈ Mb → L₁.map (MulAut.conj τ).toMonoidHom = L₂ → W₁.map (τ : W →* W) = W₂ →
      CFSG.pCore 2 ↥Mb = ⊥ →
      (Nonempty (↥(twoResidual (Mb ⊓ Subgroup.centralizer
          ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)))) ≃* Multiplicative (ZMod 5)) ∨
        Nonempty (↥(twoResidual (Mb ⊓ Subgroup.centralizer
          ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)))) ≃*
            Multiplicative (ZMod 5 × ZMod 5))) →
      rk W = 24 ∧ E3.mParam Mb = 4 ∧ E3.aParam Mb = 2 ∧ E3.nPrime Mb = 4 ∧
      (∀ x ∈ Mb, x ≠ 1 → rkIdx (fixV (Subgroup.zpowers x)) ≤ 4 →
        orderOf x = 2 ∧ (W₁ ≤ fixV (Subgroup.zpowers x) ∨ W₂ ≤ fixV (Subgroup.zpowers x))) ∧
      ∀ A ∈ E3.aSet 2 Mb, (∀ a ∈ A, ∀ w ∈ W₁, a w ∈ W₁) ∧ (∀ a ∈ A, ∀ w ∈ W₂, a w ∈ W₂) ∧
        E3.mQuot A (A ⊓ fixingSubgroup (MulAut W) (W₁ : Set W)) ≤ 2 ∧
        E3.mQuot A (A ⊓ fixingSubgroup (MulAut W) (W₂ : Set W)) ≤ 2

end CFSG.Quasithin.Vol2.Ch10.SecB
