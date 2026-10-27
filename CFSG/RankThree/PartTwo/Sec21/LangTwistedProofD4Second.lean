module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Geom

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley LangTwistedProof



@[expose] def d4TrialityY0Elt (K : Type) [Field K] (σ : K ≃+* K) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ⟨d4TrialityY0 K, d4TrialityY0_mem σ.toRingHom⟩

@[expose] def KF82D4SecondCentY0 : Prop :=
  ∀ n : ℕ, Odd n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
      IsoPGUThree (Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ)) (2 ^ n)

namespace LangTwistedProof

theorem mulAut_congr_eq {X : Type*} [Group X] (β α : MulAut X) :
    MulAut.congr β α = β * α * β⁻¹ :=
  MulEquiv.ext fun _ => rfl

theorem fieldActor_pow_three {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    rw [pow_three, RingAut.mul_apply, RingAut.mul_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [← h1, hσ3, fieldActor_one]

end LangTwistedProof

theorem kF82D4SecondCent_of_y0
    (hY : D4SecondCentIrred) (hY0 : KF82D4SecondCentY0) : KF82D4SecondCent := by
  intro n hn K _ _ σ hK hσ y hyσ hy3 hnstd
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀def
  have hσ₀3 : σ₀ ^ 3 = 1 := fieldActor_pow_three hK hσ
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hg3 : (MulAut.conj y * σ₀) ^ 3 = 1 := by
    rw [conj_mul_pow_three σ₀ hσ₀3, hyσ, hyσ, ← pow_three', hy3', map_one]
  obtain ⟨h, y', hy', hyy⟩ := exists_conj_eq_of_geom d4TrialityGeomClasses_holds
    d4DiagramCentIrred_holds hY hK hσ y hg3
  rcases hy' with hy1 | hy0
  ·
    exfalso
    apply hnstd
    have hy'1 : y' = 1 := Subtype.ext hy1
    refine ⟨MulAut.conj h⁻¹, Or.inl ?_⟩
    rw [hyy, hy'1, map_one, one_mul]
  ·
    have hy'0 : y' = d4TrialityY0Elt K σ := Subtype.ext hy0
    obtain ⟨F, hF, hFf, hFc, ⟨e⟩⟩ := hY0 n hn K σ hK hσ
    refine ⟨F, hF, hFf, hFc, ⟨?_⟩⟩
    rw [hyy, hy'0, ← mulAut_congr_eq]
    exact (Sec4.autFixCongrEquiv _ _).trans e

end CFSG.RankThree.PartTwo.Sec8
