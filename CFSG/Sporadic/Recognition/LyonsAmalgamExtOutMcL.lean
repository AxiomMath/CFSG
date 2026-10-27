module

public import CFSG.Sporadic.Recognition.LyonsAmalgamExtIndexTwo
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtOut
public import CFSG.Sporadic.Recognition.LyonsAS4NormQuot
public import CFSG.Sporadic.Recognition.McLMultiplierCert

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup CFSG.Blueprint

section Center


theorem center_eq_bot_of_equiv_mcl {K : Type} [Group K] (e : K ≃* NativeSporadic.McL) :
    Subgroup.center K = ⊥ := by
  have hs : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.McL.isSimpleGroup_McL e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative K := Subgroup.center_eq_top_iff.mp h
    have hp : (Nat.card K).Prime := Group.is_simple_iff_prime_card.mp hs
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL] at hp
    exact absurd hp (by norm_num)

end Center

section McL


theorem card_mulAut_of_equiv_mcl {K : Type} [Group K] (e : K ≃* NativeSporadic.McL) :
    Nat.card (MulAut K) = 2 * Nat.card K :=
  card_mulAut_of_outer (center_eq_bot_of_equiv_mcl e) (outer_card_of_equiv_mcl e)

theorem card_mulAut_le_of_centerQuot_mcl {M : Type} [Group M] [Group.IsPerfect M]
    (e : M ⧸ Subgroup.center M ≃* NativeSporadic.McL) :
    Nat.card (MulAut M) ≤ 2 * Nat.card (M ⧸ Subgroup.center M) := by
  have : Finite (M ⧸ Subgroup.center M) := Finite.of_equiv _ e.symm.toEquiv
  calc Nat.card (MulAut M) ≤ Nat.card (MulAut (M ⧸ Subgroup.center M)) :=
        card_mulAut_le_of_centerQuot (MulEquiv.refl _)
    _ = 2 * Nat.card (M ⧸ Subgroup.center M) := card_mulAut_of_equiv_mcl e

end McL

section Perfect

theorem isPerfect_mclCover : Group.IsPerfect McLMultiplier.MclCover :=
  CFSG.LieType.Multipliers.presentedCover_isPerfect McLMultiplier.mclCommW_mem_commutator

end Perfect

section Cover


theorem nonempty_centerQuot_mulEquiv_mclCover :
    Nonempty (McLMultiplier.MclCover ⧸ Subgroup.center McLMultiplier.MclCover ≃*
      NativeSporadic.McL) := by
  have hP := McLMultiplier.isPresentation_mclGen_of_certificate
  have hwg := McLMultiplier.lift_mclCommW_of_certificate
  have hS : Subgroup.center CFSG.Sporadic.McL.J = ⊥ :=
    center_eq_bot_of_equiv_mcl CFSG.Sporadic.McL.mclEquivJ.symm
  exact ⟨(centerQuotMulEquivOfCentralKer (CFSG.LieType.Multipliers.coverMap hP hwg)
    (CFSG.LieType.Multipliers.coverMap_surjective hP hwg)
    (CFSG.LieType.Multipliers.coverMap_ker_le_center hP hwg) hS).trans
    CFSG.Sporadic.McL.mclEquivJ.symm⟩

theorem finite_mclCover : Finite McLMultiplier.MclCover :=
  McLMultiplier.card_presentedCover_le_of_certificate.1

theorem card_center_mclCover : Nat.card (Subgroup.center McLMultiplier.MclCover) = 3 := by
  have hP := McLMultiplier.isPresentation_mclGen_of_certificate
  have hwg := McLMultiplier.lift_mclCommW_of_certificate
  have hS : Subgroup.center CFSG.Sporadic.McL.J = ⊥ :=
    center_eq_bot_of_equiv_mcl CFSG.Sporadic.McL.mclEquivJ.symm
  rw [← ker_eq_center_of_central_ker (CFSG.LieType.Multipliers.coverMap hP hwg)
    (CFSG.LieType.Multipliers.coverMap_surjective hP hwg)
    (CFSG.LieType.Multipliers.coverMap_ker_le_center hP hwg) hS,
    ← Nat.card_congr (CFSG.LieType.Multipliers.griessHopfMultiplierEquivKer hP
      McLMultiplier.mclCommW_mem_commutator hwg).toEquiv]
  exact McLMultiplier.card_griessHopfMultiplier_J_of_certificate

theorem finite_of_mulEquiv_mclCover {M : Type*} [Group M] (φ : M ≃* McLMultiplier.MclCover) :
    Finite M :=
  have := finite_mclCover
  Finite.of_equiv _ φ.symm.toEquiv

theorem card_center_of_mulEquiv_mclCover {M : Type*} [Group M]
    (φ : M ≃* McLMultiplier.MclCover) : Nat.card (Subgroup.center M) = 3 := by
  rw [← card_center_mclCover,
    ← Subgroup.card_map_of_injective (f := (φ : M →* McLMultiplier.MclCover))
      (K := Subgroup.center M) φ.injective,
    Subgroup.map_center_eq φ]

end Cover

section CoverBound


theorem card_mulAut_le_mclCover :
    Nat.card (MulAut McLMultiplier.MclCover) ≤
      2 * Nat.card (McLMultiplier.MclCover ⧸ Subgroup.center McLMultiplier.MclCover) := by
  obtain ⟨e⟩ := nonempty_centerQuot_mulEquiv_mclCover
  have := isPerfect_mclCover
  exact card_mulAut_le_of_centerQuot_mcl e

theorem card_mulAut_le_of_mulEquiv_mclCover {M : Type} [Group M]
    (φ : M ≃* McLMultiplier.MclCover) :
    Nat.card (MulAut M) ≤ 2 * Nat.card (M ⧸ Subgroup.center M) := by
  obtain ⟨e⟩ := nonempty_centerQuot_mulEquiv_mclCover
  have hperf := isPerfect_mclCover
  have : Group.IsPerfect M :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  exact card_mulAut_le_of_centerQuot_mcl
    ((QuotientGroup.congr (Subgroup.center M) (Subgroup.center McLMultiplier.MclCover) φ
      (Subgroup.map_center_eq φ)).trans e)

theorem exists_mulEquiv_extend_of_mclCover {B₁ B₂ : Type} [Group B₁] [Group B₂]
    {M₁ : Subgroup B₁} {M₂ : Subgroup B₂} (hM₁ : M₁.index = 2) (hM₂ : M₂.index = 2)
    (φ₂ : M₂ ≃* McLMultiplier.MclCover) (μ : M₁ ≃* M₂)
    (hinv₁ : ∀ b : B₁, b ∉ M₁ → ∀ z : M₁, z ∈ center M₁ → b * (z : B₁) * b⁻¹ = (z : B₁)⁻¹)
    (hinv₂ : ∀ b : B₂, b ∉ M₂ → ∀ z : M₂, z ∈ center M₂ → b * (z : B₂) * b⁻¹ = (z : B₂)⁻¹) :
    ∃ ν : B₁ ≃* B₂, ∀ m : M₁, ν m = μ m := by
  have := finite_of_mulEquiv_mclCover φ₂
  exact exists_mulEquiv_extend_of_index_two hM₁ hM₂ μ (card_center_of_mulEquiv_mclCover φ₂)
    (card_mulAut_le_of_mulEquiv_mclCover φ₂) hinv₁ hinv₂

theorem exists_mulEquiv_of_mclCover_center {B₁ B₂ : Type} [Group B₁] [Group B₂]
    {M₁ : Subgroup B₁} {M₂ : Subgroup B₂} (hM₁ : M₁.index = 2) (hM₂ : M₂.index = 2)
    (φ₂ : M₂ ≃* McLMultiplier.MclCover) (μ : M₁ ≃* M₂)
    (hinv₁ : ∀ b : B₁, b ∉ M₁ → ∀ z : M₁, z ∈ center M₁ → b * (z : B₁) * b⁻¹ = (z : B₁)⁻¹)
    (hinv₂ : ∀ b : B₂, b ∉ M₂ → ∀ z : M₂, z ∈ center M₂ → b * (z : B₂) * b⁻¹ = (z : B₂)⁻¹)
    {z₁ : M₁} {z₂ : M₂} (hz₁ : z₁ ∈ center M₁) (hz₂ : z₂ ∈ center M₂) (h₁ : z₁ ≠ 1)
    (h₂ : z₂ ≠ 1) :
    ∃ ν : B₁ ≃* B₂, ν (z₁ : B₁) = (z₂ : B₂) ∧ ∃ α : MulAut M₂, ∀ m : M₁, ν m = α (μ m) := by
  have := finite_of_mulEquiv_mclCover φ₂
  exact exists_mulEquiv_of_index_two_center hM₁ hM₂ μ (card_center_of_mulEquiv_mclCover φ₂)
    (card_mulAut_le_of_mulEquiv_mclCover φ₂) hinv₁ hinv₂ hz₁ hz₂ h₁ h₂

end CoverBound

end CFSG.Sporadic.Recognition.LyonsSims
