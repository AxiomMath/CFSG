module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

private theorem w183_commutator_mul_center {G : Type} [Group G] {z z' a b : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) :
    ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have hz1 : ⁅z, b * z'⁆ = 1 :=
    Commute.commutator_eq ((Subgroup.mem_center_iff.mp hz (b * z')).symm)
  have hz2 : ⁅a, z'⁆ = 1 :=
    Commute.commutator_eq (Subgroup.mem_center_iff.mp hz' a)
  rw [commutatorElement_mul_left_eq_conj_mul, hz1,
    commutatorElement_mul_right_eq_mul_conj, hz2]
  group

private theorem w183_center_specialLinear_four_eq_bot {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 4) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at hr
    exact zero_ne_one hr
  have hr3 : r ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [hK] at h
  have hr1 : r = 1 := by
    have h : r ^ 4 = r := by
      calc r ^ 4 = r ^ 3 * r := by ring
        _ = 1 * r := by rw [hr3]
        _ = r := one_mul r
    rw [hr] at h
    exact h.symm
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

theorem exists_mulEquiv_specialLinear_four_of_lieModel
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 4 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2), Fintype.card K = 4 ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 4) K ≃* ↥L) := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun a b h => MulEquiv.ext (congr_fun h))
  have hsc : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 4 2 2 :=
    hlie.statedClassicalModel_of_ne_zero (by omega)
  simp only [StatedClassicalModel] at hsc
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hsc
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hKcard]
    norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hKcard])
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ :=
    w183_center_specialLinear_four_eq_bot hK4
  have hScalSub : (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) = ⊥ := by
    rw [← map_center_eq_statedScalars 4 K, hcenter, Subgroup.map_bot]
  have ebot : StatedProj (StatedSL 4 K) ≃* ↥(StatedSL 4 K) :=
    (QuotientGroup.quotientMulEquivOfEq hScalSub).trans QuotientGroup.quotientBot
  let φ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(StatedSL 4 K) := e.trans ebot
  let π : ↥L →* ↥(StatedSL 4 K) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨q, rfl⟩ := φ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
    exact ⟨x, rfl⟩
  have hker : π.ker = Subgroup.center ↥L := by
    change (φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))).ker = _
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
      φ.toMonoidHom φ.injective, QuotientGroup.ker_mk']
  have hcen : π.ker ≤ Subgroup.center ↥L := le_of_eq hker
  have hodd : Odd (Nat.card π.ker) := hker ▸ w135_odd_card_center hctx
  obtain ⟨s, hs, -⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated (n := 4)
      (by omega) hπ hcen hodd
  have hcomm : ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ s.range := by
    rw [Subgroup.commutator_le]
    intro l₁ _ l₂ _
    have hz₁ : (s (π l₁))⁻¹ * l₁ ∈ Subgroup.center ↥L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs]
      simp
    have hz₂ : (s (π l₂))⁻¹ * l₂ ∈ Subgroup.center ↥L := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs]
      simp
    have h1 : l₁ = s (π l₁) * ((s (π l₁))⁻¹ * l₁) := by group
    have h2 : l₂ = s (π l₂) * ((s (π l₂))⁻¹ * l₂) := by group
    rw [h1, h2, w183_commutator_mul_center hz₁ hz₂]
    exact MonoidHom.mem_range.mpr ⟨⁅π l₁, π l₂⁆, map_commutatorElement s (π l₁) (π l₂)⟩
  have hsurj : Function.Surjective s := by
    refine MonoidHom.range_eq_top.mp (le_antisymm le_top ?_)
    rw [← hctx.2.2.2.2.1.1.commutator_eq_top]
    exact hcomm
  let s' : Matrix.SpecialLinearGroup (Fin 4) K →* ↥L :=
    s.comp (specialLinearGroupEquivStatedSL 4 K).toMonoidHom
  have hinj : Function.Injective s' := by
    intro a b hab
    have h1 : π (s' a) = (specialLinearGroupEquivStatedSL 4 K) a := by
      simp only [s', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs]
    have h2 : π (s' b) = (specialLinearGroupEquivStatedSL 4 K) b := by
      simp only [s', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs]
    exact (specialLinearGroupEquivStatedSL 4 K).injective
      (by rw [← h1, ← h2, hab])
  have hsurj' : Function.Surjective s' :=
    hsurj.comp (specialLinearGroupEquivStatedSL 4 K).surjective
  exact ⟨K, hKfield, Fintype.ofFinite K, inferInstance, hK4,
    ⟨MulEquiv.ofBijective s' ⟨hinj, hsurj'⟩⟩⟩

theorem center_specialLinear_eq_bot_of_card_four {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 4) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ :=
  w183_center_specialLinear_four_eq_bot hK

end CFSG.LocalAnalysis.WeakClosure81
