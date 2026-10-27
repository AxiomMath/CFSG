module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K] [CharP K 2]

theorem radA1_le_centralizer_rootU₂ : radA1 K ≤ rootC₂ K := by
  rintro _ ⟨b, c, d, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨e, rfl⟩
  rw [uElt_mul, uElt_mul]
  congr 1 <;> ring

theorem rootU₂_le_radA1 : rootU₂ K ≤ radA1 K := by
  rintro _ ⟨c, rfl⟩
  exact ⟨0, c, 0, rfl⟩

theorem sElt_mem_rootC₂ (M : SL₂ K) : sElt M ∈ rootC₂ K :=
  sHom₂_range_le_centralizer_rootU₂ ⟨M, rfl⟩

theorem eq_radA2_of_normal (hK : 2 < Nat.card K) {V : Subgroup (antiSp K)} (hVC : V ≤ rootC₂ K)
    (hVn : (V.subgroupOf (rootC₂ K)).Normal) (hVA : V ≤ radA2 K) (hVU : ¬ V ≤ rootU₂ K) :
    V = radA2 K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hconjC : ∀ g ∈ rootC₂ K, ∀ z ∈ V, g * z * g⁻¹ ∈ V := by
    intro g hg z hz
    have := hVn.conj_mem ⟨z, hVC hz⟩ (Subgroup.mem_subgroupOf.mpr hz) ⟨g, hg⟩
    simpa using Subgroup.mem_subgroupOf.mp this
  obtain ⟨z₀, hz₀V, hz₀U⟩ : ∃ z ∈ V, z ∉ rootU₂ K := by
    by_contra h
    push Not at h
    exact hVU h
  have hz₀A := hVA hz₀V
  have hv₀ : vecOf₂ z₀ ≠ 0 := fun h => hz₀U ((vecOf₂_eq_zero_iff hz₀A).mp h)
  have himage : ∀ w : Fin 2 → K, ∃ z ∈ V, vecOf₂ z = w := by
    intro w
    by_cases hw : w = 0
    · refine ⟨1, one_mem _, ?_⟩
      rw [hw, ← aElt_zero_zero, vecOf₂_aElt]
    · obtain ⟨M, hM⟩ := exists_sl2_mulVec_eq hv₀ hw
      exact ⟨sElt M * z₀ * (sElt M)⁻¹, hconjC _ (sElt_mem_rootC₂ M) _ hz₀V, by
        rw [vecOf₂_conj M hz₀A, hM]⟩
  have hAV : ∀ x ∈ radA2 K, ∃ z ∈ V, ∃ u ∈ rootU₂ K, x = z * u := by
    intro x hx
    obtain ⟨z, hzV, hzx⟩ := himage (vecOf₂ x)
    have hzA := hVA hzV
    refine ⟨z, hzV, z⁻¹ * x, ?_, by group⟩
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (mul_self_of_mem_radA2 hzA)
    rw [← vecOf₂_eq_zero_iff (mul_mem (inv_mem hzA) hx), vecOf₂_mul (inv_mem hzA) hx, hzi, hzx]
    ext i
    simp [CharTwo.add_self_eq_zero]
  have hsq : ∀ u ∈ antiUnipotent K, u * u ∈ V := by
    intro u hu
    obtain ⟨a, b, c, d, rfl⟩ := hu
    have hxy : uElt a b c d = uElt a (b + a * d) c 0 * uElt 0 0 0 d := by
      rw [uElt_mul]
      congr 1 <;> first | ring1 | linear_combination (-(a * d)) * h2
    obtain ⟨z, hzV, u₂, hu₂, hx⟩ := hAV (uElt a (b + a * d) c 0) ⟨a, b + a * d, c, rfl⟩
    have hy : uElt 0 0 0 d ∈ radA1 K := ⟨0, 0, d, rfl⟩
    set y := u₂ * uElt 0 0 0 d with hydef
    have hyA1 : y ∈ radA1 K := mul_mem (rootU₂_le_radA1 hu₂) hy
    have hu' : uElt a b c d = z * y := by rw [hxy, hx, mul_assoc]
    have hyy : y * y = 1 := mul_self_of_mem_radA1 hyA1
    have hzy : y * z * y⁻¹ ∈ V := hconjC _ (radA1_le_centralizer_rootU₂ hyA1) _ hzV
    rw [hu']
    have : z * y * (z * y) = z * (y * z * y⁻¹) * (y * y) := by group
    rw [this, hyy, mul_one]
    exact mul_mem hzV hzy
  have hZV : antiUnipotentCenter K ≤ V := by
    rw [← closure_squares_eq hK]
    exact (Subgroup.closure_le _).mpr fun g ⟨h, hh, hg⟩ => hg ▸ hsq h hh
  have hUV : rootU₂ K ≤ V := fun u ⟨c, hc⟩ => hZV (hc ▸ ⟨0, c, rfl⟩)
  refine le_antisymm hVA fun x hx => ?_
  obtain ⟨z, hzV, u, hu, rfl⟩ := hAV x hx
  exact mul_mem hzV (hUV hu)

variable (K) in
@[expose] def quotS₂ : SL₂ K →* (rootC₂ K) ⧸ (radA2 K).subgroupOf (rootC₂ K) :=
  (QuotientGroup.mk' _).comp ((sHom₂ K).codRestrict (rootC₂ K) sElt_mem_rootC₂)

theorem quotS₂_apply (M : SL₂ K) :
    quotS₂ K M = QuotientGroup.mk ⟨sElt M, sElt_mem_rootC₂ M⟩ :=
  rfl

theorem quotS₂_bijective : Function.Bijective (quotS₂ K) := by
  constructor
  · intro M N h
    rw [quotS₂_apply, quotS₂_apply, QuotientGroup.eq] at h
    have h1 := Subgroup.mem_subgroupOf.mp h
    have h2 : (sElt M)⁻¹ * sElt N = sElt (M⁻¹ * N) := by
      rw [← sHom₂_apply, ← sHom₂_apply, ← sHom₂_apply, map_mul, map_inv]
    have h3 : (sElt M)⁻¹ * sElt N ∈ radA2 K ⊓ (sHom₂ K).range := by
      refine ⟨by simpa using h1, ⟨M⁻¹ * N, ?_⟩⟩
      rw [sHom₂_apply, h2]
    rw [radA2_inf_sHom₂_range, Subgroup.mem_bot, h2] at h3
    have := sHom₂_injective (K := K) (h3.trans (map_one (sHom₂ K)).symm)
    exact (inv_mul_eq_one.mp this)
  · intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, c, M, hg⟩ := exists_aElt_mul_sElt g.2
    refine ⟨M, ?_⟩
    rw [quotS₂_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : ((((⟨sElt M, sElt_mem_rootC₂ M⟩ : rootC₂ K))⁻¹ * g : rootC₂ K) : antiSp K) =
        (sElt M)⁻¹ * (aElt v c * sElt M) := by
      simp [hg]
    rw [h1]
    have := conj_mem_radA2 (firstCol_sElt M).inv (aElt_mem_radA2 v c)
    simpa [mul_assoc] using this

@[expose] noncomputable def quotS₂Equiv (K : Type) [Field K] [CharP K 2] :
    SL₂ K ≃* (rootC₂ K) ⧸ (radA2 K).subgroupOf (rootC₂ K) :=
  MulEquiv.ofBijective (quotS₂ K) quotS₂_bijective

theorem isPerfect_rootC₂ (hK : 4 ≤ Nat.card K) : Group.IsPerfect (rootC₂ K) := by
  refine ⟨?_⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨v, c, M, hg⟩ := exists_aElt_mul_sElt g.2
  have hS : ∀ N : SL₂ K, (⟨sElt N, sElt_mem_rootC₂ N⟩ : rootC₂ K) ∈ commutator (rootC₂ K) := by
    intro N
    have h1 : N ∈ commutator (SL₂ K) := by
      rw [(sl2_isPerfect hK).commutator_eq_top]
      exact Subgroup.mem_top N
    have h2 := Subgroup.mem_map_of_mem ((sHom₂ K).codRestrict (rootC₂ K) sElt_mem_rootC₂) h1
    rw [commutator_def, Subgroup.map_commutator] at h2
    exact Subgroup.commutator_mono le_top le_top h2
  set W : Subgroup (rootC₂ K) :=
    commutator (rootC₂ K) ⊓ (radA2 K).subgroupOf (rootC₂ K) with hW
  set V : Subgroup (antiSp K) := W.map (rootC₂ K).subtype with hV
  have hVC : V ≤ rootC₂ K := Subgroup.map_subtype_le W
  have hVsub : V.subgroupOf (rootC₂ K) = W :=
    Subgroup.comap_map_eq_self_of_injective (rootC₂ K).subtype_injective W
  have hVn : (V.subgroupOf (rootC₂ K)).Normal := by
    rw [hVsub]
    exact ⟨fun n hn g => ⟨(inferInstance : (commutator (rootC₂ K)).Normal).conj_mem n hn.1 g,
      (inferInstance : ((radA2 K).subgroupOf (rootC₂ K)).Normal).conj_mem n hn.2 g⟩⟩
  have hVA : V ≤ radA2 K := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hy.2
  have hVU : ¬ V ≤ rootU₂ K := by
    intro hle
    set v : Fin 2 → K := ![1, 0] with hvdef
    set M₀ : SL₂ K := ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two]; simp⟩ with hM₀
    have hα : aElt v 0 ∈ rootC₂ K := radA2_le_centralizer_rootU₂ (aElt_mem_radA2 v 0)
    have hcomm : (⟨aElt v 0, hα⟩ : rootC₂ K) * ⟨sElt M₀, sElt_mem_rootC₂ M₀⟩ *
        (⟨aElt v 0, hα⟩ : rootC₂ K)⁻¹ * (⟨sElt M₀, sElt_mem_rootC₂ M₀⟩ : rootC₂ K)⁻¹ ∈
        commutator (rootC₂ K) := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hcalc : (((⟨aElt v 0, hα⟩ : rootC₂ K) * ⟨sElt M₀, sElt_mem_rootC₂ M₀⟩ *
        (⟨aElt v 0, hα⟩ : rootC₂ K)⁻¹ * (⟨sElt M₀, sElt_mem_rootC₂ M₀⟩ : rootC₂ K)⁻¹ :
          rootC₂ K) : antiSp K) =
        aElt v 0 * aElt ((M₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 0 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [aElt_inv]
      have := sElt_mul_aElt M₀ v 0
      calc aElt v 0 * sElt M₀ * aElt v 0 * (sElt M₀)⁻¹
          = aElt v 0 * (sElt M₀ * aElt v 0 * (sElt M₀)⁻¹) := by group
        _ = _ := by rw [this, mul_inv_cancel_right]
    have hzA : aElt v 0 * aElt ((M₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 0 ∈ radA2 K :=
      mul_mem (aElt_mem_radA2 _ _) (aElt_mem_radA2 _ _)
    have hz : aElt v 0 * aElt ((M₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 0 ∈ V :=
      ⟨_, ⟨hcomm, Subgroup.mem_subgroupOf.mpr (hcalc ▸ hzA)⟩, hcalc⟩
    have hz' := hle hz
    have hvec := (vecOf₂_eq_zero_iff hzA).mpr hz'
    rw [vecOf₂_mul (aElt_mem_radA2 _ _) (aElt_mem_radA2 _ _), vecOf₂_aElt, vecOf₂_aElt] at hvec
    have := congrFun hvec 1
    simp [hvdef, hM₀] at this
  have hVeq := eq_radA2_of_normal (by omega) hVC hVn hVA hVU
  have hAc : aElt v c ∈ rootC₂ K := radA2_le_centralizer_rootU₂ (aElt_mem_radA2 v c)
  have hA : (⟨aElt v c, hAc⟩ : rootC₂ K) ∈ commutator (rootC₂ K) := by
    have hmem : aElt v c ∈ V := by
      rw [hVeq]
      exact aElt_mem_radA2 v c
    obtain ⟨y, hy, hyv⟩ := hmem
    have hyeq : y = ⟨aElt v c, hAc⟩ := Subtype.ext hyv
    have := hy.1
    rwa [hyeq] at this
  have hgeq : g = ⟨aElt v c, hAc⟩ * ⟨sElt M, sElt_mem_rootC₂ M⟩ := Subtype.ext hg
  rw [hgeq]
  exact mul_mem hA (hS M)

theorem isPGroup_radA2_subgroupOf : IsPGroup 2 ((radA2 K).subgroupOf (rootC₂ K)) := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨v, c, hvc⟩ := mem_radA2_iff.mp (Subgroup.mem_subgroupOf.mp g.2)
  apply Subtype.ext
  apply Subtype.ext
  show (g.1.1) ^ (2 ^ 1) = 1
  rw [pow_one, pow_two, hvc]
  exact aElt_mul_self v c

theorem pCore_rootC₂ [Finite K] (hK : 4 ≤ Nat.card K) :
    CFSG.pCore 2 (rootC₂ K) = (radA2 K).subgroupOf (rootC₂ K) := by
  apply le_antisymm
  · intro x hx
    let φ : rootC₂ K →* SL₂ K :=
      (quotS₂Equiv K).symm.toMonoidHom.comp (QuotientGroup.mk' _)
    have hφ : Function.Surjective φ :=
      (quotS₂Equiv K).symm.surjective.comp (QuotientGroup.mk'_surjective _)
    have hP : (CFSG.pCore 2 (rootC₂ K)).map φ ≤ CFSG.pCore 2 (SL₂ K) :=
      le_sSup ⟨Subgroup.Normal.map CFSG.pCore_normal φ hφ,
        IsPGroup.map CFSG.pCore_isPGroup φ⟩
    rw [sl2_pCore_eq_bot hK] at hP
    have h2 := hP (Subgroup.mem_map_of_mem φ hx)
    rw [Subgroup.mem_bot] at h2
    have h3 : (QuotientGroup.mk x : (rootC₂ K) ⧸ (radA2 K).subgroupOf (rootC₂ K)) = 1 := by
      have := congrArg (quotS₂Equiv K) h2
      simpa [φ] using this
    exact (QuotientGroup.eq_one_iff x).mp h3
  · exact le_sSup ⟨inferInstance, isPGroup_radA2_subgroupOf⟩

end KCRootAxis

end CFSG.RankThree.PartOne
