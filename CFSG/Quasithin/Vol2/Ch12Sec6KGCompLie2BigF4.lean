module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigSz
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigL2
public import CFSG.Quasithin.H13.L32ACSkPfF4
public import CFSG.LieType.Ree.LargeReeInvolutionFusion
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersRankOne
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersParabolicOne
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.H13.L32ACSkPfSz
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf CFSG.Blueprint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.ReeTag

theorem exists_inv_of_injective {A B : Type} [Group A] [Group B] (ι : A →* B)
    (hι : Function.Injective ι) {z : A}
    (h : ∃ y : A, Odd (orderOf y) ∧ z * y * z⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1)) :
    ∃ y : B, Odd (orderOf y) ∧ ι z * y * (ι z)⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1) := by
  obtain ⟨y, hy1, hy2, hy3⟩ := h
  refine ⟨ι y, by rwa [orderOf_injective ι hι], ?_, ?_⟩
  · have := congrArg ι hy2
    rwa [map_mul, map_mul, map_inv, map_inv] at this
  · rintro (h3 | h5)
    · exact hy3 (Or.inl (hι (by rw [map_pow, h3, map_one])))
    · exact hy3 (Or.inr (hι (by rw [map_pow, h5, map_one])))

theorem exists_inv_of_conj {G : Type} [Group G] {z w g : G} (hg : g * z * g⁻¹ = w)
    (h : ∃ y : G, Odd (orderOf y) ∧ w * y * w⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1)) :
    ∃ y : G, Odd (orderOf y) ∧ z * y * z⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1) := by
  have e : (MulAut.conj g⁻¹).toMonoidHom w = z := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hg]
    group
  have := exists_inv_of_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective h
  rwa [e] at this


section F4

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

omit [Finite K] in
theorem sylowA_one_eq : sylowA m K 1 = largeReeA1Hom K m (xT 1) := by
  have hx : (xT 1 : SL2 K) = uSL 1 := Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [coe_xT, coe_uSL]
  have h0 : LargeReeCover.nTwo K 0 = 1 := by
    have h : F4.fixedRelElt (⟨0, by decide⟩ : Fin F4.fixedWeylOrder) = 1 := rfl
    rw [LargeReeCover.nTwo, show LargeReeCover.kTwo 0 = ⟨0, by decide⟩ from rfl, h,
      canonicalRep_one]
  rw [hx, largeReeA1Hom_uSL, one_pow, sylowA_eq, twoCoordG, h0, one_mul, inv_one, mul_one,
    stdTwoG_eq_xUnit, largeReeSigma, one_pow]

theorem exists_inv_tOne (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {w : F4.reeGamma K m} (hw : (w : ModGL F4.tag K) = sylowL m K 1) :
    ∃ y : F4.reeGamma K m, Odd (orderOf y) ∧ w * y * w⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hΓ : ∀ g : SL2 K, largeReeA1Hom K m g ∈ F4.reeGamma K m := fun g =>
    rankOneGroupOne_le_reeGamma hK (by rw [rankOneGroupOne_eq_range hK]; exact ⟨g, rfl⟩)
  set n : F4.reeGamma K m := ⟨weylTwo K * weylOne K * weylTwo K,
    mul_mem (mul_mem weylTwo_mem weylOne_mem) weylTwo_mem⟩
  set φ : SL2 K →* F4.reeGamma K m :=
    (MulAut.conj n).toMonoidHom.comp ((largeReeA1Hom K m).codRestrict _ hΓ)
  have hφ : Function.Injective φ := fun g h e => largeReeA1Hom_injective
    (congrArg Subtype.val ((MulAut.conj n).injective e))
  have e : φ (xT 1) = w := by
    apply Subtype.ext
    rw [hw, ← weyl_conj_sylowA_one, sylowA_one_eq]
    rfl
  obtain ⟨y, hy⟩ := exists_inv_of_hom hK (by omega) φ hφ (one_ne_zero (α := K))
  exact ⟨y, by rwa [e] at hy⟩

theorem exists_inv_zOne (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {w : F4.reeGamma K m} (hw : (w : ModGL F4.tag K) = sylowH m K 0 1) :
    ∃ y : F4.reeGamma K m, Odd (orderOf y) ∧ w * y * w⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := rankOneGroupTwo_le_reeGamma hK
  have hSz : SuzukiModel (rankOneGroupTwo K m) 2 (2 * m + 1) :=
    ⟨rfl, m, hm, K, inferInstance, inferInstance, rfl, hK, ⟨rankOneEquivSuzuki K m hm hK⟩⟩
  have : Finite (rankOneGroupTwo K m) :=
    Finite.of_equiv _ (rankOneEquivSuzuki K m hm hK).symm.toEquiv
  set b : rankOneGroupTwo K m := ⟨sylowB m K 0 1,
    Subgroup.subset_closure (Or.inl (Or.inl (sylowB_mem_U2 hK 0 1)))⟩
  have hb2 : b ^ 2 = 1 := by
    have hH : sylowH m K 0 0 = 1 := by simp [sylowH, sylowX, largeReeSigma_zero, pinnedX_zero]
    have := sylowB_mul_sylowH_sq hK (0 : K)
    rw [hH, mul_one] at this
    exact Subtype.ext this
  have hb1 : b ≠ 1 := by
    intro h1
    have h2 : sylowB m K 0 1 = sylowB m K 0 0 := by
      rw [sylowB_zero_zero]
      exact congrArg Subtype.val h1
    exact one_ne_zero (sylowB_injective hK h2).2
  have hpg : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hb2 hb1, pow_one])
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have hS : IsSylowTwoOf (P : Subgroup (rankOneGroupTwo K m)) ⊤ :=
    ⟨le_top, P.isPGroup', by
      rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
      exact P.not_dvd_index⟩
  have hinv := exists_inv_of_suzukiModel (by omega) hSz hS (hP (Subgroup.mem_zpowers b)) hb2 hb1
  set n : F4.reeGamma K m := ⟨weylOne K * weylTwo K * weylOne K,
    mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem⟩
  set ι : rankOneGroupTwo K m →* F4.reeGamma K m :=
    (MulAut.conj n).toMonoidHom.comp (Subgroup.inclusion hR)
  have hι : Function.Injective ι :=
    ((MulAut.conj n).injective).comp (Subgroup.inclusion_injective hR)
  have e : ι b = w := by
    apply Subtype.ext
    rw [hw, ← weyl_conj_sylowB_zero]
    rfl
  have := exists_inv_of_injective ι hι hinv
  rwa [e] at this

theorem false_of_autConf_2f4 {M : Type} [Group M] {f : ℕ} (hM : ReeTitsModel M .twistedF4 2 f)
    {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  obtain ⟨-, -, -, -, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := large_Ree_model_Schreier _ 2 f hM
  obtain ⟨-, a, hfa, hmodel'⟩ := hM
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel'
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  have ha : 1 ≤ a := by omega
  obtain ⟨hNF, hF⟩ := CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK'
  have hZ := large_Ree_fixed_group_center_trivial a K hK'
  have hinn : ∀ α : MulAut (F4.reeGamma K a), (∃ k : ℕ, α ^ 2 ^ k = 1) →
      α ∈ (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range := fun α hα =>
    mem_range_conj_of_pow_two_pow (F4.reeGammaFieldAutHom K a) hNF (fun β hβ => hF β hβ)
      (f := 2 * a + 1) ⟨a, rfl⟩ (ringAut_pow_eq_one hK') hα
  refine not_autConf_of_inner hZ hinn (fun _ _ z _ hz2 hz1 => ?_) (h.map E)
  have hzsq : (z : ModGL F4.tag K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hz2, Subgroup.coe_one]
  have hzne : (z : ModGL F4.tag K) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  rcases involution_conj_zOne_or_tOne ha hK' z.2 hzsq hzne with ⟨x, hx, hxz⟩ | ⟨x, hx, hxz⟩
  · exact exists_inv_of_conj (g := ⟨x, hx⟩) rfl (exists_inv_zOne ha hK' hxz)
  · exact exists_inv_of_conj (g := ⟨x, hx⟩) rfl (exists_inv_tOne ha hK' hxz)

end F4

end CFSG.Quasithin.H13.S126C
