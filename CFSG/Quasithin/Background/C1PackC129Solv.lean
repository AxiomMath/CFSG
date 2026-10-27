module

public import CFSG.Quasithin.Background.C1PackC129Set
public import CFSG.Quasithin.Background.C1GNC129
public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Background.C118NoOuter
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace C1Pack

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem natCard_pCore_quotient_eq_three_of_isShort2 {L : Subgroup G} (hL : IsShort2 L)
    (hsolv : Group.IsSolvable ↥L) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
  rcases hL.2.2.2.1 with hq | h3
  · exfalso
    have := hsolv
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq inferInstance
  · exact h3

omit [Finite G] in
theorem false_of_surjective_of_involution {L : Subgroup G} {K : Type*} [Group K] (α : ↥L →* K)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) {g : K} (hg1 : g ≠ 1) (hgg : g * g = 1) : False := by
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hK : Nat.card K = 3 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  have hdvd : orderOf g ∣ Nat.card K := orderOf_dvd_natCard g
  rw [hord, hK] at hdvd
  omega

omit [Finite G] in
theorem isAltType_three_of_isChiBlock_of_isSolvable {X L : Subgroup G} (hL : IsChiBlock X L)
    (hX : Group.IsSolvable ↥X) : IsAltType L 3 := by
  have hLX : L ≤ X := hL.1.2.1
  have : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLX)
      (Subgroup.inclusion_injective hLX)
  have hcard := natCard_pCore_quotient_eq_three_of_isShort2 hL.1.1 inferInstance
  rcases hL.2 with ⟨n, hn, F, hFf, hFfin, hcardF, α, hα, hker, -⟩ | ⟨m, hm, hm3, halt⟩
  · exfalso
    let _ := hFf
    let _ := hFfin
    have hchar : (2 : F) = 0 := by
      have h2 : ringChar F = 2 := by
        refine FiniteField.even_card_iff_char_two.mpr ?_
        rw [hcardF]
        exact Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have : CharP F 2 := ringChar.eq_iff.mp h2
      simpa using CharP.cast_eq_zero F 2
    let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hg1 : g ≠ 1 := by
      intro h
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simp [g] at this
    have hgg : g * g = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul]
      fin_cases i <;> fin_cases j <;> simp [g, Matrix.mul_apply, Fin.sum_univ_two]
      rw [one_add_one_eq_two]
      exact hchar
    exact false_of_surjective_of_involution α hα hker hcard hg1 hgg
  · by_cases hm3' : m = 3
    · subst hm3'
      exact halt
    · exfalso
      have hm4 : 4 ≤ m := by omega
      obtain ⟨α, hα, hker, -⟩ := halt
      have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin m) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hα)
      have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have h1 : Nat.card (alternatingGroup (Fin m)) = 3 := by
        rw [← Nat.card_congr e.toEquiv]
        exact hcard
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h1
      have h2 : Nat.factorial 4 ≤ Nat.factorial m := Nat.factorial_le hm4
      have h3 : Nat.factorial 4 = 24 := by decide
      omega

theorem inf_le_pCoreOf_of_a3Block {L M : Subgroup G} (hLs : IsShort2 L) (hL3 : IsAltType L 3)
    (hWM : pCoreOf 2 L ≤ M) (hLM : ¬ L ≤ M) : L ⊓ M ≤ pCoreOf 2 L := by
  obtain ⟨c, hA4⟩ := S14110.A4Data.of_isShort2 hLs hL3
  have hW : pCoreOf 2 L = blockU L := pCoreOf_eq_blockU_of_a4 hA4
  rintro x ⟨hxL, hxM⟩
  obtain ⟨w, hw, k, rfl⟩ := hA4.mem_decomp hxL
  have hwM : w ∈ M := hWM (hW ▸ hw)
  have hckM : c ^ k ∈ M := by
    have := M.mul_mem (M.inv_mem hwM) hxM
    simpa using this
  by_cases h3 : (3 : ℤ) ∣ k
  · obtain ⟨j, rfl⟩ := h3
    have hc3 : c ^ (3 * j) = 1 := by
      rw [zpow_mul]
      have : c ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact hA4.c_pow_three
      rw [this, one_zpow]
    rw [hc3, mul_one, hW]
    exact hw
  · exfalso
    apply hLM
    have hcM : c ∈ M := by
      have hmod : c ^ (k % 3) = c ^ k := by
        have := zpow_mod_orderOf c k
        rw [hA4.order_c] at this
        simpa using this
      have hcases : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hcases with h1 | h2
      · rw [h1, zpow_one] at hmod
        rw [hmod]
        exact hckM
      · rw [h2] at hmod
        have hc2 : c ^ (2 : ℤ) ∈ M := by rw [hmod]; exact hckM
        have hc2' : c ^ 2 ∈ M := by simpa using hc2
        have : c = c ^ 2 * c ^ 2 := by
          calc c = c ^ 3 * c := by rw [hA4.c_pow_three, one_mul]
            _ = c ^ 2 * c ^ 2 := by group
        rw [this]
        exact M.mul_mem hc2' hc2'
    rw [hA4.eq_sup]
    exact sup_le (hW ▸ hWM) (Subgroup.zpowers_le.mpr hcM)

theorem asc129_of_isSolvable {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {H T M : Subgroup G} (hsq : IsSQTKIn H) (hX : CharTwo H) (hT : IsSylowTwoOf T H)
    (hcgs : cgsIn H T ≤ M) (hMH : M ≤ H) (hsolv : Group.IsSolvable ↥H) :
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G), r ≤ 2 ∧
      (∀ i, IsChi0Block H (Lb i) ∧ IsBorelOfBlock (Lb i) (Lb i ⊓ M) ∧
        ⁅Lb i, thompsonJ T⁆ = Lb i) ∧
      ∀ h ∈ H, ∃ m ∈ M, ∃ x : Fin r → G, (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod := by
  by_cases hT0 : T = ⊥
  ·
    have hO : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
    rw [hT0, le_bot_iff] at hO
    refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, fun h hh => ?_⟩
    have hmem : h ∈ H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      refine ⟨hh, ?_⟩
      rw [hO]
      exact Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [show g = 1 from by simpa using hg]
        simp
    have h2 := hX hmem
    rw [hO] at h2
    have h1 : h = 1 := by simpa using h2
    exact ⟨1, M.one_mem, Fin.elim0, fun i => i.elim0, by simp [h1]⟩
  · have hSQ : IsSQTKTC H := C1GN.isSQTKTC_iff_sqtkGroup.mpr hsq
    have hperf : perfectCore H ≤ Subgroup.centralizer (VZ T H : Set G) := by
      rw [(isSolvable_iff_perfectCore_eq_bot H).mp hsolv]
      exact bot_le
    have hM : (H ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (H ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M :=
      (C1GN.le_cgsIn_of_isGNChoice hC hT.2.1 hT0).trans hcgs
    have hTM : T ≤ M := fun t ht =>
      hcgs (inf_normalizer_le_cgsIn hT0 ⟨hT.1 ht, Subgroup.le_normalizer ht⟩)
    obtain ⟨r, L, hr2, hL, hprod⟩ := lemma_C128_solv_set hC hX hSQ hT hT0 hperf hM hMH
    refine ⟨r, L, hr2, fun i => ?_, hprod⟩
    obtain ⟨hchi, hJ, hLM⟩ := hL i
    have hA3 : IsAltType (L i) 3 := isAltType_three_of_isChiBlock_of_isSolvable hchi hsolv
    have hsub : IsSubnormal (L i) H := IsBlock2.isSubnormal hchi.1
    have hWM : pCoreOf 2 (L i) ≤ M :=
      (A4.pCoreOf_le_of_subnormal 2 hsub).trans ((B6.pCoreOf_two_le_of_isSylowTwoOf hT).trans hTM)
    have hcard := C2Six.natCard_pCore_quotient_of_isAltType_three hA3
    refine ⟨⟨hchi.1, Or.inr (Or.inl hA3)⟩, ?_, hJ⟩
    simp only [IsBorelOfBlock, hcard, ↓reduceIte]
    exact inf_le_pCoreOf_of_a3Block hchi.1.1 hA3 hWM hLM

end C1Pack

theorem asc129StatementSolv (G : Type) [Group G] [Finite G] :
    ∀ (H T M : Subgroup G), IsSQTKIn H → CharTwo H → IsSylowTwoOf T H → cgsIn H T ≤ M → M ≤ H →
      Group.IsSolvable ↥H →
      ∃ (r : ℕ) (Lb : Fin r → Subgroup G), r ≤ 2 ∧
        (∀ i, IsChi0Block H (Lb i) ∧ IsBorelOfBlock (Lb i) (Lb i ⊓ M) ∧
          ⁅Lb i, thompsonJ T⁆ = Lb i) ∧
        ∀ h ∈ H, ∃ m ∈ M, ∃ x : Fin r → G, (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod := by
  intro H T M hsq hX hT hcgs hMH hsolv
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) theoremC118
  exact C1Pack.asc129_of_isSolvable hC hsq hX hT hcgs hMH hsolv

end CFSG.Quasithin
