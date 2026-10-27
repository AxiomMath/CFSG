module

public import CFSG.RankThree.PartOne.S15K.BlockModel
public import CFSG.RankThree.PartOne.KC.SymplecticTorusSetting
public import CFSG.RankThree.PartOne.S15K.PSylowSub

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

section Paired

variable {r : ℕ} {K : Type} [Field K]

theorem nonempty_mulEquiv_specialBlock_paired {ℓ f p : ℕ} {x : StatedSp r K}
    {h : primaryFactors (spEnd x)} (hP : SpPairedBlock ℓ f p x h) :
    Nonempty (Matrix.SpecialLinearGroup (Fin (primaryMultiplicity (spEnd x) (h : K[X])))
      (AdjoinRoot (h : K[X])) ≃* ↥(specialBlock (spForm r K) (spLin r K x) (h : K[X]))) := by
  obtain ⟨φ₀, hφ₀, -⟩ := hP.factor
  let φ := (spOrbitEquiv x rfl).trans φ₀
  have hφ : ∀ (g : orbitFactor (spForm r K) (spLin r K x) (h : K[X])) (v : Fin r ⊕ Fin r → K)
      (hv : v ∈ primaryComponent (spEnd x) (h : K[X])),
      blockApply (φ g) v hv =
        ((g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
          Module.End K (Fin r ⊕ Fin r → K)) v := fun g v hv => by
    rw [MulEquiv.trans_apply, hφ₀, spEnd_orbitEquiv]
  have hspec := specialBlock_eq_kerImage (B := spForm r K) (x := spLin r K x) (a := h) φ
    (MonoidHom.id _) hφ
  rw [MonoidHom.comp_id] at hspec
  obtain ⟨e₁⟩ := nonempty_specialLinearGroup_mulEquiv_ker_det
    (E := AdjoinRoot (h : K[X])) (W := primaryComponent (spEnd x) (h : K[X]))
  obtain ⟨e₂⟩ := nonempty_kerImage_mulEquiv (orbitFactor (spForm r K) (spLin r K x) (h : K[X])) φ
    (blockGLDet (spEnd x) (h : K[X]))
  have e₃ : ↥(kerImage (orbitFactor (spForm r K) (spLin r K x) (h : K[X])) φ
      (blockGLDet (spEnd x) (h : K[X]))) ≃*
      ↥(specialBlock (spForm r K) (spLin r K x) (h : K[X])) :=
    MulEquiv.subgroupCongr hspec.symm
  exact ⟨(e₁.trans e₂.symm).trans e₃⟩

theorem blockModel_specialBlock_paired {f p : ℕ} [Finite K] [CharP K 2] {x : StatedSp r K}
    (hf : 2 ≤ f) {h : primaryFactors (spEnd x)} (hP : SpPairedBlock 2 f p x h)
    (hm2 : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]))
    (hm3 : primaryMultiplicity (spEnd x) (h : K[X]) ≤ 3) :
    BlockModel p ↥(specialBlock (spForm r K) (spLin r K x) (h : K[X])) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_specialBlock_paired hP
  have hdeg : 1 ≤ (h : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
  have hE : Nat.card (AdjoinRoot (h : K[X])) = 2 ^ (f * (h : K[X]).natDegree) := by
    rw [hP.card_field, pow_mul]
  have hfin : Finite (AdjoinRoot (h : K[X])) :=
    Nat.finite_of_card_ne_zero (by rw [hE]; positivity)
  have hg : 2 ≤ f * (h : K[X]).natDegree := le_trans hf (Nat.le_mul_of_pos_right f hdeg)
  have hpg : p ∣ 2 ^ (f * (h : K[X]).natDegree) - 1 := by
    have := hP.dvd
    rwa [← pow_mul] at this
  have hchar : CharP (AdjoinRoot (h : K[X])) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (h : K[X]))).injective 2
  exact ⟨f * (h : K[X]).natDegree, AdjoinRoot (h : K[X]), inferInstance, hfin, hchar, hE, hg, hpg,
    Or.inl ⟨primaryMultiplicity (spEnd x) (h : K[X]), by omega, ⟨e.symm⟩⟩⟩

end Paired

section Fixed

variable {r : ℕ} {K : Type} [Field K]

theorem blockModel_specialBlock_fixed {f p : ℕ} [Finite K] [CharP K 2] {x : StatedSp r K}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks 2 f p x (proj r K x))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x))
    (hm2 : 2 ≤ primaryMultiplicity (spEnd x) (X - 1))
    (hlt : Module.finrank K (primaryComponent (spEnd x) (X - 1)) < 6) :
    BlockModel p ↥(specialBlock (spForm r K) (spLin r K x) (X - 1)) := by
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hfr : primaryMultiplicity (spEnd x) (X - 1) =
      Module.finrank K (primaryComponent (spEnd x) (X - 1)) := by
    have : Fact (Irreducible (X - 1 : K[X])) := ⟨by simpa using irreducible_X_sub_C (1 : K)⟩
    have h1 := finrank_primaryComponent (spEnd x) (X - 1 : K[X])
    have h2 : (X - 1 : K[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : K)
    rw [h2, one_mul] at h1
    exact h1.symm
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hO : ({(X - 1 : K[X]), reciprocalPolynomial (X - 1 : K[X])} : Set K[X]) = {X - 1} := by
    rw [KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
  let Φ := (spOrbitEquiv x hO).trans φ
  have hBalt : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun z => spForm_isAlt z.1
  have hnd := blocks.fixed_nondegenerate
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hBalt hnd
  have hs12 : s = 1 ∨ s = 2 := by omega
  have hqs : CFSG.IsQuasisimple ↥(orbitFactor (spForm r K) (spLin r K x) (X - 1)) := by
    have := isQuasisimple_sesqUnitaryGroup_of_alt hBalt hnd (by omega) (Or.inl hq4)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Φ.symm this
  have hfacts := spBlockFacts_of_spFixed hsq blocks hmem (Or.inl hq4)
  have hcomm := hfacts.commutator_eq hm2
  have hperf : ⁅orbitFactor (spForm r K) (spLin r K x) (X - 1),
      orbitFactor (spForm r K) (spLin r K x) (X - 1)⁆ =
        orbitFactor (spForm r K) (spLin r K x) (X - 1) :=
    (Subgroup.isPerfect_iff).1 hqs.1
  have hspec : specialBlock (spForm r K) (spLin r K x) (X - 1) =
      orbitFactor (spForm r K) (spLin r K x) (X - 1) := by
    simpa [hperf] using hcomm.symm
  let e' : ↥(specialBlock (spForm r K) (spLin r K x) (X - 1)) ≃* StatedSp s K :=
    ((MulEquiv.subgroupCongr hspec).trans Φ).trans e
  rcases hs12 with rfl | rfl
  · exact ⟨f, K, inferInstance, inferInstance, inferInstance, hK, hf, hpq,
      Or.inl ⟨2, Or.inl rfl, ⟨e'.trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm⟩⟩⟩
  · exact ⟨f, K, inferInstance, inferInstance, inferInstance, hK, hf, hpq, Or.inr (Or.inl ⟨e'⟩)⟩

end Fixed


section Assembly

variable {K : Type} [Field K]

theorem spEnd_eq_one_iff {x : StatedSp 3 K} : spEnd x = 1 ↔ x = 1 :=
  ⟨fun h => spLin_injective (Units.ext (by simpa [spEnd] using h)), fun h => by subst h; simp [spEnd]⟩

theorem blockModel_spBlockGSp {f p : ℕ} [Finite K] [CharP K 2] (hp5 : 5 ≤ p) {x : StatedSp 3 K}
    (hK : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hx1 : x ≠ 1)
    (hsq : Squarefree (minpoly K (spEnd x))) (blocks : SpPrimaryBlocks 2 f p x (proj 3 K x))
    (a : SpBlockIdx x) : BlockModel p ↥(spBlockGSp x (a.1 : K[X])) := by
  have hf : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  obtain ⟨⟨h, hmem⟩, hm2⟩ := a
  have e₀ : ↥(spBlockGSp x h) ≃* ↥(specialBlock (spForm 3 K) (spLin 3 K x) h) :=
    ((spBlockGSp x h).equivMapOfInjective (gspLin 3 K) gspLin_injective).trans
      (MulEquiv.subgroupCongr (map_spBlockGSp h))
  refine BlockModel.of_mulEquiv e₀.symm ?_
  have hV : Module.finrank K (Fin 3 ⊕ Fin 3 → K) = 6 := by simp
  by_cases h1 : h = X - 1
  · subst h1
    have hlt : Module.finrank K (primaryComponent (spEnd x) (X - 1)) < 6 := by
      by_contra hge
      have hle := Submodule.finrank_le (primaryComponent (spEnd x) (X - 1))
      have heq : Module.finrank K (primaryComponent (spEnd x) (X - 1)) =
          Module.finrank K (Fin 3 ⊕ Fin 3 → K) := by omega
      have htop := Submodule.eq_top_of_finrank_eq heq
      rw [blocks.fixed_eq, LinearMap.ker_eq_top, sub_eq_zero] at htop
      exact hx1 (spEnd_eq_one_iff.mp htop)
    exact blockModel_specialBlock_fixed hK hf hpq hsq blocks hmem hm2 hlt
  · have h2 : ¬ reciprocalPolynomial h = h := by
      intro h2
      obtain ⟨d, -, hpd, -⟩ := (blocks.selfDual ⟨h, hmem⟩ h1 h2).exists_half
      exact false_of_dvd_pow_add_one hp5 (by positivity) hpq hpd
    have hP := blocks.paired ⟨h, hmem⟩ (Ne.symm h2)
    have hdeg : 1 ≤ h.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors hmem)
    have hh' : reciprocalPolynomial h ∈ primaryFactors (spEnd x) :=
      blocks.bijOn.mapsTo (Finset.mem_coe.mpr hmem)
    have hbound : 2 * (h.natDegree * primaryMultiplicity (spEnd x) h) ≤ 6 := by
      classical
      have hsum := finrank_eq_sum_degree_mul_multiplicity hsq
      rw [hV] at hsum
      set F : primaryFactors (spEnd x) → ℕ :=
        fun b => (b : K[X]).natDegree * primaryMultiplicity (spEnd x) (b : K[X]) with hF
      have hne : (⟨h, hmem⟩ : primaryFactors (spEnd x)) ≠ ⟨reciprocalPolynomial h, hh'⟩ := fun hc =>
        h2 (congrArg Subtype.val hc).symm
      have h3 : F ⟨h, hmem⟩ + F ⟨reciprocalPolynomial h, hh'⟩ ≤ ∑ b, F b := by
        rw [← Finset.sum_pair hne]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      have h4 : F ⟨reciprocalPolynomial h, hh'⟩ = F ⟨h, hmem⟩ := by
        simp only [hF]
        rw [← hP.natDegree_eq, ← hP.multiplicity_eq]
      have h5 : F ⟨h, hmem⟩ = h.natDegree * primaryMultiplicity (spEnd x) h := rfl
      have h6 : (6 : ℕ) = ∑ b, F b := hsum
      omega
    have hm2' : 2 ≤ primaryMultiplicity (spEnd x) h := hm2
    have hm1 : primaryMultiplicity (spEnd x) h ≤ h.natDegree * primaryMultiplicity (spEnd x) h :=
      Nat.le_mul_of_pos_left _ hdeg
    exact blockModel_specialBlock_paired (h := ⟨h, hmem⟩) hf hP hm2'
      (show primaryMultiplicity (spEnd x) h ≤ 3 by omega)

end Assembly

end CFSG.RankThree.PartOne.S15K
