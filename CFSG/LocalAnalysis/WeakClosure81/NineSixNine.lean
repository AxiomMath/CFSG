module

public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem six_nine_two_core_mem {M V H S A : Subgroup G}
    (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hMnorm : normalizer (V : Set G) = M)
    (hS : IsSylowIn 2 S H) {i k n : ℕ} (hn : n = k + i)
    (hA : A ∈ E3.gammaSet V i S) (hAV : A ≤ V) (hAne : ¬ A ≤ pCoreOf 2 H)
    (hK : E1.IsE k H S A H) (hkV : n < rk ↥V)
    (hr : (n : ℕ∞) < E3.rParam V)
    (hne : ⁅twoResidual H, E3.cClos V n S⁆ ≠ ⊥)
    (hbeta : (n : ℕ∞) < betaN i M V) :
    ∃ g ∈ H, InCalO2 n M ⊥ V g :=
  six_nine_two_core hV hM hMnorm hS hn hA hAV hAne hK hkV hr hne hbeta

theorem lt_rParam_of_isTI {V : Subgroup G} (hTI : IsTI V) {n : ℕ} (hn : n < rk ↥V) :
    (n : ℕ∞) < E3.rParam V := by
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ E3.rParam V := by
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hcent⟩ := hU
    have hUbot : U = ⊥ := by
      rw [← le_bot_iff]
      intro u huU
      by_contra hu1
      exact hcent (le_trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU))
        (centralizer_le_normalizer_of_isTI hTI (hUV huU)
          (by simpa [Subgroup.mem_bot] using hu1)))
    rw [hUbot, mQuot_bot]
    exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt hn)
  exact lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n)) hle

theorem betaN_eq_top_of_isTI {V : Subgroup G} (hTI : IsTI V) (n : ℕ) :
    betaN n (normalizer (V : Set G)) V = ⊤ := by
  have hcal : calBn n (normalizer (V : Set G)) V = ∅ := by
    ext U
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hU
    simp only [calBn, propN, Set.mem_setOf_eq] at hU
    obtain ⟨-, t, ht, -, W, hWV, -, -, hWt, hPropB⟩ := hU
    rw [SetLike.le_def] at hWt
    push Not at hWt
    obtain ⟨w, hwW, hwC⟩ := hWt
    have htw : ¬ t * w = w * t := by
      intro h
      exact hwC (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact h)
    have hx1 : w⁻¹ * t⁻¹ * w * t ≠ 1 := by
      intro hx
      apply htw
      have h1 : t⁻¹ * w * t = w := by
        have := congrArg (fun z => w * z) hx
        simpa [mul_assoc] using this
      have h2 : w * t = t * w := by
        have := congrArg (fun z => t * z) h1
        simpa [mul_assoc] using this
      exact h2.symm
    have hcommV : commElt W t ≤ V := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨w', hw', rfl⟩
      have h2 : t⁻¹ * w' * t ∈ V := (Subgroup.mem_normalizer_iff''.1 ht.1 w').1 (hWV hw')
      have h3 : w'⁻¹ * (t⁻¹ * w' * t) ∈ (V : Set G) := V.mul_mem (V.inv_mem (hWV hw')) h2
      simpa only [mul_assoc] using h3
    have hxmem : w⁻¹ * t⁻¹ * w * t ∈ commElt W t :=
      Subgroup.subset_closure ⟨w, hwW, rfl⟩
    have hxV : w⁻¹ * t⁻¹ * w * t ∈ V := by simpa using hcommV hxmem
    have hCle : centralizer (commElt W t : Set G) ≤ normalizer (V : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxmem)).trans
        (centralizer_le_normalizer_of_isTI hTI hxV hx1)
    exact hPropB hCle
  rw [betaN, hcal]
  exact iInf_eq_top.mpr fun U => iInf_eq_top.mpr fun hU => (Set.notMem_empty U hU).elim

theorem exists_mem_conj_of_isE {V A H S : Subgroup G} (hV : Hyp7 V) (hm : 2 < rk ↥V)
    (hA : IsGConj V A) (hS : IsSylowIn 2 S H) (hAS : A ≤ S) (hAH : ¬ A ≤ pCoreOf 2 H)
    (hK : E1.IsE 1 H S A H) (hne : ⁅twoResidual H, E3.cClos V 1 S⁆ ≠ ⊥) :
    ∃ y ∈ H,
      InCalO 1 (normalizer (A : Set G)) ⊥ A y ∧ ¬ IsPGroup 2 ↥(A ⊔ conjSubgroup A y) := by
  obtain ⟨g, rfl⟩ := hA
  have hAb : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup' hV.1 g
  have hTI : IsTI (conjSubgroup V g) := isTI_conj hV.2.2 g
  have hkV : 1 < rk ↥(conjSubgroup V g) := by
    rw [E3.rk_conjSubgroup]
    omega
  have hr : (1 : ℕ∞) < E3.rParam (conjSubgroup V g) := lt_rParam_of_isTI hTI hkV
  have hne' : ⁅twoResidual H, E3.cClos (conjSubgroup V g) 1 S⁆ ≠ ⊥ := by
    rwa [E3.cClos_conjV]
  have hbeta : (1 : ℕ∞) < betaN 0 (normalizer (conjSubgroup V g : Set G))
      (conjSubgroup V g) := by
    rw [betaN_eq_top_of_isTI hTI 0]
    exact ENat.natCast_lt_top 1
  have hA0 : conjSubgroup V g ∈ E3.gammaSet (conjSubgroup V g) 0 S := by
    refine ⟨hAS, 1, ?_, ?_⟩
    · rw [CFSG.Quasithin.conjSubgroup_one]
    · rw [CFSG.Quasithin.conjSubgroup_one]
      exact E3.mQuot_self (conjSubgroup V g)
  obtain ⟨y, hyH, hInCalO, -, -, hnon2⟩ :=
    six_nine_two_core_mem (M := normalizer (conjSubgroup V g : Set G)) hAb le_rfl rfl hS
      (by norm_num) hA0 le_rfl hAH hK hkV hr hne' hbeta
  exact ⟨y, hyH, hInCalO, hnon2⟩

end CFSG.LocalAnalysis.WeakClosure81
