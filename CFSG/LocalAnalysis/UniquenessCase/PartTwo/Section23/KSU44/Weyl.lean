module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Torus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Quasithin.H13.U4ParCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par KTabD Matrix

private lemma det_hypGram_two_zero_S09 {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K) :
    (hypGram 2 0 K).det = 1 := by
  haveI : CharP K 2 := hK.charP
  have hsq : (hypGram 2 0 K).det * (hypGram 2 0 K).det = 1 := by
    rw [← Matrix.det_mul, hypGram_mul_self, Matrix.det_one]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hdm : (hypGram 2 0 K).det + 1 = (hypGram 2 0 K).det - 1 := by
    have h : (hypGram 2 0 K).det + 1 - ((hypGram 2 0 K).det - 1) = 0 := by
      rw [show (hypGram 2 0 K).det + 1 - ((hypGram 2 0 K).det - 1) = (2 : K) by ring,
        htwo]
    exact sub_eq_zero.mp h
  have hz : ((hypGram 2 0 K).det - 1) * ((hypGram 2 0 K).det + 1) = 0 := by
    have h : ((hypGram 2 0 K).det - 1) * ((hypGram 2 0 K).det + 1) =
        (hypGram 2 0 K).det * (hypGram 2 0 K).det - 1 := by ring
    rw [h, hsq, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · rw [hdm] at h
    exact sub_eq_zero.mp h

private lemma hypGram_mul_diagonal_mul_S09 {K : Type} [Field K]
    (hK : UnitaryFieldData 2 2 K) (x : Fin 2 → rootsOfUnity 3 K) :
    hypGram 2 0 K
        * diagonal (torusEntries hK (fun i => (x i : Kˣ)) (1 : Fin 0 → Kˣ))
        * hypGram 2 0 K
        * diagonal (torusEntries hK (fun i => (x i : Kˣ)) (1 : Fin 0 → Kˣ)) = 1 := by
  have hd : ∀ a : HypIndex 2 0,
      torusEntries hK (fun i => (x i : Kˣ)) (1 : Fin 0 → Kˣ) (hypPartner a)
        * torusEntries hK (fun i => (x i : Kˣ)) (1 : Fin 0 → Kˣ) a = 1 := by
    intro a
    rcases a with i | k | i
    · have hb : hK.bar ((x i : Kˣ) : K) = ((x i : Kˣ) : K) :=
        splitInv_rootsOfUnity_three hK (x i)
      simp only [hypPartner_inl, torusEntries, hb]
      exact inv_mul_cancel₀ (Units.ne_zero (x i : Kˣ))
    · exact k.elim0
    · have hb : hK.bar ((x i : Kˣ) : K) = ((x i : Kˣ) : K) :=
        splitInv_rootsOfUnity_three hK (x i)
      simp only [hypPartner_inr_inr, torusEntries, hb]
      exact mul_inv_cancel₀ (Units.ne_zero (x i : Kˣ))
  ext a b
  rw [mul_diagonal, mul_hypGram_apply, hypGram_mul_apply]
  by_cases hab : a = b
  · subst hab
    rw [diagonal_apply_eq, hd a]
    simp
  · rw [diagonal_apply_ne _ (fun h => hab (hypPartner_injective h)), zero_mul]
    simp [hab]

theorem exists_weyl {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K) :
    ∃ w : hypSU hK 2 0, w ∉ lineStab (hypSU hK 2 0) (Pi.single ie1 1) ∧
      ∀ e ∈ torusE hK, w * e * w⁻¹ = e⁻¹ := by
  classical
  let wGL : GL (HypIndex 2 0) K :=
    ⟨hypGram 2 0 K, hypGram 2 0 K, hypGram_mul_self, hypGram_mul_self⟩
  have hwGL_val : ((wGL : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = hypGram 2 0 K := rfl
  have hwGL_mem : wGL ∈ hypSU hK 2 0 := by
    rw [mem_hypSU]
    refine ⟨?_, ?_⟩
    · rw [hwGL_val, hypGram_map hK.bar, hypGram_transpose, hypGram_mul_self, one_mul]
    · rw [hwGL_val]
      exact det_hypGram_two_zero_S09 hK
  let w : hypSU hK 2 0 := ⟨wGL, hwGL_mem⟩
  have hwmat : ((w : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = hypGram 2 0 K := rfl
  have hwinvmat : (((w⁻¹ : hypSU hK 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) = hypGram 2 0 K := rfl
  refine ⟨w, ?_, ?_⟩
  · intro hw
    rw [mem_lineStab] at hw
    obtain ⟨c, hc⟩ := hw
    have hleft : (((w : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K)
          *ᵥ (Pi.single ie1 1 : HypIndex 2 0 → K)) if1 = 1 := by
      rw [hwmat, hypGram_mulVec]
      simp
    have hright : (c • (Pi.single ie1 1 : HypIndex 2 0 → K)) if1 = 0 := by
      simp
    have h1 := congrFun hc if1
    rw [hleft, hright] at h1
    exact one_ne_zero h1
  · intro e he
    change e ∈ (splitTorusHom hK 2 0 (rootsOfUnity 3 K)
      (splitInv_rootsOfUnity_three hK)).range at he
    obtain ⟨x, rfl⟩ := he
    apply eq_inv_of_mul_eq_one_left
    apply hypSU_ext
    simp only [coe_mul_hypSU, hwmat, hwinvmat, coe_splitTorusHom, Subgroup.coe_one,
      Units.val_one]
    exact hypGram_mul_diagonal_mul_S09 hK x

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
