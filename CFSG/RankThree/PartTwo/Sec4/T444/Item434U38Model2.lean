module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model1

public section

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model
open scoped LinearAlgebra.Projectivization Matrix

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

section Gens


theorem vec3_ne_zero_of_coord {w : Fin 3 → GF64} (h : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0) :
    w ≠ 0 := by
  rintro rfl
  rcases h with h | h | h <;> exact h rfl

theorem vec3_exists_smul_normV3 {w : Fin 3 → GF64} (hw : w ≠ 0) :
    ∃ r : GF64, r • w = normV3 (w 0) (w 1) (w 2) := by
  have hne : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2.1, hcon.2.2])
  unfold normV3
  split_ifs with h1 h2
  · refine ⟨(w 0)⁻¹, funext fun i => ?_⟩
    fin_cases i <;> simp [inv_mul_cancel₀ h1]
  · have h0 : w 0 = 0 := not_not.mp h1
    refine ⟨(w 1)⁻¹, funext fun i => ?_⟩
    fin_cases i <;> simp [inv_mul_cancel₀ h2, h0]
  · have h0 : w 0 = 0 := not_not.mp h1
    have h1' : w 1 = 0 := not_not.mp h2
    have h2' : w 2 ≠ 0 := by
      rcases hne with h | h | h
      · exact absurd h0 h
      · exact absurd h1' h
      · exact h
    refine ⟨(w 2)⁻¹, funext fun i => ?_⟩
    fin_cases i <;> simp [inv_mul_cancel₀ h2', h0, h1']

theorem vec3_mk_eq_mk_normV3 {w u : Fin 3 → GF64} (hw : w ≠ 0) (hu : u ≠ 0)
    (h : normV3 (w 0) (w 1) (w 2) = u) :
    Projectivization.mk GF64 w hw = Projectivization.mk GF64 u hu := by
  obtain ⟨r, hr⟩ := vec3_exists_smul_normV3 hw
  exact ((Projectivization.mk_eq_mk_iff' GF64 u w hu hw).2 ⟨r, hr.trans h⟩).symm

noncomputable def rootCoord64 (k : Fin 6) : Coord J64 :=
  ⟨(rootA k, rootB k), by
    show rootB k + J64.conj (rootB k) + rootA k * J64.conj (rootA k) = 0
    simp only [J64_conj]
    exact Certificates.certificate188002.roots k⟩

noncomputable def genElt (k : Fin 7) : ProjectiveSpecialUnitaryMatrixGroup J64 :=
  if h : k.val < 6 then root J64 J64_form (rootCoord64 ⟨k.val, h⟩) else weyl J64 J64_form

theorem genElt_matrix (k : Fin 7) :
    ∃ M : GL (Fin 3) GF64, (genElt k : Matrix.ProjGenLinGroup (Fin 3) GF64) =
      Matrix.ProjGenLinGroup.mk M ∧ (M : Matrix (Fin 3) (Fin 3) GF64) = genMat k := by
  unfold genElt
  by_cases h : k.val < 6
  · refine ⟨hermitianUnipotentGL J64 (rootCoord64 ⟨k.val, h⟩), ?_, ?_⟩
    · rw [dif_pos h]
      exact CFSG.UnitaryThreeRecognition.Model.coe_root J64 J64_form _
    · rw [hermitianUnipotentGL_val, genMat, dif_pos h]
      funext i j
      fin_cases i <;> fin_cases j <;>
        simp [hermitianUnipotentMatrix, rootMat, rootCoord64, J64_conj] <;> rfl
  · refine ⟨hermitianWeylGL, ?_, ?_⟩
    · rw [dif_neg h]
      exact CFSG.UnitaryThreeRecognition.Model.coe_weyl J64 J64_form
    · have hz : ((hermitianWeylGL (K := GF64) : GL (Fin 3) GF64) : Matrix (Fin 3) (Fin 3) GF64) =
          hermitianWeylMatrix (K := GF64) := rfl
      rw [hz, genMat, dif_neg h]
      funext i j
      fin_cases i <;> fin_cases j <;> simp [hermitianWeylMatrix, weylMat] <;> rfl

theorem genElt_smul_symm (k : Fin 7) (j : Fin 513) :
    ptsE (genElt k • ptsE.symm j) = CFSG.Monster.B.Co2.permOfArr 513 gensO[k.val]! j := by
  obtain ⟨M, hg, hMg⟩ := genElt_matrix k
  have hvalid : CFSG.RankThree.Native.validA 513 gensO[k.val]! = true :=
    CFSG.Monster.B.Co2.allLt_spec (i := k.val) Certificates.certificate188002.chain.2.1 (by have := k.isLt; omega)
  have hval : ((CFSG.Monster.B.Co2.permOfArr 513 gensO[k.val]! j : Fin 513) : ℕ) =
      (gensO[k.val]!)[j.val]! :=
    (CFSG.RankThree.Native.rep_of_validA hvalid j).symm
  obtain ⟨hnz, t', ht'val, ht'pt⟩ := Certificates.certificate188002.gens.2 k j
  have htt : t' = CFSG.Monster.B.Co2.permOfArr 513 gensO[k.val]! j :=
    Fin.ext (ht'val.trans hval.symm)
  obtain ⟨hvj, hq⟩ := ptsE_symm_coe j
  obtain ⟨hvt, hpt⟩ := ptsE_symm_coe (CFSG.Monster.B.Co2.permOfArr 513 gensO[k.val]! j)
  have hMv : (M : Matrix (Fin 3) (Fin 3) GF64) *ᵥ ptsV j = mulVec3 (genMat k) (ptsV j) := by
    rw [hMg]
    funext i
    simp [mulVec3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hw : (M : Matrix (Fin 3) (Fin 3) GF64) *ᵥ ptsV j ≠ 0 := by
    rw [hMv]
    exact vec3_ne_zero_of_coord hnz
  have hn : normV3 (((M : Matrix (Fin 3) (Fin 3) GF64) *ᵥ ptsV j) 0)
      (((M : Matrix (Fin 3) (Fin 3) GF64) *ᵥ ptsV j) 1)
      (((M : Matrix (Fin 3) (Fin 3) GF64) *ᵥ ptsV j) 2) =
      ptsV (CFSG.Monster.B.Co2.permOfArr 513 gensO[k.val]! j) := by
    rw [hMv, ← htt]
    exact ht'pt
  have hsmul : genElt k • ptsE.symm j =
      ptsE.symm (CFSG.Monster.B.Co2.permOfArr 513 gensO[k.val]! j) := by
    apply Subtype.ext
    rw [CFSG.UnitaryThreeRecognition.Model.coe_smul_of_eq_mk J64 hg hq, hpt]
    exact vec3_mk_eq_mk_normV3 hw hvt hn
  rw [hsmul, Equiv.apply_symm_apply]

theorem genElt_smul (k : Fin 7) (p : IsoPoint J64) :
    ptsE (genElt k • p) = CFSG.Monster.B.Co2.permOfArr 513 gensO[k.val]! (ptsE p) := by
  have key := genElt_smul_symm k (ptsE p)
  rwa [Equiv.symm_apply_apply] at key

end Gens

end CFSG.RankThree.PartTwo.Sec4.Item434U38
