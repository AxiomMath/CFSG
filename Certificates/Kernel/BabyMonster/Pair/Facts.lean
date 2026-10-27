module

public import Certificates.Kernel.BabyMonster.Pair.Steps
public import Certificates.Kernel.BabyMonster.Pair.QBindA
public import Certificates.Kernel.BabyMonster.Pair.QBindB
public import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Monster.B.Dyadic.PairK
public import Certificates.Kernel.BabyMonster.Pair.WChain

public section

namespace CertificateChecks.KernelBM.Pair

open CFSG.KC.BM CFSG.Monster.B.Dyadic CertificateChecks.KernelBM.Fix

theorem qmat0 :
    Qmat 0 = stripMat NativePair.Q0 := (qmat_rows 0 quot0).trans rowsQ0

theorem qmat25 :
    Qmat 25 = stripMat NativePair.Q25 := (qmat_rows 25 quot25).trans rowsQ25

theorem qmat_Qs (g : Fin 26) : Qmat g = stripMat (Qs.getD g []) := by
  fin_cases g
  · exact qmat0
  · exact qmat1
  · exact qmat2
  · exact qmat3
  · exact qmat4
  · exact qmat5
  · exact qmat6
  · exact qmat7
  · exact qmat8
  · exact qmat9
  · exact qmat10
  · exact qmat11
  · exact qmat12
  · exact qmat13
  · exact qmat14
  · exact qmat15
  · exact qmat16
  · exact qmat17
  · exact qmat18
  · exact qmat19
  · exact qmat20
  · exact qmat21
  · exact qmat22
  · exact qmat23
  · exact qmat24
  · exact qmat25

theorem conjWord_range : ∀ j ∈ CFSG.Monster.B.Bin.conjWord24, 1 ≤ j ∧ j ≤ 26 := by
  decide +kernel

theorem BWK_eq :
    BWK = stripMat NativePair24.W := by
  have hmap : CFSG.Monster.B.Bin.conjWord24.map (fun j => QnK (j - 1)) = wordL.map stripMat := by
    rw [wordL, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j - 1 < 26 := by
      have := conjWord_range j hj
      omega
    rw [Function.comp_apply, QnK, dite_eq_left hj', qmat_Qs ⟨j - 1, hj'⟩]
  have hwf : ∀ X ∈ wordL.tail, wfMat X = true := by
    intro X hX
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_of_mem_tail hX)
    have := conjWord_range j hj
    exact wf_Qs (j - 1) (by omega)
  rw [BWK, hmap, wordL_eq, List.map_cons, List.prod_cons, ← foldl_mul_eq]
  exact stripMat_wchain wchain hwf NativePair24.wf_Q17

theorem F0K_eq : F0K = stripMat NativePair24.F0 := by
  have h := rowsMat_eq_stripMat (R := NativePair.F0.rows) (S := NativePair24.F0)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_F0 69) NativePair24.wf_F0
  rw [← h]
  ext j t
  rfl

theorem probe_eq :
    probeProdK FK (Qmat 25) = stripMat NativePair24.PR := by
  have hmap : CFSG.Monster.B.Bin.probeWord.map (fun l => if l then FK else Qmat 25) =
      probeL.map stripMat := by
    rw [probeL, List.map_map]
    refine List.map_congr_left fun l _ => ?_
    rw [Function.comp_apply, qmat25, FK]
    cases l
    · rfl
    · rfl
  have hwf : ∀ X ∈ probeL.tail, wfMat X = true := by
    intro X hX
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_tail hX)
    cases l
    · exact NativePair24.wf_Q25
    · exact NativePair24.wf_F
  rw [probeProdK, hmap, probeL_eq, List.map_cons, List.prod_cons, ← foldl_mul_eq]
  exact stripMat_wchain prchain hwf NativePair24.wf_F

theorem f_sq : stripMat NativePair24.F * stripMat NativePair24.F = 1 := by
  have hA : stripMat CFSG.KC.BM.Seeds.A1 * stripMat CFSG.KC.BM.Seeds.A1 = 1 := by
    rw [← genA₁_eq_stripMat]
    exact genA₁_mul_self
  calc stripMat NativePair24.F * stripMat NativePair24.F =
      stripMat NativePair24.F * stripMat NativePair24.F * (stripMat NativePair24.T *
        stripMat NativePair24.Ti) := by rw [tinv, mul_one]
    _ = stripMat NativePair24.F * (stripMat NativePair24.F * stripMat NativePair24.T) *
        stripMat NativePair24.Ti := by simp only [mul_assoc]
    _ = stripMat NativePair24.F * (stripMat NativePair24.T * stripMat CFSG.KC.BM.Seeds.A1) *
        stripMat NativePair24.Ti := by rw [ta]
    _ = stripMat NativePair24.F * stripMat NativePair24.T * stripMat CFSG.KC.BM.Seeds.A1 *
        stripMat NativePair24.Ti := by simp only [mul_assoc]
    _ = stripMat NativePair24.T * stripMat CFSG.KC.BM.Seeds.A1 * stripMat CFSG.KC.BM.Seeds.A1 *
        stripMat NativePair24.Ti := by rw [ta]
    _ = stripMat NativePair24.T * (stripMat CFSG.KC.BM.Seeds.A1 * stripMat CFSG.KC.BM.Seeds.A1) *
        stripMat NativePair24.Ti := by simp only [mul_assoc]
    _ = 1 := by rw [hA, mul_one, tinv]

theorem factPair_of : FactPair := by
  have hAB : FK * Qmat 25 = stripMat NativePair24.AB := by rw [FK, qmat25, cAB]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [BWK_eq, FK, F0K_eq, conjF]
  · rw [F0K_eq, f0sq]
  · rw [F0K_eq]
    exact f0ne
  · rw [F0K_eq]
    exact rankF0
  · rw [FK, TK, genA₁_eq_stripMat, ta]
  · rw [qmat25, TK, genA₂_eq_stripMat, tb]
  · rw [FK, f_sq]
  · rw [qmat25, pow_succ, pow_two, bcube]
  · rw [qmat25]
    exact bne
  · rw [hAB, ab_pow]
  · rw [hAB]
    exact ab_ne 5 (by norm_num) (by norm_num)
  · rw [hAB]
    exact ab_ne 11 (by norm_num) (by norm_num)
  · rw [probe_eq]
    exact pr_ne
  · rw [probe_eq, pr_pow]
  · rw [FK, ← rowsMat_eq_stripMat (R := NativePair24.F.rows) (S := NativePair24.F)
      (by bm_blocks CFSG.KC.BM.NativePair24.rows_F 69) NativePair24.wf_F]
    ext j t
    rfl
  · rw [TK, ← rowsMat_eq_stripMat (R := NativePair24.T.rows) (S := NativePair24.T)
      (by bm_blocks CFSG.KC.BM.NativePair24.rows_T 69) NativePair24.wf_T]
    ext j t
    rfl

end CertificateChecks.KernelBM.Pair

end
