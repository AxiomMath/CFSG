module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL34
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Field

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4.Res6L364 (K64)

theorem exists_cube_one_of_det_one {A : GL (Fin 3) K64}
    (hdet : Matrix.GeneralLinearGroup.det A = 1) (hA : conjAut 3 K64 A ^ 3 = 1) :
    ∃ B : GL (Fin 3) K64, conjAut 3 K64 B = conjAut 3 K64 A ∧ B ^ 3 = 1 := by
  have hk : A ^ 3 ∈ (conjAut 3 K64).ker := by
    rw [MonoidHom.mem_ker, map_pow, hA]
  rw [CFSG.RankThree.PartTwo.Sec4.ker_conjAut_three] at hk
  obtain ⟨c, hc⟩ : ∃ c : K64ˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = A ^ 3 := hk
  have hc3 : c ^ 3 = 1 := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hc
    rw [det_scalar_three, map_pow, hdet, one_pow] at h1
    exact h1
  have hc21 : (c : K64) ^ 21 = 1 := by
    have h3 : (c : K64) ^ 3 = 1 := by
      have := congrArg Units.val hc3
      simpa using this
    calc (c : K64) ^ 21 = ((c : K64) ^ 3) ^ 7 := by ring
      _ = 1 := by rw [h3, one_pow]
  obtain ⟨μ, hμ⟩ := CFSG.RankThree.PartTwo.Sec4.Res6L364.exists_cube_root hc21
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h] at hμ
    exact c.ne_zero (by rw [← hμ]; norm_num)
  set s : K64ˣ := Units.mk0 μ hμ0 with hs
  have hs3 : s ^ 3 = c := Units.ext (by simpa [hs] using hμ)
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * A, ?_, ?_⟩
  · rw [map_mul, conjAut_scalar, one_mul]
  · have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹) A :=
      (Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) s⁻¹ A)
    rw [hcomm.mul_pow, ← hc, ← map_pow, ← map_mul, inv_pow, ← hs3, inv_mul_cancel, map_one]

theorem exists_eigenvector_of_pow_three {A : GL (Fin 3) K64} (hA : A ^ 3 = 1) :
    ∃ u : Fin 3 → K64, u ≠ 0 ∧ ∃ l : K64,
      Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) K64) u = l • u := by
  set M : Matrix (Fin 3) (Fin 3) K64 := (A : Matrix (Fin 3) (Fin 3) K64) with hM
  have hM3 : M ^ 3 = 1 := by
    have := congrArg (fun X : GL (Fin 3) K64 => (X : Matrix (Fin 3) (Fin 3) K64)) hA
    simpa [hM, Units.val_pow_eq_pow_val] using this
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → K64, w ≠ 0 :=
    ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩
  have hω : (CFSG.RankThree.PartTwo.Sec4.Res6L364.ω) ^ 2 +
      CFSG.RankThree.PartTwo.Sec4.Res6L364.ω + 1 = 0 :=
    CFSG.RankThree.PartTwo.Sec4.Res6L364.omega_sq_add
  have hω3 : (CFSG.RankThree.PartTwo.Sec4.Res6L364.ω) ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.Sec4.Res6L364.omega_cube
  generalize CFSG.RankThree.PartTwo.Sec4.Res6L364.ω = ω at hω hω3
  obtain ⟨p1, hp1⟩ : ∃ p1 : Fin 3 → K64, p1 = M.mulVec w := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p2 : Fin 3 → K64, p2 = M.mulVec p1 := ⟨_, rfl⟩
  have hp3 : M.mulVec p2 = w := by
    have : (M ^ 3).mulVec w = w := by rw [hM3, Matrix.one_mulVec]
    rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at this
    rw [hp2, hp1]
    exact this
  obtain ⟨w1, hw1⟩ : ∃ w1 : Fin 3 → K64, w1 = p1 - ω ^ 2 • w := ⟨_, rfl⟩
  obtain ⟨w2, hw2⟩ : ∃ w2 : Fin 3 → K64, w2 = M.mulVec w1 - ω • w1 := ⟨_, rfl⟩
  have e1 : M.mulVec w1 = p2 - ω ^ 2 • p1 := by
    rw [hw1, Matrix.mulVec_sub, Matrix.mulVec_smul, ← hp1, ← hp2]
  have e2 : w2 = p2 - ω ^ 2 • p1 - ω • (p1 - ω ^ 2 • w) := by rw [hw2, e1, hw1]
  have e3 : M.mulVec w2 = (w - ω ^ 2 • p2) - ω • (p2 - ω ^ 2 • p1) := by
    rw [hw2, Matrix.mulVec_sub, Matrix.mulVec_smul, e1, Matrix.mulVec_sub, Matrix.mulVec_smul,
      hp3, ← hp2]
  have hw3 : M.mulVec w2 - w2 = 0 := by
    rw [e3, e2]
    linear_combination (norm := module) hω3 • (p1 - w) + hω • (p1 - p2)
  by_cases h1 : w1 = 0
  · refine ⟨w, hw, ω ^ 2, ?_⟩
    rw [hw1, sub_eq_zero] at h1
    rw [← hp1]
    exact h1
  by_cases h2 : w2 = 0
  · refine ⟨w1, h1, ω, ?_⟩
    rw [hw2, sub_eq_zero] at h2
    exact h2
  · refine ⟨w2, h2, 1, ?_⟩
    rw [one_smul]
    exact sub_eq_zero.mp hw3

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
