module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenNF

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

def pi6 : Fin 6 → Fin 6 := ![0, 1, 3, 4, 2, 5]

def pinv6 : Fin 6 → Fin 6 := ![0, 1, 4, 2, 3, 5]

def permM : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun r c => if r = pi6 c then 1 else 0

def pg : G6 := ⟨permM, permMᵀ, by decide, by decide⟩

theorem permM_conj_apply' (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (a b : Fin 6) :
    (permM * M * permMᵀ) a b = M (pinv6 a) (pinv6 b) := by
  fin_cases a <;> fin_cases b <;>
    simp (config := {decide := true}) [Matrix.mul_apply, Fin.sum_univ_six, permM, pi6, pinv6]

theorem pg_conj_u0R : pg * Sp4Cen.u0 * pg⁻¹ = u0 := by
  apply Units.ext
  show permM * Sp4Cen.U0 * permMᵀ = u0M
  decide

theorem exists_conj_u0 {u : G6} (h3 : orderOf u = 3)
    (h16 : 16 ≤ Nat.card {v : Fin 6 → ZMod 2 //
      (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v}) :
    ∃ g : G6, g * u * g⁻¹ = u0 := by
  obtain ⟨Q, hQ⟩ := Sp4Cen.exists_conj_u0 h3 h16
  refine ⟨pg * Q, ?_⟩
  calc pg * Q * u * (pg * Q)⁻¹ = pg * (Q * u * Q⁻¹) * pg⁻¹ := by group
    _ = u0 := by rw [hQ, pg_conj_u0R]

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
