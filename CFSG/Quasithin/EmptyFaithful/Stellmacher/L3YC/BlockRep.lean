module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

section BlockRep

variable {F : Type} [Field F]

theorem exists_block_rep (h01 : ∀ c : F, c = 0 ∨ c = 1) {k : ℕ}
    (S : Set (Matrix (Fin 3) (Fin 3) F))
    (hS : ∀ X : Matrix (Fin 3) (Fin 3) F, (∀ A ∈ S, A * X = X * A) → X = 0 ∨ X = 1)
    (Φ : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F))
    (hΦ : ∀ A ∈ S, ∀ w : Fin k → Fin 3 → F,
      Φ (fun i => A.mulVec (w i)) = fun i => A.mulVec (Φ w i)) :
    ∃ B : Matrix (Fin k) (Fin k) F,
      ∀ (w : Fin k → Fin 3 → F) (i : Fin k), Φ w i = ∑ j, B i j • w j := by
  classical
  have hsmul : ∀ (c : F) (w : Fin k → Fin 3 → F), Φ (c • w) = c • Φ w := by
    intro c w
    rcases h01 c with rfl | rfl <;> simp
  let P : Fin k → Fin k → Matrix (Fin 3) (Fin 3) F := fun i j =>
    Matrix.of fun m' m => Φ (Pi.single j (Pi.single m 1)) i m'
  have hvec : ∀ (i j : Fin k) (u : Fin 3 → F), Φ (Pi.single j u) i = (P i j).mulVec u := by
    intro i j u
    have hu : (Pi.single j u : Fin k → Fin 3 → F) =
        ∑ m, u m • (Pi.single j (Pi.single m 1) : Fin k → Fin 3 → F) := by
      ext j' m'
      by_cases hj : j' = j
      · subst hj
        simp [Finset.sum_apply, Pi.single_apply]
      · simp [Finset.sum_apply, hj]
    rw [hu, map_sum]
    ext m'
    simp [hsmul, Matrix.mulVec, dotProduct, P, Finset.sum_apply, mul_comm]
  have hcomm : ∀ i j, ∀ A ∈ S, A * P i j = P i j * A := by
    intro i j A hA
    rw [Matrix.ext_iff_mulVec]
    intro u
    have h1 := hΦ A hA (Pi.single j u)
    have h2 : (fun i' => A.mulVec ((Pi.single j u : Fin k → Fin 3 → F) i')) =
        Pi.single j (A.mulVec u) := by
      ext i' m'
      by_cases hi : i' = j
      · subst hi
        simp
      · simp [hi]
    rw [h2] at h1
    have h3 := congrFun h1 i
    rw [hvec, hvec] at h3
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h3.symm
  have hPB : ∀ i j, ∃ b : F, ∀ u : Fin 3 → F, (P i j).mulVec u = b • u := by
    intro i j
    rcases hS (P i j) (fun A hA => hcomm i j A hA) with h | h
    · exact ⟨0, fun u => by simp [h]⟩
    · exact ⟨1, fun u => by simp [h]⟩
  choose B hB using hPB
  refine ⟨Matrix.of B, fun w i => ?_⟩
  have hw : w = ∑ j, (Pi.single j (w j) : Fin k → Fin 3 → F) := (Finset.univ_sum_single w).symm
  conv_lhs => rw [hw]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hvec, hB]
  rfl

end BlockRep

end Stellmacher.L3YC

end CFSG.Quasithin
