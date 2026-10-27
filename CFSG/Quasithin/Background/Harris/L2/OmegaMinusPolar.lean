module

public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusCoord

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

@[expose] def omegaBil (b : K) (v w : QIdx → K) : K :=
  v (.inl 0) * w (.inr (.inl 0)) + w (.inl 0) * v (.inr (.inl 0)) +
    b * (v (.inr (.inr 0)) * w (.inr (.inr 1)) + w (.inr (.inr 0)) * v (.inr (.inr 1)))

theorem omegaBil_comm (b : K) (v w : QIdx → K) : omegaBil b v w = omegaBil b w v := by
  simp only [omegaBil]
  ring

theorem omegaBil_add_right (b : K) (v w w' : QIdx → K) :
    omegaBil b v (w + w') = omegaBil b v w + omegaBil b v w' := by
  simp only [omegaBil, Pi.add_apply]
  ring

theorem omegaBil_add_left (b : K) (v v' w : QIdx → K) :
    omegaBil b (v + v') w = omegaBil b v w + omegaBil b v' w := by
  simp only [omegaBil, Pi.add_apply]
  ring

theorem omegaBil_zero_left (b : K) (w : QIdx → K) : omegaBil b 0 w = 0 := by
  simp [omegaBil]

theorem omegaBil_smul_right (b : K) (v w : QIdx → K) (k : K) :
    omegaBil b v (k • w) = k * omegaBil b v w := by
  simp only [omegaBil, Pi.smul_apply, smul_eq_mul]
  ring

theorem statedQuadMinus_add (h2 : (2 : K) = 0) (b c : K) (v w : QIdx → K) :
    StatedQuadMinus 2 K b c (v + w) =
      StatedQuadMinus 2 K b c v + StatedQuadMinus 2 K b c w + omegaBil b v w := by
  simp only [statedQuadMinus_two, omegaBil, Pi.add_apply]
  linear_combination (v (.inr (.inr 0)) * w (.inr (.inr 0)) +
    c * (v (.inr (.inr 1)) * w (.inr (.inr 1)))) * h2

theorem omegaBil_mulVec (h2 : (2 : K) = 0) (b c : K) (A : Matrix QIdx QIdx K)
    (hA : ∀ v, StatedQuadMinus 2 K b c (A *ᵥ v) = StatedQuadMinus 2 K b c v) (v w : QIdx → K) :
    omegaBil b (A *ᵥ v) (A *ᵥ w) = omegaBil b v w := by
  have h1 := statedQuadMinus_add h2 b c (A *ᵥ v) (A *ᵥ w)
  have h2' := statedQuadMinus_add h2 b c v w
  rw [← Matrix.mulVec_add, hA, hA, hA] at h1
  linear_combination h2' - h1 + 0 * h2

theorem ne_zero_of_nonsplit [Finite K] (h2 : (2 : K) = 0) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (F := K) (ringChar.eq K 2) c
  apply hbc s
  rw [hb, zero_mul, add_zero, hs]
  linear_combination s ^ 2 * h2

theorem eq_zero_of_omegaBil_eq_zero {b : K} (hb : b ≠ 0) {v : QIdx → K}
    (h : ∀ w, omegaBil b v w = 0) : v = 0 := by
  have h1 := h (Pi.single (.inr (.inl 0)) 1)
  have h2 := h (Pi.single (.inl 0) 1)
  have h3 := h (Pi.single (.inr (.inr 0)) 1)
  have h4 := h (Pi.single (.inr (.inr 1)) 1)
  simp [omegaBil] at h1 h2 h3 h4
  funext i
  rcases i with i | i | i
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h1
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h2
  · fin_cases i
    · exact (h4.resolve_left hb)
    · exact (h3.resolve_left hb)

end CFSG.Quasithin.G11.Harris.L2
