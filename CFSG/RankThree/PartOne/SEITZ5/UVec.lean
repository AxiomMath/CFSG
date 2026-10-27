module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.SEITZ2.SU3Core

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def vec2 (p q : Fin n) (a b : K) : Fin n → K := Pi.single p a + Pi.single q b

theorem herm_vec2_left (p q : Fin n) (a b : K) (x : Fin n → K) :
    herm σ (vec2 p q a b) x = σ a * x p + σ b * x q := by
  rw [vec2, herm_add_left, herm_single_left, herm_single_left]

theorem vec2_apply_left {p q : Fin n} (hpq : p ≠ q) (a b : K) : vec2 p q a b p = a := by
  simp [vec2, hpq]

theorem vec2_apply_right {p q : Fin n} (hpq : p ≠ q) (a b : K) : vec2 p q a b q = b := by
  simp [vec2, hpq.symm]

theorem vec2_apply_other {p q r : Fin n} (hp : r ≠ p) (hq : r ≠ q) (a b : K) :
    vec2 p q a b r = 0 := by
  simp [vec2, hp, hq]

theorem herm_vec2_vec2_disj {p q p' q' : Fin n} (hpp : p ≠ p') (hpq : p ≠ q') (hqp : q ≠ p')
    (hqq : q ≠ q') (a b c d : K) : herm σ (vec2 p q a b) (vec2 p' q' c d) = 0 := by
  rw [herm_vec2_left, vec2_apply_other hpp hpq, vec2_apply_other hqp hqq]
  simp

theorem herm_vec2_vec2_same {p q : Fin n} (hpq : p ≠ q) (a b c d : K) :
    herm σ (vec2 p q a b) (vec2 p q c d) = σ a * c + σ b * d := by
  rw [herm_vec2_left, vec2_apply_left hpq, vec2_apply_right hpq]

theorem isRat_vec2 {k : Subfield K} (p q : Fin n) {a b : K} (ha : a ∈ k) (hb : b ∈ k) :
    IsRat k (vec2 p q a b) := fun r => by
  rw [vec2, Pi.add_apply]
  refine k.add_mem ?_ ?_
  · by_cases h : r = p
    · subst h
      simpa using ha
    · simp [h, k.zero_mem]
  · by_cases h : r = q
    · subst h
      simpa using hb
    · simp [h, k.zero_mem]

end CFSG.RankThree.PartOne.SEITZ5
