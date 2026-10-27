module

public import CFSG.RankThree.GF2n.Stroth80.Sec111Odd

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth_11_1b_ii (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) {h : G}
    (hH : h ∈ H0 M Z) (hL : ∀ x ∈ LB M Q B, ⁅h, x⁆ ∈ Q) (hB : ∀ b ∈ B, ⁅h, b⁆ ∈ Z) :
    ∃ k : ℕ, h ^ 2 ^ k ∈ Q := by
  have hhM : h ∈ M := hH.1
  have hn1 : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨a, s, hs, hrs⟩ := Nat.exists_eq_two_pow_mul_odd hn1
  have hQn : ∀ y ∈ Q, h * y * h⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hhM) y).mp hy
  have hZn : ∀ y ∈ Z, h * y * h⁻¹ ∈ Z := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hhM) y).mp hy
  have hLk : ∀ k : ℕ, ∀ y ∈ LB M Q B, ⁅h ^ k, y⁆ ∈ Q := by
    intro k y hy
    induction k with
    | zero => simp [commutatorElement_def]
    | succ k ih =>
      have e : ⁅h ^ (k + 1), y⁆ = h * ⁅h ^ k, y⁆ * h⁻¹ * ⁅h, y⁆ := by
        rw [pow_succ']
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Q.mul_mem (hQn _ ih) (hL y hy)
  have hBk : ∀ k : ℕ, ∀ u ∈ B, ⁅h ^ k, u⁆ ∈ Z := by
    intro k u hu
    induction k with
    | zero => simp [commutatorElement_def]
    | succ k ih =>
      have e : ⁅h ^ (k + 1), u⁆ = h * ⁅h ^ k, u⁆ * h⁻¹ * ⁅h, u⁆ := by
        rw [pow_succ']
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Z.mul_mem (hZn _ ih) (hB u hu)
  have hord : orderOf (h ^ 2 ^ a) = s := by
    rw [orderOf_pow_of_dvd (by positivity) (hrs ▸ dvd_mul_right _ _), hrs]
    exact Nat.mul_div_cancel_left s (by positivity)
  have hx : h ^ 2 ^ a = 1 :=
    hc.eq_one_of_odd_comm hw (Subgroup.pow_mem _ hH _) (fun y hy => hLk _ y hy)
      (fun u hu => hBk _ u hu) (by rw [hord]; exact hs)
  exact ⟨a, by rw [hx]; exact Q.one_mem⟩

end CFSG.RankThree.GF2n.Stroth80
