module

public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne

open Matrix

variable {n : ℕ} {K : Type} [Field K]

@[expose] def avgProj (p : ℕ) (B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  ∑ i ∈ Finset.range p, B ^ i

theorem mul_avgProj {p : ℕ} {B : Matrix (Fin n) (Fin n) K} (hB : B ^ p = 1) :
    B * avgProj p B = avgProj p B := by
  unfold avgProj
  rw [Finset.mul_sum]
  have h1 : ∑ i ∈ Finset.range p, B * B ^ i = ∑ i ∈ Finset.range p, B ^ (i + 1) :=
    Finset.sum_congr rfl fun i _ => (pow_succ' B i).symm
  rw [h1]
  have h2 := Finset.sum_range_succ (fun i => B ^ i) p
  have h3 := Finset.sum_range_succ' (fun i => B ^ i) p
  rw [hB] at h2
  rw [pow_zero] at h3
  have h4 : ∑ i ∈ Finset.range p, B ^ (i + 1) + 1 = ∑ i ∈ Finset.range p, B ^ i + 1 := by
    rw [← h3, h2]
  exact add_right_cancel h4

theorem pow_mul_avgProj {p : ℕ} {B : Matrix (Fin n) (Fin n) K} (hB : B ^ p = 1) (i : ℕ) :
    B ^ i * avgProj p B = avgProj p B := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, mul_assoc, mul_avgProj hB, ih]

theorem avgProj_mul_self [CharP K 2] {p : ℕ} (hp : Odd p) {B : Matrix (Fin n) (Fin n) K}
    (hB : B ^ p = 1) : avgProj p B * avgProj p B = avgProj p B := by
  have h1 : avgProj p B * avgProj p B = ∑ i ∈ Finset.range p, avgProj p B := by
    conv_lhs => unfold avgProj
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => pow_mul_avgProj hB i
  rw [h1, Finset.sum_const, Finset.card_range]
  obtain ⟨m, rfl⟩ := hp
  have h2 : ((2 * m + 1 : ℕ) : K) = 1 := by
    push_cast
    rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2]
    ring
  rw [← Nat.cast_smul_eq_nsmul K, h2, one_smul]

end CFSG.RankThree.PartOne
