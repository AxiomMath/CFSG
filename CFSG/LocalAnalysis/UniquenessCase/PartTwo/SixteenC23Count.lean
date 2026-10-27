module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem c23_relIndex_le_of_card {p : ℕ} (hp : p.Prime) {Q P K : Subgroup H} (hPQ : P ≤ Q)
    (hKQ : K ≤ Q) (hP : IsPGroup p P) (hPK : P ≤ normalizer (K : Set H)) {a b : ℕ}
    (hK : p ^ a ∣ Nat.card K) (hQ : ¬ p ^ (b + 1) ∣ Nat.card Q) :
    K.relIndex P ≤ p ^ (b - a) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hiso : K.relIndex P = K.relIndex (P ⊔ K) := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hPK
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hPK
    show Nat.card (↥P ⧸ K.subgroupOf P) = Nat.card (↥(P ⊔ K) ⧸ K.subgroupOf (P ⊔ K))
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient P K hPK).toEquiv
  have hinf : K ⊓ (P ⊔ K) = K := inf_of_le_left le_sup_right
  have hcardN : Nat.card ↥(P ⊔ K) = K.relIndex (P ⊔ K) * Nat.card ↥K := by
    rw [← Subgroup.relIndex_mul_card K (P ⊔ K), hinf]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  have hdvdP : K.relIndex P ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card K P
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvdP
  have hpaj : p ^ (a + j) ∣ Nat.card ↥(P ⊔ K) := by
    have h1 : p ^ a * p ^ j ∣ Nat.card ↥K * p ^ j := Nat.mul_dvd_mul hK dvd_rfl
    rw [pow_add, hcardN, ← hiso, hj]
    rwa [mul_comm (Nat.card ↥K) (p ^ j)] at h1
  have hpajQ : p ^ (a + j) ∣ Nat.card ↥Q :=
    hpaj.trans (Subgroup.card_dvd_of_le (sup_le hPQ hKQ))
  have hab : a + j ≤ b := by
    by_contra h
    exact hQ ((Nat.pow_dvd_pow p (Nat.succ_le_of_lt (not_le.1 h))).trans hpajQ)
  calc K.relIndex P = p ^ j := hj
    _ ≤ p ^ (b - a) := Nat.pow_le_pow_right hp.pos (Nat.le_sub_of_add_le' hab)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
