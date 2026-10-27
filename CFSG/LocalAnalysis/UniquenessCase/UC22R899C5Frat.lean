module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ABGLocalTools Subgroup

theorem uc22r899c5_exists_orderOf_mem_normalizer {Γ Q : Type} [Group Γ] [Finite Γ] [Group Q]
    (hQ : ∀ x y : Q, x * y = y * x) {q p : ℕ} [Fact q.Prime] (hp : p.Prime) (hpq : p ≠ q)
    {H P : Subgroup Γ} (hP : IsSylowOf q P H) (ψ : ↥H →* Q) {a : Γ} (haH : a ∈ H)
    (hap : a ^ p = 1) (ha : ψ ⟨a, haH⟩ ≠ 1) :
    ∃ x ∈ H, x ∈ normalizer (P : Set Γ) ∧ orderOf x = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, rfl⟩ := hP
  set N : Subgroup ↥H := ((S : Subgroup ↥H).map ψ).comap ψ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, hQ (ψ g) (ψ n), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      mul_one]
    exact hn
  have hSN : (S : Subgroup ↥H) ≤ N := fun s hs => Subgroup.mem_comap.2 ⟨s, hs, rfl⟩
  have htop := Sylow.normalizer_sup_eq_top' (N := N) S hSN
  have haS := htop.symm ▸ Subgroup.mem_top (⟨a, haH⟩ : ↥H)
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at haS
  obtain ⟨n, hn, k, hk, hnk⟩ := haS
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := q)).1 S.isPGroup'
  set m := Nat.card ↥(S : Subgroup ↥H) with hm
  have hk1 : ψ k ^ m = 1 := by
    obtain ⟨s, hs, hsk⟩ := Subgroup.mem_comap.1 hk
    have hs1 : s ^ m = 1 := by
      have : (⟨s, hs⟩ : ↥(S : Subgroup ↥H)) ^ Nat.card ↥(S : Subgroup ↥H) = 1 :=
        pow_card_eq_one'
      exact congrArg Subtype.val this
    rw [← hsk, ← map_pow, hs1, map_one]
  have hpa : ψ ⟨a, haH⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨a, haH⟩ : ↥H) ^ p = 1 := Subtype.ext (by simpa using hap)
    rw [this, map_one]
  have hoa : orderOf (ψ ⟨a, haH⟩) = p := orderOf_eq_prime hpa ha
  have hpm : ¬ p ∣ m := by
    intro h
    rw [hj] at h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : q.Prime)).1 (hp.dvd_of_dvd_pow h))
  have ham : ψ ⟨a, haH⟩ ^ m ≠ 1 := fun h => hpm (hoa ▸ orderOf_dvd_of_pow_eq_one h)
  have hnm : ψ n ^ m = ψ ⟨a, haH⟩ ^ m := by
    rw [← hnk, map_mul, Commute.mul_pow (hQ (ψ n) (ψ k)), hk1, mul_one]
  have hon : orderOf (ψ n ^ m) = p := by
    refine orderOf_eq_prime ?_ (hnm ▸ ham)
    rw [hnm, ← pow_mul, mul_comm, pow_mul, hpa, one_pow]
  have hpd : p ∣ orderOf n :=
    hon ▸ (orderOf_pow_dvd m).trans (orderOf_map_dvd ψ n)
  refine ⟨((n ^ (orderOf n / p) : ↥H) : Γ), (n ^ (orderOf n / p)).2, ?_, ?_⟩
  · have hx : n ^ (orderOf n / p) ∈ normalizer ((S : Subgroup ↥H) : Set ↥H) :=
      Subgroup.pow_mem _ hn _
    exact Subgroup.le_normalizer_map H.subtype ⟨_, hx, rfl⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (orderOf_pos n).ne' hpd

end CFSG.LocalAnalysis.UniquenessCase.UC22
