module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal

public section

namespace Subgroup

theorem IsSubnormal.eq_top_of_index_eq_prime_pow {G : Type*} [Group G] [Finite G]
    (hG : Group.IsPerfect G) {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hH : H.IsSubnormal) :
    ∀ k : ℕ, H.index = p ^ k → H = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  induction hH with
  | top => intro _ _; rfl
  | step H M hle hM hN ih =>
    intro k hk
    have hdvd : M.index ∣ p ^ k := hk ▸ Subgroup.index_dvd_of_le hle
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    obtain rfl := ih j hj
    have hHn : H.Normal := ⟨fun a ha g => hN.conj_mem ⟨a, trivial⟩ ha ⟨g, trivial⟩⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Subgroup.index_eq_one.mp (by rw [hk, pow_zero])
    · exfalso
      have hcard : Nat.card (G ⧸ H) = p ^ k := hk
      have hpG : IsPGroup p (G ⧸ H) := IsPGroup.of_card hcard
      have : Nontrivial (G ⧸ H) := by
        apply Finite.one_lt_card_iff_nontrivial.mp
        rw [hcard]
        exact Nat.one_lt_pow hk0.ne' hp.one_lt
      have : Group.IsPerfect G := hG
      exact Group.IsPerfect.not_isNilpotent (G ⧸ H) hpG.isNilpotent

end Subgroup
