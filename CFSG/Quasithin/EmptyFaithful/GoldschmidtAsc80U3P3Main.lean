module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3P3Fix
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3P3Sev
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3P3Two
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Solv

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.A312U3 CFSG.GH74.GLS.IVK.Proofs2

theorem prime_dvd_card_su3_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3 ^ 2)
    {r : ℕ} (hr : r.Prime) (h : r ∣ Nat.card (SU3F 3 F)) : r = 2 ∨ r = 3 ∨ r = 7 := by
  have := Fact.mk (Nat.prime_three)
  rw [card_su3F hF, show 3 ^ 3 * ((3 ^ 2 - 1) * (3 ^ 3 + 1)) = 2 ^ 5 * 3 ^ 3 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hr).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
        (hr.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h))

theorem no_solvable_irreducible_u3_three {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ 2) {Y : Subgroup (SU3F p F)} (hB : leviU hF ≤ Y)
    (hirr : IsIrrIn (StatedSU 3 (p ^ 1) F) Y) : ¬ Group.IsSolvable ↥Y := by
  subst hp3
  intro hsolv
  have hYne : Y ≠ ⊥ := fun h => by
    have hy : Lemma41aU3.blkU (uniData hF) (gEs hF) ∈ Y := hB ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at hy
    have := congrArg (fun g => matU g 0 1) hy
    simp [matU_gEs hF, matU_one] at this
  obtain ⟨r, N, hr, hrd, hNY, hNne, hcomm, hexp, hnorm⟩ := exists_primary_normal hsolv hYne
  rcases prime_dvd_card_su3_three hF hr hrd with rfl | rfl | rfl
  · exact false_of_normal_two_u3 hF hB hirr hNY hnorm hcomm hexp hNne
  · refine false_of_normal_three_group_u3 hF hirr (U := N) (fun g => ⟨1, ?_⟩) hnorm hNne
    exact Subtype.ext (by simpa using hexp g.1 g.2)
  · exact false_of_normal_seven_u3 hF hB hnorm hexp hNne

end CFSG.Quasithin.E2P.Asc80
