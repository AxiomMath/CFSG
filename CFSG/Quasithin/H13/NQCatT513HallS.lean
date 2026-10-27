module

public import CFSG.Quasithin.H13.NQCatT513Hall

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

theorem pPart_of_solvable_overgroups {X : Type} [Group X] [Finite X] {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {E : ℕ → Prop}
    (hidx : ∀ Z : Subgroup X, S₀ ≤ Z → Group.IsSolvable ↥Z → ∀ m : ℕ,
      Nat.card ↥Z = m * Nat.card ↥S₀ → m = 1 ∨ 3 ∣ m ∨ E m)
    {Dc : Subgroup X} (hcyc : IsCyclic ↥Dc) (hodd : Odd (Nat.card ↥Dc))
    (hperm : (Dc : Set X) * (S₀ : Set X) = (S₀ : Set X) * (Dc : Set X)) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hpD : p ∣ Nat.card ↥Dc) : ∃ a : ℕ, E (p ^ (a + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥S₀ := hS₀.2.1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS2
  have hcop : Nat.Coprime (Nat.card ↥Dc) (Nat.card ↥S₀) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
  have hY := card_sup_of_perm hperm hcop
  have hDn : Group.IsNilpotent ↥Dc := by
    have := hcyc
    infer_instance
  have hYs := isSolvable_sup_of_perm hDn hS2.isNilpotent hperm hcop
  obtain ⟨H, hSH, hHY, k, hk, hk2, hkp, hHq⟩ := exists_hall_two_p hS2 le_sup_right hYs hp
  have hHs : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHY)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hSH
  rw [mul_comm] at hm
  have hpos : 0 < Nat.card ↥S₀ := Nat.card_pos
  have hmk : m * k = Nat.card ↥Dc := by
    rw [hm, hY] at hk
    have : (m * k) * Nat.card ↥S₀ = Nat.card ↥Dc * Nat.card ↥S₀ := by rw [← hk]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hmk
    exact absurd hmk.symm Nat.card_pos.ne'
  have hmodd : ¬ 2 ∣ m := fun h2 => (Nat.not_even_iff_odd.mpr hodd)
    (even_iff_two_dvd.mpr (hmk ▸ Dvd.dvd.mul_right h2 k))
  have hmp : m = p ^ m.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hm0 fun {q} hq hqm => ?_
    rcases hHq q hq (hm ▸ Dvd.dvd.mul_right hqm _) with h | h
    · exact absurd (h ▸ hqm) hmodd
    · exact h
  have hpm : p ∣ m := by
    rw [← hmk] at hpD
    rcases hp.dvd_mul.mp hpD with h | h
    · exact h
    · exact absurd h hkp
  have hlen : m.primeFactorsList.length ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hmp
    rw [hmp] at hpm
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpm)
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hlen
  rw [ha] at hmp
  refine ⟨a, ?_⟩
  rcases hidx H hSH hHs m hm with h | h | h
  · rw [h] at hpm
    exact absurd (Nat.dvd_one.mp hpm) hp.one_lt.ne'
  · rw [hmp] at h
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm hp3
  · rwa [← hmp]

theorem cycOddPerm_of_solvable_overgroups {X : Type} [Group X] [Finite X] {S₀ : Subgroup X}
    (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hidx : ∀ Z : Subgroup X, S₀ ≤ Z → Group.IsSolvable ↥Z → ∀ m : ℕ,
      Nat.card ↥Z = m * Nat.card ↥S₀ → m = 1 ∨ 3 ∣ m) :
    CycOddPerm X fun _ => False := by
  refine cycOddPerm_of_sylow hS₀ fun Dc hcyc hodd hperm => Or.inl ?_
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqD => ?_⟩
  by_contra h3
  obtain ⟨a, ha⟩ := pPart_of_solvable_overgroups (E := fun _ => False) hS₀
    (fun Z hZ hZs m hm => (hidx Z hZ hZs m hm).elim Or.inl fun h => Or.inr (Or.inl h)) hcyc hodd
    hperm hq h3 hqD
  exact ha

end CFSG.Quasithin.H13.NQCat.T513P
