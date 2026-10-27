module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_prime_dvd_two_pow_sub_one_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ n - 1 ∧
      ((∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
        ∃ k : ℕ, n = 2 ^ k ∧ r = 3) := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨k, hk⟩ | ⟨p, hp, hpdvd, hpodd⟩
  · have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hk
      omega
    have h2n : 2 ∣ n := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    have h3dvd : 3 ∣ 2 ^ n - 1 := by
      simpa using Nat.pow_sub_one_dvd_pow_sub_one 2 h2n
    exact ⟨3, by norm_num, by norm_num, h3dvd, Or.inr ⟨k, hk, rfl⟩⟩
  · have hp1 : 1 < p := hp.one_lt
    have hp4 : 4 ≤ 2 ^ p := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
    have hne1 : 2 ^ p - 1 ≠ 1 := by omega
    obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hodd : Odd (2 ^ p - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' hp.pos.ne').mpr even_two) odd_one
    exact ⟨r, hrp, hodd.ne_two_of_dvd_nat hrdvd,
      hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hpdvd),
      Or.inl ⟨p, hpdvd, hpodd, hp1, hrdvd⟩⟩

theorem s23_9_A1_of (D : Data G) (Ch : Choice2011 G) (h53 : S23_5_3 D Ch) :
    S23_9_A1 D Ch := by
  intro h1930 c h3 _ hn
  obtain ⟨r, hrp, hr2, hrdvd, hcase⟩ :=
    exists_prime_dvd_two_pow_sub_one_of_three_le c.n (by omega)
  have hrmem : r ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hrp, hrdvd⟩
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨b, hborder⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) r hrmem.2
  have hbB0 : (b : G) ∈ c.B0 := b.2
  have hborder' : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe, hborder]
  let c' : Ctx23L D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hbZ : (b : G) ∉ Subgroup.centralizer (D.Z : Set G) := by
    intro hbC
    rcases h53 h1930 c' (by simpa [c'] using c.hpi) with hbot | ⟨h2, _⟩
    · have hbint : (b : G) ∈ c'.B ⊓ Subgroup.centralizer (D.Z : Set G) :=
        ⟨by simpa [c'] using hbB0, hbC⟩
      rw [hbot, Subgroup.mem_bot] at hbint
      have h1 : orderOf (b : G) = 1 := by rw [hbint, orderOf_one]
      rw [hborder'] at h1
      exact hrp.ne_one h1
    · have h2' : c.n = 2 * CFSG.Open.pRank 2 D.Z := by simpa [c'] using h2
      omega
  exact ⟨(b : G), hbB0, r, hrp, hr2, hborder', hbZ, hcase⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
