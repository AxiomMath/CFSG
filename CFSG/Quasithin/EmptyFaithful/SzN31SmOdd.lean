module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmallStmt
public import CFSG.Quasithin.EmptyFaithful.SzN31CntM3p

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

namespace SmOdd

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem not_three_dvd_two_pow_sub_one_of_odd {d : ℕ} (hd : Odd d) : ¬ 3 ∣ 2 ^ d - 1 := by
  obtain ⟨k, rfl⟩ := hd
  have h : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpos : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * k + 1) = x at h hpos ⊢
  omega

theorem pCoreOf_three_eq_bot_of_odd {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hodd : Odd (Module.finrank (ZMod 2) V)) : pCoreOf 3 Γ = ⊥ := by
  by_contra hne
  have hfix := g94_fixedSpace_pCoreOf_eq_bot hyp hne
  have hdvd := pgroup_dvd_two_pow Nat.prime_three (pCoreOf 3 Γ) (isPGroup_pCoreOf 3 Γ) ⊤
    (fun _ _ _ _ => Submodule.mem_top) (fun v _ hv => by
      have hv' : v ∈ fixedSpace (pCoreOf 3 Γ) := hv
      rw [hfix] at hv'
      simpa using hv')
  rw [finrank_top] at hdvd
  exact not_three_dvd_two_pow_sub_one_of_odd hodd hdvd

end SmOdd

open SmOdd

theorem smallOdd : SmallOdd := by
  intro V _ _ _ Γ A m hyp _ _ _ hodd
  have h3 := pCoreOf_three_eq_bot_of_odd hyp hodd
  have hcent : ∀ p : ℕ, p.Prime → p ≠ 2 →
      A ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) := by
    intro p hp hp2
    by_cases hp3 : p = 3
    · subst hp3
      rw [h3]
      intro a _
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Subgroup.mem_bot.mp hg]; simp
    · have h5 : 5 ≤ p := by
        have := hp.two_le
        by_contra h
        interval_cases p
        · exact hp2 rfl
        · exact hp3 rfl
        · exact absurd hp (by decide)
      by_contra hnot
      have hd4 := (counting_prime_ge_five hyp hp h5 hnot).2.2
      rw [hd4] at hodd
      exact absurd hodd (by decide)
  have hA : A = ⊥ := g94_eq_bot_of_le_centralizer_pCoreOf hyp le_rfl hcent
  have h1 := hyp.A_card
  rw [hA, Subgroup.card_bot] at h1
  have h2 := Nat.one_lt_two_pow (n := m) (by have := hyp.A_ne; omega)
  omega

end CFSG.Quasithin.SzN31
