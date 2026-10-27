module

public import CFSG.RankThree.PartOne.Mult.Trim
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi22Five
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi23Five
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi24Five
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi24Seven
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BFive
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BSeven
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open CFSG.RankThree.OddKernel CFSG.RankThree.PartOne.Mult CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
open CFSG.AGLEmbedding (KernelTrivialAt)

theorem dvd_card_of_isPGroup_ne_bot {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {K : Subgroup E} (hpK : IsPGroup p K) (hK : K ≠ ⊥) : p ∣ Nat.card K := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := hpK.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hK (Subgroup.card_eq_one.mp (by simpa using hk))
  rw [hk]
  exact dvd_pow_self p hk0

theorem eq_bot_of_restriction {E : Type} [Group E] [Finite E] {K : Subgroup E} {p : ℕ}
    (hp : p.Prime) (hpK : IsPGroup p K) {Q : ℕ → Prop}
    (hK : ∀ r : ℕ, r.Prime → r ∣ Nat.card K → Q r) (hQ : ¬ Q p) : K = ⊥ := by
  by_contra hne
  exact hQ (hK p hp (dvd_card_of_isPGroup_ne_bot hp hpK hne))

theorem kernelTrivialAt_carrier_of_five_le (h : SporadicResidualKernelsTrim)
    (s : TauCeti.SporadicName) (hs : s ≠ .M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    KernelTrivialAt (NativeSporadic.Carrier s) p := by
  refine kernelTrivialAt_carrier_of_sporadicKernelTrivial ?_
  intro E _ _ _ S _ π hS hπ hC hpk
  have h6 : Nat.Coprime (Nat.card π.ker) 6 := by
    have := Fact.mk hp
    obtain ⟨k, hk⟩ := hpk.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_)
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases p
    · exact absurd hd (by norm_num)
    · exact absurd hp (by decide)
  obtain ⟨c1, c2, c3, c4, -⟩ :=
    twenty_five_sporadic_central_prime_to_six_kernel_restriction π hπ hC h6
  cases s with
  | M => exact absurd rfl hs
  | M11 | M12 | M22 | M23 | M24 | J1 | J2 | J3 | J4 | HS | He | Ru =>
    exact c1 _ (by simp) hS
  | Co1 =>
    by_cases h5 : p = 5
    · subst h5; exact h.co1_five E S π hS hπ hC hpk
    by_cases h7 : p = 7
    · subst h7; exact h.co1_seven E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5 ∨ r = 7) (c2 _ (by simp) hS)
      (by show ¬ (p = 5 ∨ p = 7); rintro (hq | hq) <;> omega)
  | Th =>
    by_cases h5 : p = 5
    · subst h5; exact h.th_five E S π hS hπ hC hpk
    by_cases h7 : p = 7
    · subst h7; exact h.th_seven E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5 ∨ r = 7) (c2 _ (by simp) hS)
      (by show ¬ (p = 5 ∨ p = 7); rintro (hq | hq) <;> omega)
  | Fi24Prime =>
    by_cases h5 : p = 5
    · subst h5; exact sporadicKernelTrivial_fi24prime_five E S π hS hπ hC hpk
    by_cases h7 : p = 7
    · subst h7; exact sporadicKernelTrivial_fi24prime_seven E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5 ∨ r = 7) (c2 _ (by simp) hS)
      (by show ¬ (p = 5 ∨ p = 7); rintro (hq | hq) <;> omega)
  | B =>
    by_cases h5 : p = 5
    · subst h5; exact sporadicKernelTrivial_b_five E S π hS hπ hC hpk
    by_cases h7 : p = 7
    · subst h7; exact sporadicKernelTrivial_b_seven E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5 ∨ r = 7) (c2 _ (by simp) hS)
      (by show ¬ (p = 5 ∨ p = 7); rintro (hq | hq) <;> omega)
  | Co2 =>
    by_cases h5 : p = 5
    · subst h5; exact h.co2_five E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5) (c3 _ (by simp) hS)
      (by show ¬ p = 5; exact h5)
  | Co3 =>
    by_cases h5 : p = 5
    · subst h5; exact h.co3_five E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5) (c3 _ (by simp) hS)
      (by show ¬ p = 5; exact h5)
  | McL =>
    by_cases h5 : p = 5
    · subst h5; exact h.mcl_five E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5) (c3 _ (by simp) hS)
      (by show ¬ p = 5; exact h5)
  | Suz =>
    by_cases h5 : p = 5
    · subst h5; exact h.suz_five E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5) (c3 _ (by simp) hS)
      (by show ¬ p = 5; exact h5)
  | HN =>
    by_cases h5 : p = 5
    · subst h5; exact h.hn_five E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5) (c3 _ (by simp) hS)
      (by show ¬ p = 5; exact h5)
  | Ly =>
    by_cases h5 : p = 5
    · subst h5; exact h.ly_five E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5) (c3 _ (by simp) hS)
      (by show ¬ p = 5; exact h5)
  | Fi22 =>
    by_cases h5 : p = 5
    · subst h5; exact sporadicKernelTrivial_fi22_five E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5) (c3 _ (by simp) hS)
      (by show ¬ p = 5; exact h5)
  | Fi23 =>
    by_cases h5 : p = 5
    · subst h5; exact sporadicKernelTrivial_fi23_five E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 5) (c3 _ (by simp) hS)
      (by show ¬ p = 5; exact h5)
  | ONan =>
    by_cases h7 : p = 7
    · subst h7; exact h.on_seven E S π hS hπ hC hpk
    exact eq_bot_of_restriction hp hpk (Q := fun r => r = 7) (c4 hS)
      (by show ¬ p = 7; exact h7)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
