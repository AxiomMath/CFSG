module

public import CFSG.Permutation.FiveTransitive.Degree36OrderFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree36FivePower

open MulAction

private theorem eleven_le_fixed_fifth_power
    {X : Type} [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 36) (g : Equiv.Perm X) (hg : orderOf g = 25) :
    11 ≤ Nat.card (Function.fixedPoints (g ^ 5 : Equiv.Perm X)) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hne : g ^ 5 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hg] at hd
    norm_num at hd
  have hex : ∃ d ∈ g.cycleType, d ≠ 5 := by
    by_contra hn
    push Not at hn
    exact hne (Equiv.Perm.pow_prime_eq_one_iff.mpr hn)
  obtain ⟨d,hd,hdne⟩ := hex
  have hdd : d ∣ 25 := by rw [← hg]; exact Equiv.Perm.dvd_of_mem_cycleType hd
  have hdlo : 2 ≤ d := Equiv.Perm.two_le_of_mem_cycleType hd
  have hd25 : d = 25 := by
    have hdprime : d ∣ 5 ^ 2 := hdd
    obtain ⟨k,hkle,hdk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdprime
    interval_cases k <;> norm_num at hdk <;> omega
  rw [hd25,Equiv.Perm.cycleType_def] at hd
  obtain ⟨c,hc,hc25⟩ := Multiset.mem_map.mp hd
  have hcMem : c ∈ g.cycleFactorsFinset := hc
  change c.support.card = 25 at hc25
  let C := c.supportᶜ
  have hinv : ∀ x : X, g x ∈ C ↔ x ∈ C := by
    intro x
    simpa only [C,Finset.mem_compl] using
      not_congr (Equiv.Perm.mem_cycleFactorsFinset_support hcMem x)
  let r : Equiv.Perm C := g.subtypePerm hinv
  have hC : Fintype.card C = 11 := by
    rw [Fintype.card_coe,Finset.card_compl,hcard,hc25]
  have hr25 : r ^ 25 = 1 := by
    change g.subtypePerm hinv ^ 25 = 1
    rw [Equiv.Perm.subtypePerm_pow]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (g ^ 25) x.val = x.val
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hrdvd : orderOf r ∣ 5 ^ 2 := orderOf_dvd_of_pow_eq_one hr25
  obtain ⟨k,_hk,hkr⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hrdvd
  have hr5 := PrimePowerSmallDegree.pow_eq_one (by norm_num : Nat.Prime 5)
    (by rw [hC]; norm_num) r ⟨k,hkr⟩
  change g.subtypePerm hinv ^ 5 = 1 at hr5
  rw [Equiv.Perm.subtypePerm_pow] at hr5
  have hsub : (C : Set X) ⊆ Function.fixedPoints (g ^ 5 : Equiv.Perm X) := by
    intro x hx
    exact congrArg (fun e : Equiv.Perm C => (e ⟨x,hx⟩).val) hr5
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset,← Nat.card_coe_set_eq] at hle
  have hCfin : C.card = 11 := by simpa only [Fintype.card_coe] using hC
  rwa [hCfin] at hle

private theorem order_ne_twenty_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) : orderOf g ≠ 25 := by
  intro hg
  have horder : orderOf (g ^ 5) = 5 := by rw [orderOf_pow,hg]; norm_num
  have h11 := eleven_le_fixed_fifth_power hcard g.val ((Subgroup.orderOf_coe g).trans hg)
  have h6 := Degree36OrderFiveFixed.fixed_card_eq_six P hcard h5 hnotAlt
    (g ^ 5) horder (by exact le_trans (by norm_num) h11)
  change Nat.card (Function.fixedPoints (g.val ^ 5 : Equiv.Perm X)) = 6 at h6
  omega

theorem pow_five_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (he : ∃ e : ℕ, orderOf g = 5 ^ e) : g ^ 5 = 1 := by
  obtain ⟨e,he⟩ := he
  have hele : e ≤ 1 := by
    by_contra hn
    have hd : 25 ∣ orderOf g := by rw [he]; exact pow_dvd_pow 5 (by omega : 2 ≤ e)
    have hne : orderOf g ≠ 0 := by rw [he]; exact pow_ne_zero _ (by norm_num)
    exact order_ne_twenty_five P hcard h5 hnotAlt (g ^ (orderOf g / 25))
      (orderOf_pow_orderOf_div hne hd)
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [he]
  simpa only [pow_one] using pow_dvd_pow 5 hele

end FiveTransitive.Degree36FivePower

end CFSG
