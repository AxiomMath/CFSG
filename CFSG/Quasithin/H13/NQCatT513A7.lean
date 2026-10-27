module

public import CFSG.Quasithin.H13.NQCatT513Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.Seven

theorem perm7_not_dvd (σ : Perm (Fin 7)) : ¬ 15 ∣ orderOf σ ∧ ¬ 21 ∣ orderOf σ := by
  have hsum : σ.cycleType.sum ≤ 7 := by
    have := Equiv.Perm.sum_cycleType_le σ
    simpa using this
  have hle : ∀ a ∈ σ.cycleType, a ≤ 7 := fun a ha => (Multiset.le_sum_of_mem ha).trans hsum
  have htwo : ∀ a ∈ σ.cycleType, 2 ≤ a := fun a ha => Equiv.Perm.two_le_of_mem_cycleType ha
  have hp : ∀ p, p.Prime → p ∣ orderOf σ → ∃ a ∈ σ.cycleType, p ∣ a := fun p hp h => by
    rw [← Equiv.Perm.lcm_cycleType] at h
    exact prime_dvd_of_dvd_lcm hp h
  constructor
  · intro h15
    obtain ⟨a, ha, h5⟩ := hp 5 (by norm_num) ((by norm_num : 5 ∣ 15).trans h15)
    obtain ⟨b, hb, h3⟩ := hp 3 (by norm_num) ((by norm_num : 3 ∣ 15).trans h15)
    have ha7 := hle a ha
    have hb7 := hle b hb
    have ha2 := htwo a ha
    have hb2 := htwo b hb
    have hab : a ≠ b := by omega
    have := add_le_sum_of_ne ha hb hab
    omega
  · intro h21
    obtain ⟨a, ha, h7⟩ := hp 7 (by norm_num) ((by norm_num : 7 ∣ 21).trans h21)
    obtain ⟨b, hb, h3⟩ := hp 3 (by norm_num) ((by norm_num : 3 ∣ 21).trans h21)
    have ha7 := hle a ha
    have hb7 := hle b hb
    have ha2 := htwo a ha
    have hb2 := htwo b hb
    have hab : a ≠ b := by omega
    have := add_le_sum_of_ne ha hb hab
    omega

theorem cycOddPerm_alt7 :
    CycOddPerm (alternatingGroup (Fin 7)) (fun _ => False) := by
  refine cycOddPerm_of_sylow isSylowTwoOf_T7 fun Dc hcyc hodd hperm => ?_
  have hT : Nat.card ↥T7 = 2 ^ 3 := by
    rw [T7, Nat.card_congr (Subgroup.subgroupOfEquivOfLe D7_le_A7s).toEquiv, card_D7]
    norm_num
  have hcop : Nat.Coprime (Nat.card ↥Dc) (Nat.card ↥T7) := by
    rw [hT]
    exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
  have hY := card_sup_of_perm hperm hcop
  obtain ⟨i, hi, hZ⟩ := overgroup_Z (M := Dc ⊔ T7) le_sup_right
  have hYc : Nat.card ↥(Dc ⊔ T7) =
      [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
    rw [← card_map_subtype, hZ, card_Z hi]
  rw [hY, hT] at hYc
  obtain ⟨g, -, hgo⟩ := exists_orderOf_eq_card hcyc
  have hord : orderOf ((g : alternatingGroup (Fin 7)) : Perm (Fin 7)) = Nat.card ↥Dc := by
    rw [Subgroup.orderOf_coe]
    exact hgo
  have hnd := perm7_not_dvd ((g : alternatingGroup (Fin 7)) : Perm (Fin 7))
  rw [hord] at hnd
  have hc : Nat.card ↥Dc = 1 ∨ Nat.card ↥Dc = 3 ∨ Nat.card ↥Dc = 9 := by
    interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hYc <;> omega
  rcases hc with hc | hc | hc
  · exact Or.inl ⟨0, hc⟩
  · exact Or.inl ⟨1, hc⟩
  · exact Or.inl ⟨2, hc⟩

end CFSG.Quasithin.H13.NQCat.T513P
