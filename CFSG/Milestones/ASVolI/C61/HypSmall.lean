module

public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
public import CFSG.Milestones.ASVolI.C5Blocks
public import CFSG.Quasithin.EmptyFaithful.SBc15WDefs

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.Quasithin.S152N

noncomputable local instance burnsideC56_instFintypeW3 : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance burnsideC56_instDecEqW3 : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance burnsideC56_instDecN0 : DecidablePred (· ∈ W3.N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

theorem burnsideC56_W3_pow_nine : ∀ w : W3, w ^ 9 = 1 → w ^ 3 = 1 := by
  decide +kernel

theorem burnsideC56_W3_N0_pow_three : ∀ w : W3, w ∈ W3.N0 → w ^ 3 = 1 := by
  decide +kernel

theorem burnsideC56_W3_N0_comm : ∀ a b : W3, a ∈ W3.N0 → b ∈ W3.N0 → a * b = b * a := by
  decide +kernel

theorem burnsideC56_W3_mem_N0_of_odd {w : W3} (hw : Odd (orderOf w)) : w ∈ W3.N0 := by
  have h72 : orderOf w ∣ 8 * 9 := by
    have h := orderOf_dvd_natCard w
    rw [W3.card_eq] at h
    exact h
  have hcop : Nat.Coprime (orderOf w) 8 := by
    have : Nat.Coprime (orderOf w) (2 ^ 3) :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hw)
    simpa using this
  have h9 : orderOf w ∣ 9 := hcop.dvd_of_dvd_mul_left h72
  exact W3.mem_N0_of_pow_three w (burnsideC56_W3_pow_nine w (orderOf_dvd_iff_pow_eq_one.mp h9))

theorem burnsideC56_W3_oTwoUpper : oTwoUpper (⊤ : Subgroup W3) = W3.N0 := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr fun w hw => burnsideC56_W3_mem_N0_of_odd hw.2
  · intro w hw
    refine mem_oTwoUpper_of_odd (Subgroup.mem_top w) ?_
    have h3 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one (burnsideC56_W3_N0_pow_three w hw)
    exact Odd.of_dvd_nat (by decide) h3

theorem burnsideC56_W3_umax :
    ∀ S : Subgroup W3, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S := by
  intro S hS hSi
  have hSyl : IsSylowTwoOf S ⊤ := ⟨le_top, hS, by
    change ¬ 2 ∣ S.relIndex ⊤
    rwa [Subgroup.relIndex_top_right]⟩
  refine ⟨S, lt_of_le_of_ne le_top fun h => ?_, le_rfl, fun B hSB hB => ?_⟩
  · have h9 := W3.index_eq_nine hSyl
    rw [h, Subgroup.index_top] at h9
    omega
  · rcases W3.sylow_maximal hSyl hSB with h | h
    · exact h.le
    · exact absurd h hB.ne

theorem burnsideC56_umax_of_card_six {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 6) :
    ∀ S : Subgroup Y, IsPGroup 2 S → ¬ 2 ∣ S.index → burnsideC5h_p1_UMaxIn ⊤ S := by
  intro S hS hSi
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : Nat.card S = 2 := by
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hmul := S.card_mul_index
    rw [hk, hY] at hmul
    have hk3 : k < 3 := by
      by_contra h
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have : 2 ^ k * S.index ≥ 8 := le_trans (by omega) (Nat.mul_le_mul h8 hpos)
      omega
    interval_cases k
    · exfalso
      apply hSi
      rw [pow_zero, one_mul] at hmul
      rw [hmul]
      norm_num
    · simpa using hk
    · exfalso
      omega
  refine ⟨S, lt_of_le_of_ne le_top fun h => ?_, le_rfl, fun B hSB hB => ?_⟩
  · rw [h, Subgroup.card_top, hY] at hS2
    omega
  · have hB6 : Nat.card B ∣ 6 := hY ▸ Subgroup.card_subgroup_dvd_card B
    have hB2 : 2 ∣ Nat.card B := hS2 ▸ Subgroup.card_dvd_of_le hSB
    have hBne : Nat.card B ≠ 6 := fun h6 => hB.ne (Subgroup.eq_top_of_card_eq B (h6.trans hY.symm))
    have hBle : Nat.card B ≤ 6 := Nat.le_of_dvd (by norm_num) hB6
    have hBcard : Nat.card B = 2 := by
      interval_cases hc : Nat.card B <;> omega
    exact (Subgroup.eq_of_le_of_card_ge hSB (by rw [hBcard, hS2])).symm.le

theorem burnsideC56_card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem burnsideC56_perm_three_isSolvable : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
  CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_card_two_three (a := 1) (b := 1)
    (by rw [burnsideC56_card_perm_three]; norm_num)

theorem burnsideC56_W3_isSolvable : Group.IsSolvable W3 :=
  CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_card_two_three (a := 3) (b := 2)
    (by rw [W3.card_eq]; norm_num)

theorem burnsideC56_not_cube_dvd_of_dvd_72 {N p : ℕ} (hN : N ∣ 72) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 3 ∣ N := by
  intro hd
  have h1 : p ^ 3 ∣ 72 := hd.trans hN
  have h2 : p ^ 3 ≤ 72 := Nat.le_of_dvd (by norm_num) h1
  have hp5 : p < 5 := by
    by_contra h
    have : 5 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p <;> first
    | (exfalso; revert hp; norm_num; done)
    | omega
    | (exfalso; revert h1; norm_num; done)

end CFSG.ASVolI
