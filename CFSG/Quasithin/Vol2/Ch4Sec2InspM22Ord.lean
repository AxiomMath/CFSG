module

public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22LT
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic
public import CFSG.Adapters.LieModelOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem qtkOrd_PSp4_11 {S : Type} [Group S] (h : StatedClassicalModel S .PSp 2 11 1) :
    ¬ 443520 ∣ Nat.card S := by
  have hL : CFSG.Blueprint.LieModel S .PSp 2 11 1 := Or.inl ⟨by decide, h⟩
  rw [CFSG.GH74.card_of_lieModel_PSp (n := 2) (p := 11) (f := 1) (by norm_num) (by norm_num) hL]
  decide

theorem qtkOrd_G2_11
    {S : Type} [Group S] (h : ChevalleyExceptionalModel S .G2 11 1) :
    ¬ 443520 ∣ Nat.card S := by
  have hL : CFSG.Blueprint.LieModel S .G2 0 11 1 := Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  rw [CFSG.GH74.card_of_lieModel_G2 (n := 0) (p := 11) (f := 1) (by norm_num) hL]
  decide

theorem qtkOrd_PSp6_2 {S : Type} [Group S] (h : StatedClassicalModel S .PSp 3 2 1) :
    ¬ 443520 ∣ Nat.card S := by
  have hL : CFSG.Blueprint.LieModel S .PSp 3 2 1 := Or.inl ⟨by decide, h⟩
  rw [CFSG.Blueprint.LieModel.card_psp_three_two hL]
  decide

theorem qtkOrd_PSU5_4 {S : Type} [Group S] (h : StatedClassicalModel S .PSU 5 2 2) :
    ¬ 443520 ∣ Nat.card S := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_four h]
  decide

theorem qtkOrd_Tits
    {S : Type} [Group S] (h : ReeTitsModel S .Tits 2 1) :
    ¬ 443520 ∣ Nat.card S := by
  rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits h]
  decide

theorem qtkOrd_Suzuki {S : Type} [Group S] {f : ℕ}
    (h : SuzukiModel S 2 f) : ¬ 443520 ∣ Nat.card S := by
  obtain ⟨-, a, -, hf, hcard⟩ := CFSG.GH74.card_of_suzukiModel h
  rw [hcard]
  intro hdvd
  have h3 : 3 ∣ CFSG.Open.ordSuzuki (2 ^ f) := dvd_trans (by norm_num) hdvd
  have hq : 2 ^ f % 3 = 2 := by
    rw [hf, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  clear hdvd hcard
  unfold CFSG.Open.ordSuzuki at h3
  generalize 2 ^ f = q at h3 hq
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = r at h3 hq2
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h4 | h4
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h4 with h5 | h5
    · have h6 := Nat.mod_eq_zero_of_dvd h5
      omega
    · have h6 := Nat.mod_eq_zero_of_dvd h5
      omega
  · have h6 := Nat.mod_eq_zero_of_dvd h4
    omega

theorem qtkOrd_J1 {S : Type} [Group S]
    (h : Nonempty (S ≃* NativeSporadic.Carrier .J1)) : ¬ 443520 ∣ Nat.card S := by
  rw [CFSG.GH74.card_of_isSporadic_J1 h]
  decide

theorem qtkOrd_J2 {S : Type} [Group S]
    (h : Nonempty (S ≃* NativeSporadic.Carrier .J2)) : ¬ 443520 ∣ Nat.card S := by
  rw [CFSG.GH74.card_of_isSporadic_J2 h]
  decide

theorem qtkOrd_J3 {S : Type} [Group S]
    (h : Nonempty (S ≃* NativeSporadic.Carrier .J3)) : ¬ 443520 ∣ Nat.card S := by
  rw [CFSG.GH74.card_of_isSporadic_J3 h]
  decide

theorem qtkOrd_He {S : Type} [Group S]
    (h : Nonempty (S ≃* NativeSporadic.Carrier .He)) : ¬ 443520 ∣ Nat.card S := by
  have hc : Nat.card S = 4030387200 :=
    CFSG.GH74.card_eq_of_isSporadic (s := .He) CFSG.Sporadic.He.card_He h
  rw [hc]
  decide

theorem qtkOrd_Ru {S : Type} [Group S]
    (h : Nonempty (S ≃* NativeSporadic.Carrier .Ru)) : ¬ 443520 ∣ Nat.card S := by
  have hc : Nat.card S = 145926144000 :=
    CFSG.GH74.card_eq_of_isSporadic (s := .Ru) CFSG.Sporadic.Ru.card_Ru h
  rw [hc]
  decide

theorem qtkOrdNoM22_holds :
    QTKOrdNoM22 := by
  unfold QTKOrdNoM22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S _ _ h
    exact qtkOrd_PSp4_11 h
  · intro S _ _ h
    exact qtkOrd_G2_11 h
  · intro S _ _ h
    exact qtkOrd_PSp6_2 h
  · intro S _ _ h
    exact qtkOrd_PSU5_4 h
  · intro S _ _ h
    exact qtkOrd_Tits h
  · intro S _ _ f h
    exact qtkOrd_Suzuki h
  · intro S _ _ h
    exact qtkOrd_J1 h
  · intro S _ _ h
    exact qtkOrd_J2 h
  · intro S _ _ h
    exact qtkOrd_J3 h
  · intro S _ _ h
    exact qtkOrd_He h
  · intro S _ _ h
    exact qtkOrd_Ru h

end CFSG.Quasithin.H13.Ch4

end
