module

public import CFSG.Quasithin.Background.GoldschmidtZ2D8Core
public import CFSG.Quasithin.Background.F6CatRecogInputs2
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.GH74.Orders.LieType
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru

public section

namespace CFSG.Quasithin.F6

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Exceptional


theorem noSylowZ2D8_of_g2 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : NoSylowZ2D8 S := by
  have hcard : Nat.card S = CFSG.Open.ordG2 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  exact noSylowZ2D8_of_card_eq_of_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordG2 hf).two (by omega)

theorem noSylowZ2D8_of_trialityD4 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) : NoSylowZ2D8 S := by
  have hcard : Nat.card S = CFSG.Open.ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  exact noSylowZ2D8_of_card_eq_of_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hf).two (by omega)

theorem noSylowZ2D8_of_twistedF4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : ReeTitsModel S .twistedF4 2 f) : NoSylowZ2D8 S := by
  obtain ⟨k, -, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel h
  exact noSylowZ2D8_of_card_eq_of_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 (by omega)).two (by omega)

end Exceptional

section Suzuki


theorem noSylowZ2D8_of_suzuki {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : SuzukiModel S 2 f) : NoSylowZ2D8 S := by
  obtain ⟨-, a, -, hf, hcard⟩ := CFSG.GH74.card_of_suzukiModel h
  exact noSylowZ2D8_of_card_eq_of_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordSuzuki (by omega)).two (by omega)

end Suzuki

section Tits


theorem noSylowZ2D8_of_tits {S : Type} [Group S] [Finite S]
    (h : ReeTitsModel S .Tits 2 1) : NoSylowZ2D8 S := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 h
  have hc : Nat.card S = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  exact noSylowZ2D8_of_card_eq (a := 11) (by norm_num) ⟨8775, by decide, by rw [hc]; norm_num⟩

end Tits

section Sporadic


theorem noSylowZ2D8_of_sporadic {S : Type} [Group S] [Finite S] {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru)
    (e : S ≃* NativeSporadic.Carrier s) : NoSylowZ2D8 S := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have e' : S ≃* NativeSporadic.M11 := e
    refine noSylowZ2D8_of_orderOf_eq_eight
      (a := e'.symm ⟨CFSG.GH74.SmallRanks.m11Elt, CFSG.GH74.SmallRanks.m11Elt_mem⟩) ?_
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact CFSG.GH74.SmallRanks.orderOf_m11Elt.trans (by norm_num)
  · have hc : Nat.card S = 95040 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M12
    exact noSylowZ2D8_of_card_eq (a := 6) (by norm_num) ⟨1485, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 443520 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M22
    exact noSylowZ2D8_of_card_eq (a := 7) (by norm_num) ⟨3465, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 10200960 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Quasithin.H13.card_native_M23_eq
    exact noSylowZ2D8_of_card_eq (a := 7) (by norm_num) ⟨79695, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 244823040 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M24
    exact noSylowZ2D8_of_card_eq (a := 10) (by norm_num) ⟨239085, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    exact noSylowZ2D8_of_card_eq (a := 3) (by norm_num) ⟨21945, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 604800 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    exact noSylowZ2D8_of_card_eq (a := 7) (by norm_num) ⟨4725, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 86775571046077562880 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J4.card_J4
    exact noSylowZ2D8_of_card_eq (a := 21) (by norm_num)
      ⟨41377816699065, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 44352000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.HS.card_HS
    exact noSylowZ2D8_of_card_eq (a := 9) (by norm_num) ⟨86625, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 4030387200 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.He.card_He
    exact noSylowZ2D8_of_card_eq (a := 10) (by norm_num) ⟨3935925, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 145926144000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ru.card_Ru
    exact noSylowZ2D8_of_card_eq (a := 14) (by norm_num) ⟨8906625, by decide, by rw [hc]; norm_num⟩

end Sporadic

section List


theorem noSylowZ2D8_of_sqtkSimpleList {S : Type} [Group S] [Finite S]
    (h : CFSG.Milestones.SQTKSimpleList S) : NoSylowZ2D8 S := by
  rcases h with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hodd⟩ | (⟨f, hf⟩ | htits) | ⟨n, hn, hmodel⟩ |
    ⟨s, hs, ⟨e⟩⟩
  · exact noSylowZ2D8_of_alternating hn5 hn8 e
  · rcases hodd with ⟨f, -, h⟩ | h | h
    · exact noSylowZ2D8_of_psl_two_odd hp hp2 h
    · exact noSylowZ2D8_of_psl_three_odd hp hp2 h
    · exact noSylowZ2D8_of_psu_three_odd hp hp2 h
  · rcases hf with ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact noSylowZ2D8_of_psl_two_even hf h
    · exact noSylowZ2D8_of_psl_char_two h (by omega)
    · exact noSylowZ2D8_of_psu_char_two h (by omega)
    · exact noSylowZ2D8_of_psp_char_two h (by omega)
    · exact noSylowZ2D8_of_g2 (by omega) h
    · exact noSylowZ2D8_of_trialityD4 hf h
    · exact noSylowZ2D8_of_twistedF4 h
    · exact noSylowZ2D8_of_suzuki h
  · exact noSylowZ2D8_of_tits htits
  · rcases hn with rfl | rfl
    · exact noSylowZ2D8_of_psl_char_two hmodel (by norm_num)
    · exact noSylowZ2D8_of_psl_char_two hmodel (by norm_num)
  · exact noSylowZ2D8_of_sporadic hs e

theorem z2D8SylowListFact_holds : Z2D8SylowListFact :=
  fun _ _ _ h P => noSylowZ2D8_of_sqtkSimpleList h P

end List

end CFSG.Quasithin.F6
