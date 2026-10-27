module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Route
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3NoFive
public import CFSG.RankThree.PartTwo.Sec15.MathAsch1511Of316

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14



theorem res1Thm340_l3
    (h316 : Sec19.Item316) {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop} (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X)
    (h5 : Res1L3NoFive Q P) : Sylow155R1.Res1Thm340 Q P :=
  res1Thm340_l3_of Sec14.Ronan149.item145BotS14_holds Sec14.Ronan149.item1444S14_holds
    Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds KFacts.kpSz hQ
    (claim153Normal_of_tau_l3 h316 hQ) h5

theorem res1Thm340_l3_of_even
    (h316 : Sec19.Item316) {P : ∀ (Y : Type) [Group Y], Prop}
    (heven : Res1L3NoFive Res1L3QEven P) : Sylow155R1.Res1Thm340 Res1L3Q P :=
  res1Thm340_l3 h316 (fun _ _ h => h) (res1L3NoFive_of_even heven)

theorem res1ZExclLeN_l2_l3_of_h150
    (h316 : Sec19.Item316) {Q : ∀ (X : Type) [Group X], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X) (h5 : Res1L3NoFive Q Res1OpenL2Type)
    (h150 : Sylow155R1.Res1Thm150b Q Res1OpenL2Type) :
    Sylow155R1.Res1ZExclLeN Q Res1OpenL2Type :=
  res1ZExclLeN_l2_l3_of_h340_h150 h316 hQ (res1Thm340_l3 h316 hQ h5) h150

theorem res1ZExclLeN_l2_l3_of_even_h150
    (h316 : Sec19.Item316)
    (heven : Res1L3NoFive Res1L3QEven Res1OpenL2Type)
    (h150 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenL2Type) :
    Sylow155R1.Res1ZExclLeN Res1L3Q Res1OpenL2Type :=
  res1ZExclLeN_l2_l3_of_h150 h316 (fun _ _ h => h) (res1L3NoFive_of_even heven) h150


theorem res1L3NoFive_even
    (h316 : Sec19.Item316) {P : ∀ (Y : Type) [Group Y], Prop} :
    Res1L3NoFive Res1L3QEven P := by
  intro G _ _ A c L X K Y M T P' Yc z τ Y' hY' hXY' hF hN
  obtain ⟨-, e, -, hLe⟩ := τ.q
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact not_case148Five_of_even item135_holds τ
    (Res1PtInputs.item152_at_lThreePi Sec14.Ronan149.item149S14_holds
      Sec14.Ronan148M.item148R_holds item134_holds Sec11.Close.closed_sec4Item4_8
      Sec4.Sporadic.rank3II_4_15 KFacts.kpSz τ.sec15 hLe)
    (Res1H1.item1511R_of_item316 h316 G A c L τ.sec15) hY' hXY' hF

theorem res1Thm340_l3_of_316
    (h316 : Sec19.Item316) {P : ∀ (Y : Type) [Group Y], Prop} :
    Sylow155R1.Res1Thm340 Res1L3Q P :=
  res1Thm340_l3_of_even h316 (res1L3NoFive_even h316)

theorem res1ZExclLeN_l2_l3_of_316_h150
    (h316 : Sec19.Item316)
    (h150 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenL2Type) :
    Sylow155R1.Res1ZExclLeN Res1L3Q Res1OpenL2Type :=
  res1ZExclLeN_l2_l3_of_even_h150 h316 (res1L3NoFive_even h316) h150

end CFSG.RankThree.PartTwo.Sec15.GagenL3
