module

public import CFSG.RankThree.PartTwo.Sec14.Step143BalanceHolds
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly3
public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q171Delta
public import CFSG.RankThree.PartTwo.Sec17.C174Para2Concl143
public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofHJ
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof177Q0
public import CFSG.RankThree.PartTwo.Sec17.LitScopeProof
public import CFSG.RankThree.PartTwo.Sec17.Item171GenProof

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

theorem item143_of_proved
    : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G), Sec14Std G A c L → Item143 A (lB A) :=
  fun G _ _ A c L h => Ronan148Q.item143_of_item143Q (Ronan148M.item143QS14_holds G A c L h)

theorem item174_of_item143
    (h135 : Item135) (h145 : Item145BotS14) (h146 : Item146S14)
    (h149 : Item149S14) (h1411 : Item1411_1S17) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (h166 : Item166S17) (h167 : Item167R) (h168 : Item168S17)
    (h172 : Item172S17) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → Item174 A (lB A) := by
  intro G _ _ A c L Y₀ h
  have h166' : Item166 A (lB A) := h166 G A c L Y₀ h
  rcases h.a10_or_omega with hA10 | hΩ
  · intro X hXΔ hX3
    by_contra hns
    obtain ⟨K, hK, n, hn⟩ := kFact174_holds G A c L Y₀ h X hXΔ hX3 hns
    exact C174.not_five_dvd_cQuot_of_a10 h hA10
      (C174.five_dvd_card_cQuot_of_suzuki h166' h hXΔ hX3 hK ⟨n, hn⟩)
  · have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
      rcases h1514 G A c L Y₀ h Y₀ h.mem_y0Star (hMeets G A c L Y₀ h) with
        ⟨-, -, -, hprod, -⟩ | ⟨-, -, hTr, -⟩ | ⟨-, -, -, -, hle, -⟩
      · exact card_inf_eq_nine_of_prod h hprod
      · exfalso
        have h3 := hTr.1
        rw [hΩ, Set.ncard_singleton] at h3
        omega
      · exact absurd h.le_y0 (hle Y₀ h.mem_y0Star)
    exact rank3II_17_4_of_printM h h166' (h145 G A c L h.toSec14Std) (h168 G A c L Y₀ h)
      (h146 G A c L h.toSec14Std) (h172 G A c L Y₀ h) h9 kFact174_holds
      (C174.claim174_of_inputs h135 h145 h146 Ronan148M.item148NHJS14_holds h149 h1411 h166 h167)
      (C174.step174KbM_of_item143 h135 item143_of_proved h146 h166)

theorem item171S17_holds
    (h1444 : Item1444S14) (h146 : Item146S14) (h145 : Item145BotS14)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Item171S17 := by
  obtain ⟨h45, -, -, h422, -, -, -, -, -, -, h142All⟩ := Ronan148M.closedInputs
  have h142R : Item142R := Sec14.item142R_of_wired h142All
  have h143Q : Ronan148Q.Item143QS14 := Ronan148M.item143QS14_holds
  have hD0 : Step171Delta0 := Ronan143Q.step171Delta0_ofQ h422 h45 h142R h143Q
  have hQ : Step171CommQ := step171CommQ_of h1444 h146 (item145BotS17_of h145) h1514 hMeets
  exact item171S17_of_steps h1514 hMeets Ronan148M.concl142S14_holds (step171Comm_of hQ hD0)
    hD0

theorem step177Meet_holds
    (h1444 : Item1444S14) (h146 : Item146S14) (h145 : Item145BotS14)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Step177Meet :=
  step177Meet_of_claim17Q0 (claim17Q0_of_step171CommQ
    (step171CommQ_of h1444 h146 (item145BotS17_of h145) h1514 hMeets))

theorem step177Contra_holds
    (h171 : Item171S17) (h9 : CardInfNineS17)
    (hsol : Step177OThreeSolv) : Step177Contra := by
  obtain ⟨-, h48, -, -, -, -, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact step177Contra_of_items h171 step143Balance_holds h9 hsol h134 h48

theorem step177MainB_holds
    (h171 : Item171S17) (h9 : CardInfNineS17)
    (hsol : Step177OThreeSolv) : Step177MainB :=
  step177MainB_of_any (step177MainMAny_of_MB
    (step177MainMB_of_contra (step177Contra_holds h171 h9 hsol) step143Balance_holds h9))

theorem item177S17_of_inputs
    (h310 : Sec6.Item3_10) (h135 : Item135) (h145 : Item145BotS14)
    (h146 : Item146S14) (h149 : Item149S14) (h1411 : Item1411_1S17)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h166 : Item166S17) (h167 : Item167R)
    (h168 : Item168S17) (h172 : Item172S17) (h176 : Item176R) (h9 : CardInfNineS17)
    (h1444 : Item1444S14) : Item177S17 := by
  have hsol : Step177OThreeSolv :=
    step177OThreeSolv_of_printM h166 (item145BotS17_of h145) h168 h146 h172 h9 kFact174_holds
      (C174.claim174_of_inputs h135 h145 h146 Ronan148M.item148NHJS14_holds h149 h1411 h166 h167)
      (C174.step174KbM_of_item143 h135 item143_of_proved h146 h166)
  have h171 : Item171S17 := item171S17_holds h1444 h146 h145 h1514 hMeets
  exact item177S17_of_B_one (item177One_of_item3_10 h310) h1514 hMeets claim1715A_of h176
    (step177Meet_holds h1444 h146 h145 h1514 hMeets) (step177MainB_holds h171 h9 hsol)

end CFSG.RankThree.PartTwo.Sec17
