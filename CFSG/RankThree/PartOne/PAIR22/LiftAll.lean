module

public import CFSG.RankThree.PartOne.PAIR22.Odd
public import CFSG.RankThree.PartOne.PAIR22.SzLift
public import CFSG.RankThree.PartOne.K1320.Row6
public import CFSG.RankThree.PartOne.KF.F132F4Bridge
public import CFSG.RankThree.PartOne.KF.F132Row2Types
public import CFSG.RankThree.PartOne.KF.F132Row3Types
public import CFSG.RankThree.PartOne.KF.F132Row7Frame
public import CFSG.RankThree.PartOne.KF.F132Row8Frame
public import CFSG.RankThree.PartOne.Mult.Exceptional
public import CFSG.RankThree.PartOne.S13K.Row1

public section

namespace CFSG.RankThree.PartOne.PAIR22

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def PairLiftRows : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A →
    ∀ u ∈ reflectionSet p E, u ∈ torusImage E L → PairLift p E u

theorem pairLiftRows_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    PairLiftRows := by
  have hECS := Mult.exceptionalCenterSmallPrimes_of_griess hGA
  intro G _ _ p A c L E h hF hF13 hT hEA u hu huL
  obtain ⟨-, r, hr1, hr12, hrow, -, hrA, hr9⟩ := hF.three
  have hr8 : r ≤ 8 := by
    by_contra hlt
    have h4 := hr9 (by omega)
    rw [hEA, h.A_card] at h4
    have hp := h.prime
    have h5 := Sec12Three.five_le h
    have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hsplit := (hF13.reflection u hu).1
  have ht2 : u * u = 1 := RefFacts.mul_self_eq_one hu.1
  interval_cases r
  · obtain ⟨f, g, -, -, hKF⟩ :=
      kf132At_row1 hGA G p A c L E h hF hF13 hT (by norm_num) hrow hrA hr9 u hu huL
    exact pairLift_of_kfAt hKF
  · obtain ⟨f, g, -, -, hKF⟩ :=
      kf132At_row2 hGA hECS G p A c L E h hF hF13 hT (by norm_num) hrow hrA hr9 u hu huL
    exact pairLift_of_kfAt hKF
  · obtain ⟨f, g, -, -, hKF⟩ :=
      kf132At_row3 hGA hECS G p A c L E h hF hF13 hT (by norm_num) hrow hrA hr9 u hu huL
    exact pairLift_of_kfAt hKF
  ·
    obtain ⟨f, hf1, hpq, hmod⟩ := hrow
    rcases KF132.kf132Row4_classes hGA (KF132.twistedF4CenterBot_of_hGA hGA) h hF hF13 hEA hf1 hpq
        hmod u hu huL with hKF | hSz
    · exact pairLift_of_kfAt hKF
    · obtain ⟨x, -, hx, hxt⟩ := Sec12Three.mem_torusImage_iff.mp huL
      exact pairLift_of_szAt hsplit ht2 hx hxt hSz
  · obtain ⟨f, g, -, -, hKF⟩ :=
      kf132At_row5 hGA G p A c L E h hF hF13 hT (by norm_num) hrow hrA hr9 u hu huL
    exact pairLift_of_kfAt hKF
  ·
    obtain ⟨f, hf1, hpq, hmod⟩ := hrow
    rcases (KF132.kf132Row6_frame hGA h hF hF13 hEA hf1 hpq hmod).1 u hu huL with hEx | hKF
    · exact K1320.row6Lift_holds hGA G p A c L E f h hF hF13 hT hEA hf1 hpq hmod u hu huL hEx
    · exact pairLift_of_kfAt hKF
  · obtain ⟨f, g, -, -, hKF⟩ :=
      kf132At_row7 hGA G p A c L E h hF hF13 hT (by norm_num) hrow hrA hr9 u hu huL
    exact pairLift_of_kfAt hKF
  · obtain ⟨f, g, -, -, hKF⟩ :=
      kf132At_row8 hGA G p A c L E h hF hF13 hT (by norm_num) hrow hrA hr9 u hu huL
    exact pairLift_of_kfAt hKF

theorem pairLiftAll_of_rows (hRe : Sec13Reinst) (hRows : PairLiftRows) : PairLiftAll := by
  intro G _ _ p A c L E h hF hF13 hT hEA u hu
  obtain ⟨hrefl, Y, hY, huY⟩ := hu
  obtain ⟨B, c', hB, hc'B, hc'1, hY12, hYF, hY13, hYT⟩ := hRe G p A c L E h hF13 hT Y hY
  have hBE : B = E := Subgroup.eq_of_le_of_card_ge hB.1 (by rw [hB.2.2.1, hEA, h.A_card])
  exact hRows G p B c' Y E hY12 hYF hY13 hYT hBE.symm u ⟨hrefl, Y, hY, huY⟩ huY

end CFSG.RankThree.PartOne.PAIR22
