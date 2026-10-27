module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU43
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVG23
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL52
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowR27

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Easy

theorem noCQOf_projSL_three_char_three {e : ℕ} (he : e = 1 ∨ e = 3) :
    NoCQOf (projSL 3 (GaloisField 3 e)) := by
  have hS := RowV.card_projSL_three_char_three (e := e) (by omega)
  rcases he with rfl | rfl
  · exact NoCQOf.of_card_dvd (B := 18) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
  · exact NoCQOf.of_card_dvd (B := 6558) hS.dvd (by norm_num) (by norm_num)
      (by decide +kernel)

theorem noCQOf_projSU_three_char_three {e : ℕ} (he : e = 1 ∨ e = 3) :
    NoCQOf (projSU 3 3 e) := by
  have hS := RowV.card_projSU_three_char_three (e := e) (by omega)
  rcases he with rfl | rfl
  · exact NoCQOf.of_card_dvd (B := 19) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
  · exact NoCQOf.of_card_dvd (B := 6559) hS.dvd (by norm_num) (by norm_num)
      (by decide +kernel)

theorem noCQOf_g2_three : NoCQOf (TauCeti.CFSGIndex.lie g2ThreeIndex).Group :=
  NoCQOf.of_card_dvd (M := CFSG.Open.ordG2 3) (B := 170) RowV.card_g2_three_dvd
    (by decide) (by decide +kernel) (by decide +kernel)

theorem noCQOf_three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    NoCQOf (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := by
  intro hr
  obtain ⟨f⟩ := CFSG.AGLEmbedding.ReeModel.nonempty_reeGamma_equiv 1 le_rfl hr
  have hcard : Nat.card RonanK432.Ree27 = 10073444472 := by
    rw [CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq RonanK432.card_ree27Field]
    norm_num
  refine NoCQOf.of_card_dvd (M := 10073444472) (B := 2200) ?_ (by norm_num) (by norm_num)
    (by decide +kernel)
  rw [← Nat.card_congr f.toEquiv, hcard]

theorem noCQOf_u43 : NoCQOf (projSU 4 3 1) :=
  NoCQOf.of_noCQ425 (noCC425_of_card_dvd (M := 653184) (B := 87) (by norm_num) (by norm_num)
    (by decide +kernel) fun s hs => RowV.card_centralizer_u43_dvd s hs)

theorem noCQOf_eight_SL5 : NoCQOf (projSL 5 (GaloisField 2 1)) := by
  refine NoCQOf.of_not_dvd ?_
  rw [← Nat.card_congr Res417Four.gl5EquivProjSL.toEquiv]
  exact RonanK432.not_27_dvd_card_gl5

theorem noCQOf_eight_SU5_4 : NoCQOf (projSU 5 2 2) := by
  refine NoCQOf.of_not_dvd ?_
  rw [Item434SmallTwoOther.U54.card_U54]
  norm_num

theorem noCQOf_seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    NoCQOf (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
  intro m hm
  refine NoCQOf.of_not_dvd ?_
  obtain ⟨-, a, -, F, _, _, hf, hK', ⟨θ⟩⟩ := Census.suzukiModel_of_index m hm
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3 : ¬ 3 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
    rw [Nat.card_congr θ.toEquiv]
    exact KFacts.not_three_dvd_card_suzukiGroup hK
  exact fun h => h3 ((show 3 ∣ 27 by norm_num).trans h)

theorem noCQOf_m11 :
    NoCQOf (Spor .M11) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M11 ≃* Spor .M11 := b
  refine NoCQOf.of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M11]
  norm_num

theorem noCQOf_m22 :
    NoCQOf (Spor .M22) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M22 ≃* Spor .M22 := b
  refine NoCQOf.of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
  norm_num

theorem noCQOf_m23 :
    NoCQOf (Spor .M23) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M23 ≃* Spor .M23 := b
  refine NoCQOf.of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Schreier.m23_card]
  norm_num

theorem noCQOf_j1 :
    NoCQOf (Spor .J1) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J1 ≃* Spor .J1 := b
  refine NoCQOf.of_not_dvd ?_
  rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J1.card_J1]
  norm_num

theorem noCQOf_hs :
    NoCQOf (Spor .HS) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  refine NoCQOf.of_not_dvd ?_
  rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.HS.card_HS]
  norm_num

end Easy

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
