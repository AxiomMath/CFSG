module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVG23
public import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowR27

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)


theorem rowSEpsOf_alternating_nine_twelve {n : ℕ} (hn9 : 9 ≤ n) (hn12 : n ≤ 12) :
    RowSEpsOf (alternatingGroup (Fin n)) := by
  intro S _ _ _ _ ⟨φ⟩
  have hS := (Nat.card_congr φ.toEquiv).trans (KS14.card_alternatingGroup_fin (n := n) (by omega))
  have hn : n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 := by omega
  rcases hn with rfl | rfl | rfl | rfl <;>
    exact noCfgSEps_of_card (B := 3) hS.dvd (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_three :
    ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
      RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := by
  intro hr S _ _ _ _ ⟨e⟩
  obtain ⟨f⟩ := CFSG.AGLEmbedding.ReeModel.nonempty_reeGamma_equiv 1 le_rfl hr
  have hcard : Nat.card RonanK432.Ree27 = 10073444472 := by
    rw [CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq RonanK432.card_ree27Field]
    norm_num
  have h1 : Nat.card S = Nat.card RonanK432.Ree27 :=
    Nat.card_congr (e.toEquiv.trans f.toEquiv.symm)
  exact noCfgSEps_of_card (N := 10073444472) (B := 3) (h1.trans hcard).dvd (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSEpsOf (projSL 3 (GaloisField 3 e)) := by
  intro e he1 he3
  intro S _ _ _ _ ⟨φ⟩
  have hS := (Nat.card_congr φ.toEquiv).trans (RowV.card_projSL_three_char_three he1)
  obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  · exact noCfgSEps_of_card (B := 3) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact noCfgSEps_of_card (B := 3) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact noCfgSEps_of_card (B := 4) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)

theorem rowSEpsOf_nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSEpsOf (projSU 3 3 e) := by
  intro e he1 he3
  intro S _ _ _ _ ⟨φ⟩
  have hS := (Nat.card_congr φ.toEquiv).trans (RowV.card_projSU_three_char_three he1)
  obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  · exact noCfgSEps_of_card (B := 3) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact noCfgSEps_of_card (B := 3) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact noCfgSEps_of_card (B := 4) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)

theorem rowSEpsOf_nine_G2 :
    RowSEpsOf (TauCeti.CFSGIndex.lie g2ThreeIndex).Group := by
  intro S _ _ _ _ ⟨φ⟩
  exact noCfgSEps_of_card (N := CFSG.Open.ordG2 3) (B := 3)
    (by rw [Nat.card_congr φ.toEquiv]; exact RowV.card_g2_three_dvd)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_nine_SL4 : RowSEpsOf (projSL 4 (GaloisField 3 1)) := by
  intro S _ _ _ _ ⟨φ⟩
  exact noCfgSEps_of_card (N := 3 ^ 6 * 16640) (B := 3)
    (by rw [Nat.card_congr φ.toEquiv]; exact RowV.card_projSL_four_three_dvd)
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_nine_SU4 : RowSEpsOf (projSU 4 3 1) := by
  intro S _ _ _ _ ⟨φ⟩
  have hS := (Nat.card_congr φ.toEquiv).trans CFSG.PGLModel.card_projSU_four_three
  exact noCfgSEps_of_card (B := 3) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

end CFSG.RankThree.PartTwo.Sec4.RonanEps
