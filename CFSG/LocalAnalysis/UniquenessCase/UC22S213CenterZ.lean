module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicLocal17
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.GH74.GLS.Stage2.Final.ECInterGriess

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_center_bar2_eq_bot_of_isSpor
    (hSC : PartTwo.Inputs1719.K_SporadicCoverCenterOdd) {M L : Subgroup G} (hL : L ∈ calC M)
    {s : TauCeti.SporadicName} (hs : s = .M11 ∨ s = .M23 ∨ s = .HS ∨ s = .J2 ∨ s = .He)
    (hX : IsSpor (BarInf L) s) : center (Bar2 L) = ⊥ := by
  obtain ⟨φ⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨f⟩ := hX
  have hs' : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .HS ∨
      s = .He ∨ s = .Ru ∨ s = .J4 := by
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp
  have hodd : Odd (Nat.card (center (Bar2 L))) := uc22p20p_odd_center_bar2 ↥L
  rcases hSC (Bar2 L) s hL.2.2 hodd ⟨φ.symm.trans f⟩ hs' with h | ⟨rfl, -⟩
  · exact h
  · rcases hs with h | h | h | h | h <;> cases h

theorem uc22s213_center_bar2_eq_bot_of_psl2 (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {p e : ℕ} (hp5 : 5 ≤ p)
    (hX : LieModel (BarInf L) .PSL 2 p e) : center (Bar2 L) = ⊥ := by
  obtain ⟨φ⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hL.2.2)
    ((CFSG.Blueprint.LieModel.of_mulEquiv φ hX).statedClassicalModel (by decide))
  have hgen : genericOrders .PSL 2 p e = (Nat.gcd 2 (p ^ e - 1), 1) := rfl
  rcases CFSG.GH74.GLS.Stage2.Final.ECInterGriess.exceptionalOrders_psl2 (p := p) (f := e)
      (by omega) with hexc | ⟨h3, -⟩
  · have h2 : Nat.card (center (Bar2 L)) ∣ 2 := by
      refine hdvd.trans ?_
      simp only [hgen, hexc, mul_one]
      exact Nat.gcd_dvd_left _ _
    have hodd : Odd (Nat.card (center (Bar2 L))) := uc22p20p_odd_center_bar2 ↥L
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  · omega

theorem uc22s213_center_bar2_eq_bot_of_psl_five_two (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) (hX : LieModel (BarInf L) .PSL 5 2 1) :
    center (Bar2 L) = ⊥ := by
  obtain ⟨φ⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hL.2.2)
    ((CFSG.Blueprint.LieModel.of_mulEquiv φ hX).statedClassicalModel (by decide))
  have hgen : genericOrders .PSL 5 2 1 = (1, 1) := rfl
  have hexc : exceptionalOrders .PSL 5 2 1 = (1, 1) := rfl
  simp only [hgen, hexc, mul_one, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

theorem uc22s213_center_bar2_eq_bot_of_isAlt {M L : Subgroup G} (hL : L ∈ calC M) {m : ℕ}
    (hm : 8 ≤ m) (hX : IsAlt (BarInf L) m) : center (Bar2 L) = ⊥ := by
  obtain ⟨φ⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨f⟩ := hX
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
  have hker := CFSG.GH74.Generic.centralQuotientMap_ker (φ.symm.trans f)
  have hodd : Odd (Nat.card (center (Bar2 L))) := uc22p20p_odd_center_bar2 ↥L
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) _
    (CFSG.GH74.Generic.centralQuotientMap_surjective (φ.symm.trans f)) hker.le
    (by rw [hker]; exact hodd)
  rw [hker] at h1
  exact Subgroup.eq_bot_of_card_eq _ h1

end CFSG.LocalAnalysis.UniquenessCase.UC22
