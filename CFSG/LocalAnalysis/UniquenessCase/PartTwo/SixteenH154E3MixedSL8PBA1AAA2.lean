module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.Quasithin.Background.F918J3
public import CFSG.RankThree.PartOne.TCP.AlModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_SL2_eight_lieModel {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    CFSG.Blueprint.LieModel ↥(autSub L (commSub ⊤ L)) .PSL 2 2 3 := by
  classical
  obtain ⟨hSL, _hNat⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e2⟩⟩ := hSL
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    rw [FiniteField.even_card_iff_char_two]
    rw [Fintype.card_eq_nat_card, hKcard]
    norm_num
  letI : CharP K 2 := hchar ▸ ringChar.charP K
  let U : Subgroup W := commSub ⊤ L
  let Z : Subgroup W := commSub ⊤ L ⊓ fixV L
  let e3 : ↥(StatedSL 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  let e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K := e2.trans e3
  have hcenter : Subgroup.center ↥L = ⊥ := by
    have h : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
      CFSG.RankThree.PartOne.center_SL2_eq_bot'
    rw [← Subgroup.map_center_eq e] at h
    exact (Subgroup.map_eq_bot_iff_of_injective
      (f := (e : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K)) _ e.injective).1 h
  have hfaithQ : L ⊓ centSec U Z = ⊥ := s16h_H5_faithful_on_quotient hc hcenter
  have hfaith : L ⊓ centSub U = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hg' : g ∈ L ⊓ centSec U Z := ⟨hg.1, centSub_le_centSec U Z hg.2⟩
    rw [hfaithQ] at hg'
    exact hg'
  have hLU : L ≤ stabSub U := by
    intro g hg
    exact mem_stabSub_commSub (Y := ⊤) (X := L)
      (by rw [mem_stabSub]; intro u; simp) (Subgroup.le_normalizer hg)
  let e1 : ↥L ≃* ↥(autSub L U) := autSubEquivOfFaithful hLU hfaith
  have hLieQuot : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 3 :=
    CFSG.RankThree.PartOne.TCP.lieModel_of_equiv_SL2 (D := ↥L) (F := K) (m := 3)
      (by norm_num) hKcard e
  let iso : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(autSub L U) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans e1
  exact CFSG.Blueprint.LieModel.of_mulEquiv iso hLieQuot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
