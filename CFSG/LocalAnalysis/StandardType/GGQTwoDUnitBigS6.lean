module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open CFSG.Assembly

theorem qtwoDB44_model
    {N : Type} [Group N] [Finite N] [Group.IsPerfect N] {d : ℕ}
    (hd : 4 ≤ d) (hlab : GGHasLabel ⟨.C, d, 1⟩ (N ⧸ Subgroup.center N)) :
    Subgroup.center N = ⊥ ∧ Nonempty (N ≃* StatedSp d (ZMod 2)) := by
  classical
  have hperf : commutator N = ⊤ := Group.isPerfect_def.mp inferInstance
  have hraw := hlab
  simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeSymplectic] at hraw
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hraw
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by rw [hKcard]; norm_num
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (by rw [hKcard])
  haveI : NeZero d := ⟨by omega⟩
  have hZ : Subgroup.center N = ⊥ :=
    center_eq_bot_of_quot_psp_even (m := d) (f := 1) hperf hKcard le_rfl (by omega)
      (fun h => absurd h (by omega)) e
  refine ⟨hZ, ?_⟩
  letI : Fintype K := Fintype.ofFinite K
  let φ : K ≃+* ZMod 2 :=
    FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK2, ZMod.card])
  have e1 : N ≃* N ⧸ Subgroup.center N :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm))
  exact ⟨((e1.trans e).trans (TableBSymp.spProjEquivSp (K := K) (m := d))).trans
    (CFSG.SeitzReduction.F4Pilot.statedSpCongr φ d)⟩

end CFSG.StandardType.QTwo

end
