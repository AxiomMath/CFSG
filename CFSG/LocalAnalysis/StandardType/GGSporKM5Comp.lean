module

public import CFSG.LocalAnalysis.StandardType.GGSporKProdComp
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM5
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThree
import CFSG.Sporadic.HN
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.Fischer.Classification.Recognition.Basic
import CFSG.Monster.Tri.TriangleStabMaximal
import CFSG.YGroups.Y443.Tri.AssemblyLit
import CFSG.Assembly.OpenBridges
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeB
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeC
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2Census
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Assembly CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.Monster.Generated
open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.HardMathSupport.Dickson.I271

private theorem fiveB_comp_transport {Q Q' : Type} [Group Q] [Finite Q] [Group Q']
    (e : Q ≃* Q') {s : Q}
    (h : ∃ J : Subgroup Q, GLAPComponent 5 (Subgroup.centralizer ({s} : Set Q)) J) :
    ∃ J' : Subgroup Q', GLAPComponent 5 (Subgroup.centralizer ({e s} : Set Q')) J' := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J.map e.toMonoidHom, ?_⟩
  rw [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e s]
  exact glaPComponent_map_equiv Nat.prime_five e hJ

theorem gmat_five_pComponent_of_invertedByTwoA
    {s : Gmat} (hs : orderOf s = 5) (hinv : InvertedByTwoA s) :
    ∃ J : Subgroup Gmat, LargeEvenPComponent 5 (Subgroup.centralizer ({s} : Set Gmat)) J := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  have : Finite MGriess := hE.1.1
  let φ : Gmat ≃* MGriess :=
    (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
  have hs' : orderOf (φ s) = 5 := by rwa [MulEquiv.orderOf_eq]
  have hA : CentFiveA MGriess := TabMFive.centFiveA_MGriess_res
    ⟨TabBFiveCent.tabBFiveACard_holds, TabMFive.not_seven_dvd_card_centralizer_zFive⟩
    TabMFive.co1FiveInputs
  obtain ⟨α, _, _, hαk, i, hi, hsh⟩ :=
    invertedByTwoA_data_twoA hE Nat.prime_five (by norm_num) hs' (hinv.map φ)
  have hi7 : i = 7 := by
    clear hsh
    revert i
    decide
  subst hi7
  obtain ⟨e⟩ : Nonempty (↥(Subgroup.centralizer ({α} : Set MGriess) ⊓
      Subgroup.centralizer ({φ s} : Set MGriess)) ≃* NativeSporadic.HN) := hsh
  set H : Subgroup MGriess := Subgroup.centralizer ({α} : Set MGriess) ⊓
    Subgroup.centralizer ({φ s} : Set MGriess) with hH
  have hcard : Nat.card ↥H = 273030912000000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HN.card_HN
  have hsimple : IsSimpleGroup ↥H :=
    @MulEquiv.isSimpleGroup ↥H _ NativeSporadic.HN Units.instGroup
      CFSG.Sporadic.HN.isSimpleGroup_HN e
  have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let : CommGroup ↥H := { (inferInstance : Group ↥H) with mul_comm := hcon }
    have hpr := IsSimpleGroup.prime_card (α := ↥H)
    rw [hcard] at hpr
    norm_num at hpr
  have hbound := hA (φ s) hs' (hinv.map φ)
  have h1 : ∃ J : Subgroup MGriess,
      GLAPComponent 5 (Subgroup.centralizer ({φ s} : Set MGriess)) J :=
    bmPComponent_of_inverted_prod Nat.prime_five (by norm_num) hs' hαk inf_le_left inf_le_right
      hsimple hnab (by rw [hcard]; norm_num) (by rw [hcard]; exact hbound)
  have h2 := fiveB_comp_transport φ.symm h1
  rw [MulEquiv.symm_apply_apply] at h2
  obtain ⟨J, hJ⟩ := h2
  exact ⟨J, (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 5 _ _).2 hJ⟩

end CFSG.StandardType.SporadicShape
