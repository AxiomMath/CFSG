module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExtDescent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExtDual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExtSection
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
import CFSG.Quasithin.Background.SmithB45L2Main
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQSL2RootCommutator
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1.QuotMap
import CFSG.Quasithin.Vol2.Ch11SecOE2D
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.Statement
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem inf_centSec_eq_bot_of_mem_irrSet {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hL : IsSimpleGroup ↥L) {I : Subgroup W} (hI : I ∈ irrSet L) (hLW : L ≤ stabSub I)
    (hLC : L ≤ stabSub (I ⊓ fixV L)) : L ⊓ centSec I (I ⊓ fixV L) = ⊥ := by
  refine CFSG.LocalAnalysis.RankThreeUC.inf_centSec_eq_bot hL hLW hLC ?_
  intro htriv
  have hle : commSub I L ≤ I ⊓ fixV L := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    exact htriv x hx w hw
  have hIZ : I ≤ I ⊓ fixV L := by
    calc I = commSub I L := hI.1.symm
      _ ≤ I ⊓ fixV L := hle
  exact (ne_of_lt hI.2.1) (le_antisymm inf_le_left hIZ)

theorem k14_3Ext_holds : K14_3Ext := by
  intro W _ _ hW L n hL hn I hI hIC
  obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := CFSG.Quasithin.Vol2.Ch11.OE2.exists_sl2_of_lieModel hL
  have : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have : Fintype F := Fintype.ofFinite F
  have hLW : L ≤ stabSub I := SU3H1.le_stabSub_of_stableUnder hI.2.2.1
  have hLC : L ≤ stabSub (I ⊓ fixV L) := SU3H1.le_stabSub_of_stableUnder hI.2.2.2.1
  have hsimple : IsSimpleGroup ↥L := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL
  have hfaith := inf_centSec_eq_bot_of_mem_irrSet hsimple hI hLW hLC
  obtain ⟨Wb, _, _, _, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary
      (V := Sec I (I ⊓ fixV L)) fun v => QuotientGroup.induction_on v fun w => by
        rw [← QuotientGroup.mk_mul, show w * w = 1 from Subtype.ext (by simpa [pow_two] using hW w),
          QuotientGroup.mk_one]
  obtain ⟨c, hc, hnc⟩ := exists_dual_cocycle_section hW hI hIC hLW hLC hfaith φ θ
  set φ' := (B5.secEquiv L hLW hLC hfaith).symm.trans φ
  have hirr : (B45L2.repOf θ φ').IsIrreducible :=
    B45L2.repOf_isIrreducible θ φ' (B5.isIrrSec_autSec hI.2.1 hI.2.2.2.2 hLW hLC)
  have : Module.Finite (ZMod 2) Wb := Module.Finite.of_finite
  have : Fact (B45L2.repOf θ φ').dual.IsIrreducible :=
    ⟨CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ.isIrreducible_dual _ hirr⟩
  have : Finite (Module.Dual (ZMod 2) Wb) := Finite.of_injective _ DFunLike.coe_injective
  have hF' : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  have hnt : ∃ g, (B45L2.repOf θ φ').dual g ≠ 1 := by
    obtain ⟨g, hg⟩ := B45L2.repOf_nontrivial θ φ'
    exact ⟨g⁻¹, CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ.dual_inv_ne_one hg⟩
  have hnat := isNaturalModule_of_dual _ (isNaturalModule_of_cocycle (by omega) hF' _
    hnt hc hnc)
  exact B5.binaryNaturalSL_of_autSec inf_le_left hLW hLC hfaith
    (Thm14_5.binaryNaturalSL_of_isNaturalModule hF θ φ' hnat)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
