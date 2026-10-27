module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FixVQuot.Modules
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FixVQuot.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdFactors
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FixVQuot CFSG.LocalAnalysis.WeakClosure81
open scoped MatrixGroups

theorem isComponentOf_of_isL2_or_isSz {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {n : ℕ} (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hshape : IsL2 ↥L n ∨ IsSz ↥L n) : IsComponentOf L Y := by
  refine ⟨hLY, CFSG.Open.IsSubnormal.step hLY hLn (CFSG.Open.IsSubnormal.refl Y), ?_⟩
  rcases hshape with h2 | hsz
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax.isQuasisimple_of_isL2 h2
  · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hsz
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
        (CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hsz)).1

theorem fixV_ne_fixV_sup_of_irrSet {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L T : Subgroup (MulAut W)} (hO : O2Trivial Y)
    (hB : IsBasicModule Y) (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hcomp : IsComponentOf L Y) (hT : IsSylowIn 2 T Y)
    (hJ : ∀ J ∈ irrSet L, J ⊓ fixV L ≠ ⊥ →
      ∃ S₀ : Subgroup (MulAut W), IsSylowIn 2 S₀ L ∧ BorelMoves L S₀) :
    fixV T ≠ fixV (L ⊔ T) := by
  have hLne : L ≠ ⊥ := CFSG.Quasithin.B15P4.ne_bot_of_isComponentOf hcomp
  by_cases hfix : fixV L = ⊥
  · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.fixV_ne_fixV_sup hW hLne hfix hT.isPGroup
  · have hH : L = ⨆ X ∈ conjSet L Y, X :=
      (iSup_conjSet_eq_self_of_normal hLY hLn).symm
    have hIrrSpan : IrrSpanTrans Y L :=
      (((w4Lem12_5_holds W hW Y hO hB L hLne hLY hLn).2 L hcomp
        (h_facts hcomp hH).1)).1
    have hsumTop : (⨆ I ∈ irrSet L, I) = ⊤ := hIrrSpan.1
    obtain ⟨J, hJ_mem, hJ_ne⟩ :=
      exists_mem_irrSet_inf_fixV_ne_bot hW hsumTop hfix
    obtain ⟨S₀, hS₀, hBM⟩ := hJ J hJ_mem hJ_ne
    have hS : IsSylowIn 2 (T ⊓ L) L := IsSylowIn.inf_normal hT hLY hLn
    have hBM' : BorelMoves L (T ⊓ L) := borelMoves_of_isSylowIn hS₀ hBM hS
    have hLn' : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
    have hTL : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := hT.le.trans hLn'
    have hTS : T ≤ Subgroup.normalizer ((T ⊓ L) : Set (MulAut W)) := by
      refine le_trans (le_inf Subgroup.le_normalizer hTL)
        Subgroup.inf_normalizer_le_normalizer_inf
    exact fixV_ne_fixV_sup_of_borelMoves hW hT.isPGroup hTL hTS hBM'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
