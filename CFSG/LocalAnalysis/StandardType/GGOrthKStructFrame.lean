module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_frame {G : Type} [Group G] [Finite G] {B Bs K : Subgroup G}
    (hB : GGBstar 3 B Bs) (hinn : GGInnerDiagOn Bs K) {n : ℕ} (hn : 7 ≤ n)
    (e : ↥K ≃* ↥(CFSG.Open.StatedSL (n + 1) (ZMod 2))) :
    ∃ ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G, GGHalfTorusFrame Bs K (halfTorus n) ψ := by
  have hnorm : Bs ≤ Subgroup.normalizer (K : Set G) := GGInnerDiagOn.le_normalizer hinn
  let e' : ↥K ≃* SpecialLinearGroup (Fin (n + 1)) F2 :=
    e.trans <| (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (n + 1)
        (ZMod 2)).symm.trans (CFSG.RankThree.PartTwo.Sec4.RonanK429F.slGF2Equiv (n + 1)).symm
  let phi : SpecialLinearGroup (Fin (n + 1)) F2 →* G := K.subtype.comp e'.symm.toMonoidHom
  have hphi_range : phi.range = K := by
    change (K.subtype.comp e'.symm.toMonoidHom).range = K
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e'.symm.surjective,
      ← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype K
  have hphi_inj : Function.Injective phi := by
    intro a b hab
    exact e'.symm.injective (Subtype.ext hab)
  obtain ⟨A, hframe⟩ := ggHalf_torusFrame (p := 3) (N := n) rfl hB (by omega) hnorm phi
    hphi_range hphi_inj
  exact ⟨phi.comp (MulAut.conj A).toMonoidHom, hframe⟩

end CFSG.StandardType

end
