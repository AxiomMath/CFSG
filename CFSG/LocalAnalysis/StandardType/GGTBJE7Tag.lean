module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnola
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.LocalAnalysis.StandardType.GGTBJE8Tag
public import Certificates.Certificate13605
public import Certificates.Certificate13721
public import Certificates.Certificate13723
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviCore
public import CFSG.LocalAnalysis.StandardType.GGTBJE7Levi
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviEnnola
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJE7LeviL_holds
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  rcases hpn with hpn | hpn
  · exact ggTBJE7LeviL_of_frame hH (ggE7Split_leviModel_L hRig hH hΛ hL hpn)
  · exact ggTBJE7LeviL_of_frame hH (ggE7Enn_leviModel_L hRig hH hΛ hL hpn)

theorem ggTBJE7LeviK_holds
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  rcases hpn with hpn | hpn
  · exact ggTBJE7LeviK_of_frame hH hJK (ggE7Split_leviModel_K hRig hH hΛ hK hpn)
  · exact ggTBJE7LeviK_of_frame hH hJK (ggE7Enn_leviModel_K hRig hH hΛ hK hpn)

theorem ggTBJE7LeviL_of_labelRigid
    (hRig : GGLabelRigidInput) : GGTBJE7LeviL :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hH _ _ _ _ hΛ hL hpn _ _ _ _ _ => ggTBJE7LeviL_holds hRig hH hΛ hL hpn

theorem ggTBJE7LeviK_of_labelRigid
    (hRig : GGLabelRigidInput) : GGTBJE7LeviK :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hH hJK _ _ _ _ hΛ hK hpn _ _ _ _ _ =>
    ggTBJE7LeviK_holds hRig hH hJK hΛ hK hpn

end CFSG.StandardType

end
