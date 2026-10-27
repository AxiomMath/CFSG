module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S5Stmt
public import CFSG.Quasithin.MS93.Sec2Gen

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S310

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem stab_le_normalizer_nclStab {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    (X : GoldAmalgam A C B) (δ : Vtx X) (K : Subgroup X.Universal) :
    stab X δ ≤ Subgroup.normalizer (S5.nclStab X δ K : Set X.Universal) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [S5.nclStab, Subgroup.map_iSup]
  refine iSup_le fun y => ?_
  rw [Subgroup.map_map]
  have e : (MulAut.conj g).toMonoidHom.comp (MulAut.conj (y : X.Universal)).toMonoidHom =
      (MulAut.conj ((⟨g, hg⟩ * y : ↥(stab X δ)) : X.Universal)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [e]
  exact le_iSup (fun y : ↥(stab X δ) => K.map (MulAut.conj (y : X.Universal)).toMonoidHom) _

end S310

end CFSG.Quasithin.MS93
