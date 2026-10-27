module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusLinSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusLinIrred
import CFSG.LocalAnalysis.StandardType.GGNSJoinLinTwoAux
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem nsLinTwo_component_label (hRig : GGLabelRigidInput) {N : ℕ} (hN : 6 ≤ N) {F : Type}
    [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2) {g : GL (Fin N) F} (hg : g ^ 3 = 1)
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F))}
    (hJ₀ : CFSG.Open.IsComponentOf J₀ (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)))
    {labJ : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ)
    (hhas : GGHasLabel labJ (↥J₀ ⧸ Subgroup.center ↥J₀)) : labJ.n ≤ 2 := by
  let e := TypeA.recipeEquiv N F
  let T : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N F) :=
    J₀.map e.toMonoidHom
  have hσ : MulAut.congr e (TableB.linConjAut (Fin N) F g) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut N F g :=
    q1CentLin_congr_linConjAut g
  have hgrp : (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)).map e.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut N F g) := by
    rw [nsLT2_map_ggAutFixedSubgroup e (TableB.linConjAut (Fin N) F g), hσ]
  have hJ₀asm : CFSG.Assembly.IsComponentOf J₀
      (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hJ₀
  have hmap := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
    hJ₀asm e.toMonoidHom e.injective
  have hT : CFSG.Open.IsComponentOf T
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut N F g)) := by
    rw [← hgrp]
    exact CFSG.Assembly.isComponentOf_iff_open.mp hmap
  obtain ⟨m, j, hm, hj, hhasT, hΛT⟩ :=
    nsLT2_component_label_of_order_three hF hg hT
  let eJ : ↥J₀ ≃* ↥T := Subgroup.equivMapOfInjective J₀ e.toMonoidHom e.injective
  have hcenter : (Subgroup.center ↥J₀).map eJ.toMonoidHom = Subgroup.center ↥T :=
    Subgroup.map_center_eq eJ
  let eQ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* (↥T ⧸ Subgroup.center ↥T) :=
    QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥T) eJ hcenter
  have hhasJ : GGHasLabel ⟨.A, m - 1, j⟩ (↥J₀ ⧸ Subgroup.center ↥J₀) :=
    ggHasLabel_of_mulEquiv eQ.symm hhasT
  have hIso := hRig labJ ⟨.A, m - 1, j⟩ (↥J₀ ⧸ Subgroup.center ↥J₀) hΛ hΛT hhas hhasJ
  exact nsLT2_iso_n_le hj hIso

end CFSG.StandardType

end
