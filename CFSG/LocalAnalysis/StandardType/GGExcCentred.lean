module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGExcGen
public import CFSG.LocalAnalysis.StandardType.GGK0MainBSCentred
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableCentred
public import CFSG.LocalAnalysis.StandardType.GGK1ScExcPair
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKacV2
public import CFSG.LocalAnalysis.StandardType.GGTPNThmULabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggExcCentredRK_holds
    (hB3 : GGK0ExcB3)
    (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : GGExcCentredRK R := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hR hhJ hhX
  obtain ⟨-, hgen⟩ := hR
  obtain ⟨hloc, hflat, hcard, hrank, hnum, hself, honly, hm⟩ := hd.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hK0 : GGK0MainBS GGKacExcQuasi GGKacValid := ggK0MainBS_quasi_of_B3 hB3
  have hS : GGK0Schur GGKacExcQuasi := ggK0Schur_excPair.mono fun _ _ h => h.1
  have hperf : commutator X = ⊤ := by
    have hm0 := hm
    unfold GGTPNMarked at hm0
    exact hm0.1
  have htagX : labX.tag = .E6 ∨ labX.tag = .twE6 ∨ labX.tag = .E7 ∨ labX.tag = .E8 ∨
      labX.tag = .F4 := hgen.1.1.2.2.2
  have hgen' : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      GGKacExcQuasi lab p := by
    intro lab hlab hhas
    have hiso : GGLabelIso lab labX :=
      hrig lab labX (X ⧸ Subgroup.center X) hlab hΛX hhas hhX
    rw [excg_labelIso_eq_of_exc hiso htagX]
    exact hgen
  obtain ⟨lab, hΛlab, -, hgenlab, hXlab, D, hD, hrZ, -, o, hDo, hqs, hndvd, hoΛ, hJo⟩ :=
    exists_ggKacDatum_of_ggK0MainBS hK0 hS hloc hself hk honly hm hgen'
  have hXnot : ¬ GGLabelIso o.lab lab := by
    intro hiso
    exact not_ggHasLabel_of_le_ggAutFixedSubgroup hperf hloc.2.2.1 hloc.2.2.2.1.1 hXlab
      (largeEvenRawDatum_of_ggLabelIso hiso hJo)
  have hne : o.lab ≠ lab := fun h => hXnot (Or.inl h)
  have hrow : GGTablePRow p o.lab lab :=
    (ggTablePRow_of_ggKacValid_centred hΛlab hgenlab.1 hD hrZ hDo hne).2
  exact ⟨o.lab, lab, hoΛ, hΛlab, hrow, hJo, hXlab⟩

end CFSG.StandardType

end
