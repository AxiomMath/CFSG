module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_innDiagBig_of_setting (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab)) :
    GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L := by
  obtain ⟨lab', hlab', hhas', R, iR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  have hEq : lab' = lab := hP
  rw [hEq] at hlab' hhas'
  have hrel := ggInnerDiagOn_relabel hRig hS.1.2.2.1.1 hlab' hhas'
  have hn1 : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab'.1
    have h2 : lab.n < 2 := hlab.1
    omega
  refine largeEvenMarking_mono ?_ hrel
  intro lab'' R' _ I' F' θ' hP'
  obtain ⟨hl, hBsN, hind⟩ := hP'
  subst hl
  exact ⟨⟨rfl, hlab⟩, Or.inr (Or.inr (Or.inr ⟨hn1, rfl⟩)), hBsN, hind⟩

end CFSG.StandardType

end
