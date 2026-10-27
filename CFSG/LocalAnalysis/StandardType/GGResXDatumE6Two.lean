module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumOfWeylType
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeE6Two

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggWeylTypeFamilyOn_e6Two :
    GGWeylTypeFamilyOn GGNbrNonSplitE6TwoLabel := by
  intro p hp hp2 lab hlab hS
  refine ggNbrTableBWeylTypeNonSplitOn_e6Two p hp hp2 lab hlab hS ?_
  obtain ⟨htag, hn1, rfl⟩ := hS
  refine ⟨Or.inl (Or.inr (Or.inr (Or.inr ⟨hn1, rfl⟩))), ?_, ?_, ?_⟩
  · rw [hn1]
    norm_num
  · rintro ⟨-, h2, -⟩
    omega
  · rintro ⟨h1, -⟩
    rw [htag] at h1
    exact absurd h1 (by decide)

theorem ggTBXDatumResOn_of_e6Two
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTBXDatumResOn (fun p lab => S p lab ∧ ¬ GGNbrNonSplitE6TwoLabel p lab)) :
    GGTBXDatumResOn S :=
  ggTBXDatumResOn_of_weylType ggWeylTypeFamilyOn_e6Two hRig hcyc h

theorem ggPZNbrResDatumOn_of_e6Two
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGPZNbrResDatumOn (fun p lab => S p lab ∧ ¬ GGNbrNonSplitE6TwoLabel p lab)) :
    GGPZNbrResDatumOn S :=
  ggPZNbrResDatumOn_of_weylType ggWeylTypeFamilyOn_e6Two hRig hcyc h


end CFSG.StandardType

end
