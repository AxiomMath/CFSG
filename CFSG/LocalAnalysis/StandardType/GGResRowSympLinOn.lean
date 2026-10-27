module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumOfWeylType
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSympLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResAN2Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3

theorem ggWeylTypeFamilyOn_sympLin
    : GGWeylTypeFamilyOn GGResAN2Label := by
  intro p hp hp2 lab hlab hS
  obtain ⟨htag, hr, hn1, hp3⟩ := hS
  refine ggNbrTableBWeylTypeNonSplitOn_sympLin p hp hp2 lab hlab
    (Or.inr (Or.inl ⟨htag, by omega, hn1, hp3⟩)) ?_
  refine ⟨Or.inl (Or.inr (Or.inr (Or.inr ⟨hn1, hp3⟩))), ?_, ?_, ?_⟩
  · rw [hn1, hp3]
    norm_num
  · rintro ⟨-, h2, -⟩
    omega
  · rintro ⟨h1, -⟩
    rw [htag] at h1
    exact absurd h1 (by decide)

theorem ggTBXDatumResOn_of_sympLin
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTBXDatumResOn (fun p lab => S p lab ∧ ¬ GGResAN2Label p lab)) :
    GGTBXDatumResOn S :=
  ggTBXDatumResOn_of_weylType ggWeylTypeFamilyOn_sympLin hRig hcyc h

theorem ggPZNbrResDatumOn_of_sympLin
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGPZNbrResDatumOn (fun p lab => S p lab ∧ ¬ GGResAN2Label p lab)) :
    GGPZNbrResDatumOn S :=
  ggPZNbrResDatumOn_of_weylType ggWeylTypeFamilyOn_sympLin hRig hcyc h

end CFSG.StandardType

end
