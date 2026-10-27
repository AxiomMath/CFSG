module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u v

variable {G : Type u} [Group G]

theorem sylowSubgroupOf_restrict
    {p : ℕ} {U D A : Subgroup G}
    (hU : theorem4bIsSylowSubgroupOf p U D) (hUA : U ≤ A) :
    theorem4bIsSylowSubgroupOf p (U.subgroupOf A) (D.subgroupOf A) := by
  obtain ⟨PD, hUPD⟩ := hU
  let f : D.subgroupOf A →* D :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun d : D => d.val) hxy
  have hrange : (PD : Subgroup D) ≤ f.range := by
    intro d hd
    have hdU : d.val ∈ U := by
      rw [hUPD]
      exact Subgroup.mem_map_of_mem D.subtype hd
    exact ⟨⟨⟨d.val, hUA hdU⟩, d.property⟩, rfl⟩
  let PE : Sylow p (D.subgroupOf A) := PD.comapOfInjective f hf hrange
  refine ⟨PE, le_antisymm ?_ ?_⟩
  · intro a haU
    change a.val ∈ U at haU
    rw [hUPD] at haU
    obtain ⟨d, hd, hda⟩ := Subgroup.mem_map.mp haU
    let aE : D.subgroupOf A := ⟨a, by
      change a.val ∈ D
      rw [← hda]
      exact d.property⟩
    apply Subgroup.mem_map.mpr
    refine ⟨aE, ?_, rfl⟩
    change f aE ∈ (PD : Subgroup D)
    have heq : f aE = d := Subtype.ext hda.symm
    rwa [heq]
  · intro a haPE
    obtain ⟨aE, haE, rfl⟩ := Subgroup.mem_map.mp haPE
    change aE.val.val ∈ U
    rw [hUPD]
    exact Subgroup.mem_map_of_mem D.subtype
      (show f aE ∈ (PD : Subgroup D) from haE)

theorem restrictedSubgroupStabilizer
    {Ω : Type v} [MulAction G Ω] (A : Subgroup G) (omega : Ω) :
    MulAction.stabilizer A omega = (MulAction.stabilizer G omega).subgroupOf A := by
  ext a
  rfl

def restrictedSubgroupFixedEquiv
    {Ω : Type v} [MulAction G Ω] (A : Subgroup G) (Q : Subgroup A) :
    {omega : Ω // omega ∈ fixedPointsOfSubgroup A Ω Q} ≃
      {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω (Q.map A.subtype)} where
  toFun omega := ⟨omega.val, by
    intro q hq
    obtain ⟨qA, hqA, rfl⟩ := Subgroup.mem_map.mp hq
    exact omega.property qA hqA⟩
  invFun omega := ⟨omega.val, by
    intro q hq
    exact omega.property q.val (Subgroup.mem_map_of_mem A.subtype hq)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
