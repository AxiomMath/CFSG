module

public import CFSG.Monster.B.TwoA.Fischer.CliqueM22Design
public import CFSG.Monster.B.TwoA.Fischer.SplitAffine
public import CFSG.Monster.B.TwoA.Fischer.CliqueM22Group

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem clique_catalog_M22_quotient
    {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] :
    ∃ (η : C ≃ X₀) (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C)
        ≃* CFSG.Blueprint.NativeSporadic.M22),
      (∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
        T.image (fun z => (η z : Fin 24)) ∈ ℬ₀) ∧
      (∀ (f : setStab act lab Y C) (z : C),
        (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z)) ∧
      ∀ σ : Equiv.Perm X₀, σ ∈ P0in.map resHom ↔
        ∃ f : setStab act lab Y C, ∀ z : C, σ (η z) = η (setStabPerm act lab Y C f z) := by
  classical
  have : Finite C := (hS.finite.subset hC.1.1).to_subtype
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨η, hη⟩ := hS.exists_cliqueEta hC
  obtain ⟨θ, hθ, himg⟩ := exists_mulEquiv_M22
    (fun f => permCongr_mem_designAut η hη (hS.setStabPerm_mem_designAut f))
    (hS.maximal_clique_stabilizer_kernel.2.2 C hC).2.1
  refine ⟨η, (QuotientGroup.quotientMulEquivOfEq (ker_setStabPerm C)).symm.trans θ,
    fun T => ?_, fun f z => ?_, himg⟩
  · rw [← hη T, mem_cliqueDesign]
  · rw [hθ f z]
    rfl

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
