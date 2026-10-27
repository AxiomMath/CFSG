module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueWeightRoot
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueRoot
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.OddStandard.SmallF3.Omega.E7RootSet E7WeightRoot

namespace GGFrameModelData

variable {G : Type} [Group G] {Bs : Subgroup G}

@[expose] noncomputable def rootCoordinates (M : GGFrameModelData Bs 7) :
    Additive ↥Bs ≃+ FEVec 7 :=
  M.ψ.trans rootToWeight.symm.toAddEquiv

theorem rootCoordinates_apply (M : GGFrameModelData Bs 7) (b : Additive ↥Bs) :
    M.rootCoordinates b = rootToWeight.symm (M.ψ b) := rfl

theorem rootToWeight_rootCoordinates (M : GGFrameModelData Bs 7) (b : Additive ↥Bs) :
    rootToWeight (M.rootCoordinates b) = M.ψ b := by
  rw [rootCoordinates_apply, rootToWeight.apply_symm_apply]

theorem rootCoordinates_action (M : GGFrameModelData Bs 7) (φ : MulAut ↥Bs) (b : ↥Bs) :
    ggLin (p := 3) M.rootCoordinates φ (M.rootCoordinates (Additive.ofMul b)) =
      M.rootCoordinates (Additive.ofMul (φ b)) :=
  ggLin_apply_ofMul M.rootCoordinates φ b

theorem exists_weyl_rootCoordinates
    (M : GGFrameModelData Bs 7)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS 7))) (φ : ↥M.A) :
    ∃ w : WeylGroup Tag.E7,
      ggLin (p := 3) M.rootCoordinates (φ : MulAut ↥Bs) = rhoLinear w := by
  obtain ⟨w, hw⟩ := E7WeightRoot.exists_weyl_of_mem_closure (hgen φ)
  refine ⟨w, ?_⟩
  apply LinearEquiv.ext
  intro v
  obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, M.rootCoordinates (Additive.ofMul b) = v :=
    ⟨Additive.toMul (M.rootCoordinates.symm v), by simp⟩
  apply rootToWeight.injective
  calc
    rootToWeight (ggLin (p := 3) M.rootCoordinates (φ : MulAut ↥Bs)
        (M.rootCoordinates (Additive.ofMul b)))
        = M.ψ (Additive.ofMul ((φ : MulAut ↥Bs) b)) := by
          rw [rootCoordinates_action, rootToWeight_rootCoordinates]
    _ = (M.ρ φ).mulVec (M.ψ (Additive.ofMul b)) := (M.act φ b).symm
    _ = (M.ρ φ).mulVec (rootToWeight (M.rootCoordinates (Additive.ofMul b))) := by
          rw [rootToWeight_rootCoordinates]
    _ = rootToWeight (rhoLinear w (M.rootCoordinates (Additive.ofMul b))) := hw _

theorem rootCoordinates_mem_rootSet
    (M : GGFrameModelData Bs 7) {z : G}
    (hzBs : z ∈ Bs) (hz : M.IsRoot z) :
    M.rootCoordinates (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) ∈ rootSet := by
  obtain ⟨_, hz1, t, ht, htv⟩ := hz
  have hv : M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) ≠ 0 := by
    intro h
    apply hz1
    have hzero : Additive.ofMul (⟨z, hzBs⟩ : ↥Bs) = 0 := by
      apply M.ψ.injective
      simpa using h
    have hb : (⟨z, hzBs⟩ : ↥Bs) = 1 := by simpa using hzero
    exact congrArg Subtype.val hb
  rw [rootCoordinates_apply]
  exact E7WeightRoot.negative_eigen_mem_rootSet ht hv htv

theorem map_rootCoordinates_eq_weyl
    (M : GGFrameModelData Bs 7)
    (hA : Nat.card M.A = 2903040)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS 7))) :
    M.A.map (ggLin (p := 3) M.rootCoordinates) = rhoLinear.range := by
  have hle : M.A.map (ggLin (p := 3) M.rootCoordinates) ≤ rhoLinear.range := by
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨w, hw⟩ := M.exists_weyl_rootCoordinates hgen ⟨φ, hφ⟩
    exact ⟨w, hw.symm⟩
  have hW : Nat.card (WeylGroup Tag.E7) = 2903040 := by
    have h := Subgroup.card_mul_index evenWeyl
    rw [natCard_evenWeyl, index_evenWeyl] at h
    omega
  have hR : Nat.card rhoLinear.range = 2903040 :=
    (Nat.card_congr (MonoidHom.ofInjective rhoLinear_injective).toEquiv).symm.trans hW
  have : Finite ↥rhoLinear.range := Nat.finite_of_card_ne_zero (by omega)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (ggLin_injective M.rootCoordinates), hA, hR]

theorem weyl_le_full_rootCoordinates
    (M : GGFrameModelData Bs 7)
    (hA : Nat.card M.A = 2903040)
    (hgen : ∀ φ : ↥M.A, M.ρ φ ∈ Submonoid.closure (Set.range (feS 7))) :
    rhoLinear.range ≤ (ggAutomizer (⊤ : Subgroup G) Bs).map
      (ggLin (p := 3) M.rootCoordinates) := by
  rw [← M.map_rootCoordinates_eq_weyl hA hgen]
  apply Subgroup.map_mono
  intro φ hφ
  exact Subgroup.subset_closure (M.induced φ hφ)

end GGFrameModelData

end CFSG.StandardType.FrameRoute

end
