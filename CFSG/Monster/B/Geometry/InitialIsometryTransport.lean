module

public import CFSG.Monster.B.Geometry.InitialIsometryF4Init
public import CFSG.Monster.B.Geometry.ResidueAdj

public noncomputable section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.E6.StdF4

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {F : Type*} {Y : ChamberSystem ι F}

theorem exists_isChamberModel_of_bijOn {L : Set ι} {x : C} {ψ : F → C}
    (hψ : Set.BijOn ψ Set.univ (residue cs δ L x))
    (hadj : ∀ a b j, δ (ψ a) (ψ b) = cs.simple j ↔ a ≠ b ∧ Y.adj j a b) :
    ∃ f : residue cs δ L x → F, IsChamberModel cs (resDist cs δ L x) Y f := by
  set e : (Set.univ : Set F) ≃ residue cs δ L x := hψ.equiv ψ
  have he : ∀ a : (Set.univ : Set F), (e a : C) = ψ a := fun _ => rfl
  refine ⟨fun y => (e.symm y : F), ⟨⟨fun y z h => e.symm.injective (Subtype.ext h),
    fun a => ⟨e ⟨a, Set.mem_univ a⟩, by simp⟩⟩, fun y z j => ?_⟩⟩
  have hy : ψ (e.symm y) = y := by rw [← he, Equiv.apply_symm_apply]
  have hz : ψ (e.symm z) = z := by rw [← he, Equiv.apply_symm_apply]
  change δ y z = cs.simple j ↔ y ≠ z ∧ Y.adj j (e.symm y : F) (e.symm z : F)
  rw [← hy, ← hz, hadj]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h h'
    exact h (by rw [h'])
  · intro h h'
    exact h (e.symm.injective (Subtype.ext h'))

theorem bijOn_of_isChamberModel {L : Set ι} {x : C} {f : residue cs δ L x → F}
    (hf : IsChamberModel cs (resDist cs δ L x) Y f) :
    Set.BijOn (fun a => (hf.equiv.symm a : C)) Set.univ (residue cs δ L x) ∧
      ∀ a b j, δ (hf.equiv.symm a) (hf.equiv.symm b) = cs.simple j ↔ a ≠ b ∧ Y.adj j a b := by
  refine ⟨⟨fun a _ => (hf.equiv.symm a).2, fun a _ b _ h => hf.equiv.symm.injective
    (Subtype.ext h), fun y hy => ⟨hf.equiv ⟨y, hy⟩, Set.mem_univ _, by simp⟩⟩, fun a b j => ?_⟩
  have h := hf.2 (hf.equiv.symm a) (hf.equiv.symm b) j
  rw [← hf.equiv_apply, ← hf.equiv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  change resDist cs δ L x (hf.equiv.symm a) (hf.equiv.symm b) = cs.simple j ↔ _
  rw [h, hf.equiv.symm.injective.ne_iff]

theorem bijOn_comp_of_isometry (σ : C ≃ C) (hσ : ∀ a b, δ (σ a) (σ b) = δ a b) {L : Set ι}
    {x : C} {ψ : F → C} (hψ : Set.BijOn ψ Set.univ (residue cs δ L x))
    (hadj : ∀ a b j, δ (ψ a) (ψ b) = cs.simple j ↔ a ≠ b ∧ Y.adj j a b) :
    Set.BijOn (σ ∘ ψ) Set.univ (residue cs δ L (σ x)) ∧
      ∀ a b j, δ ((σ ∘ ψ) a) ((σ ∘ ψ) b) = cs.simple j ↔ a ≠ b ∧ Y.adj j a b := by
  refine ⟨?_, fun a b j => by simp only [Function.comp_apply, hσ, hadj]⟩
  rw [← image_residue_of_isometry (cs := cs) σ hσ L x]
  exact (σ.injective.injOn.bijOn_image).comp hψ

end CFSG.Monster.B.Geometry
