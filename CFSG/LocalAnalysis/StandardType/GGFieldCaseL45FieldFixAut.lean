module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

section CenterBot

variable {X R : Type*} [Group X] [Group R]

@[expose] def gffIsoOfCenterBot (θ : X ⧸ Subgroup.center X ≃* R) (h : Subgroup.center X = ⊥) :
    X ≃* R :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)).trans θ

theorem gffIsoOfCenterBot_apply (θ : X ⧸ Subgroup.center X ≃* R) (h : Subgroup.center X = ⊥)
    (x : X) : gffIsoOfCenterBot θ h x = θ (x : X ⧸ Subgroup.center X) :=
  rfl

end CenterBot

section Fixed

variable {X Y : Type*} [Group X] [Group Y]

theorem gff_map_fixed (m : X ≃* Y) (ψ : MulAut X) (φ : MulAut Y)
    (h : ∀ x, φ (m x) = m (ψ x)) :
    (ggAutFixedSubgroup ψ).map m.toMonoidHom = ggAutFixedSubgroup φ := by
  ext y
  rw [Subgroup.mem_map, mem_ggAutFixedSubgroup]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ggAutFixedSubgroup] at hx
    change φ (m x) = m x
    rw [h, hx]
  · intro hy
    refine ⟨m.symm y, ?_, m.apply_symm_apply y⟩
    rw [mem_ggAutFixedSubgroup]
    apply m.injective
    rw [← h, m.apply_symm_apply, hy]

theorem gff_fixed_conj (g a : MulAut Y) :
    ggAutFixedSubgroup (g * a * g⁻¹) = (ggAutFixedSubgroup a).map g.toMonoidHom :=
  (gff_map_fixed g a (g * a * g⁻¹) fun x => by simp).symm

theorem gff_nonempty_equiv_fixed {C Z : Type*} [Group C] [Group Z] (m : X ≃* C) (ψ : MulAut X)
    (g σ : MulAut C) (h : ∀ x, (g * σ * g⁻¹) (m x) = m (ψ x))
    (E : Z ≃* ↥(ggAutFixedSubgroup σ)) : Nonempty (↥(ggAutFixedSubgroup ψ) ≃* Z) := by
  have h1 : (ggAutFixedSubgroup ψ).map m.toMonoidHom =
      (ggAutFixedSubgroup σ).map g.toMonoidHom :=
    (gff_map_fixed m ψ _ h).trans (gff_fixed_conj g σ)
  exact ⟨((Subgroup.equivMapOfInjective _ m.toMonoidHom m.injective).trans
    ((MulEquiv.subgroupCongr h1).trans
      (Subgroup.equivMapOfInjective _ g.toMonoidHom g.injective).symm)).trans E.symm⟩

end Fixed

end CFSG.StandardType
