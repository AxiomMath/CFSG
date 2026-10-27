
module

public import CFSG.Monster.B.Co2.IrredMainBase

public import CFSG.Monster.B.Co2.Irred
public import CFSG.Monster.B.Co2.Simple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

theorem not_injective_GL
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [FiniteDimensional (ZMod 2) M] (h1 : 1 ≤ Module.finrank (ZMod 2) M)
    (h11 : Module.finrank (ZMod 2) M ≤ 11)
    (f : Kstab v0 →* LinearMap.GeneralLinearGroup (ZMod 2) M) : ¬ Function.Injective f := by
  intro hf
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rw [natCard_Kv, card_GL_of_finrank rfl] at hdvd
  exact not_dvd_card_GL h1 h11 hdvd

theorem isSimpleGroup_Kv :
    IsSimpleGroup (Kstab v0) := by
  have e : Agrp ≃* Kstab v0 := MulEquiv.subgroupCongr Agrp_eq_Kv
  have := isSimpleGroup_Agrp
  exact e.symm.isSimpleGroup

theorem injective_or_trivial
    {H : Type*} [Group H] (f : Kstab v0 →* H) :
    Function.Injective f ∨ ∀ k, f k = 1 := by
  have := isSimpleGroup_Kv
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · left
    exact (MonoidHom.ker_eq_bot_iff f).1 h
  · right
    intro k
    have : k ∈ f.ker := h ▸ Subgroup.mem_top k
    exact this

section Invariant

variable (U : Submodule (ZMod 2) (Wv v0))
  (hU : ∀ (k : Kstab v0) (w : Wv v0), w ∈ U → wAct v0 k w ∈ U)

include hU

theorem eq_bot_of_rhoU_trivial
    (h : ∀ k, rhoU U hU k = 1) : U = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  refine eq_zero_of_fixed w fun i => ?_
  have h1 := congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) U =>
    ((f : Module.End (ZMod 2) U) ⟨w, hw⟩ : Wv v0)) (h (⟨alpha i, alpha_mem_Kv i⟩)⁻¹)
  simpa [rhoU, restrictU_apply] using h1

theorem eq_top_of_rhoQ_trivial
    (h : ∀ k, rhoQ U hU k = 1) : U = ⊤ := by
  refine eq_top_of_commutators U fun k w => ?_
  have h1 := congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) (Wv v0 ⧸ U) =>
    (f : Module.End (ZMod 2) (Wv v0 ⧸ U)) (Submodule.Quotient.mk w)) (h k⁻¹)
  change Submodule.Quotient.mk (wAct v0 k⁻¹⁻¹ w) = Submodule.Quotient.mk w at h1
  rw [inv_inv, Submodule.Quotient.eq] at h1
  exact h1

end Invariant

theorem irreducible_v0
    (U : Submodule (ZMod 2) (Wv v0))
    (hU : ∀ (k : Kstab v0) (w : Wv v0), w ∈ U → wAct v0 k w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hbot, htop⟩ := hne
  have hfin : FiniteDimensional (ZMod 2) (Wv v0) := Module.finite_of_finrank_eq_succ finrank_W
  have hpos : 0 < Module.finrank (ZMod 2) U :=
    Nat.pos_of_ne_zero fun h => hbot (Submodule.finrank_eq_zero.1 h)
  have hlt : Module.finrank (ZMod 2) U < 22 := by
    rw [← finrank_W]
    exact Submodule.finrank_lt htop
  have hsum := U.finrank_quotient_add_finrank
  rw [finrank_W] at hsum
  by_cases hd : Module.finrank (ZMod 2) U ≤ 11
  · rcases injective_or_trivial (rhoU U hU) with h | h
    · exact not_injective_GL hpos hd _ h
    · exact hbot (eq_bot_of_rhoU_trivial U hU h)
  · rcases injective_or_trivial (rhoQ U hU) with h | h
    · exact not_injective_GL (by omega) (by omega) _ h
    · exact htop (eq_top_of_rhoQ_trivial U hU h)

end CFSG.Monster.B.Co2
