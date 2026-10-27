module

public import CFSG.Sporadic.SuzRecog.GLevel3
public import CFSG.Sporadic.SuzRecog.ModelGroups

public section

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Sporadic.Co1Patterson CFSG.Sporadic.SuzOddCore

theorem exists_hom_of_gluing
    {V : Type*} {Γ : SimpleGraph V} {T : Set V → Prop} [MulAction ↥suzM V]
    (D : TitsDataBy Γ T ↥suzM (Fin 2))
    (hXv : D.Xv = ModelGroups.Nrho1.subgroupOf suzM)
    (hXe : D.Xe = ModelGroups.pairStab.subgroupOf suzM)
    (hXt0 : D.Xt 0 = (ModelGroups.triStab (ModelGroups.rho2 * Model.rho1)).subgroupOf suzM)
    (hXt1 : D.Xt 1 = (closure {ModelGroups.s1, ModelGroups.s2}).subgroupOf suzM)
    {G : Type*} [Group G] {M : Subgroup G} (σ : ↥M ≃* ↥(invE 1)) (ψ : ↥Model.NR0 →* G)
    (Φ₂ : ↥Model.Crho1 →* G)
    (hC : ∀ x (hx : x ∈ invE 1) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hA : ∀ x (hx : x ∈ invE 1) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G))
    (hB : ∀ x (hxN : x ∈ Model.NR0) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩) :
    ∃ Φ : ↥suzM →* G, ∀ x (hxM : x ∈ suzM) (hx : x ∈ invE 1),
      Φ ⟨x, hxM⟩ = (σ.symm ⟨x, hx⟩ : G) :=
  exists_hom_of_gluing_model D hXv hXe hXt0 hXt1 C1Model.tau0_mem_B0 C1Model.tau0_mul_self
    C1Model.tau0_conj_rho1 ModelGroups.Nrho1_eq_sup ModelGroups.Crho1_eq_sup
    ModelGroups.pairStab_le_NR0 ModelGroups.triStab_rho2_mul_rho1_le_NR0
    ((closure_le _).2 (by
      rintro x (rfl | rfl)
      · exact ModelGroups.s1_mem_invE
      · exact ModelGroups.s2_mem_invE))
    (fun x hx => (ModelGroups.mem_invE_one_iff.1 hx).2) ModelGroups.invE_eq_sup σ ψ Φ₂ hC hA hB

end CFSG.Sporadic.SuzRecog
