module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsEleven
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

section

variable (S : Setting V V₁ L T) {g : G}
  (hg : Good V₁ L g) (D : HatModelU (uA V V₁))

include S hg

theorem hat_isotropic : ∀ v ∈ D.hat (wA V V₁ ⊓ rconj (wA V V₁) g),
    ∀ w ∈ D.hat (wA V V₁ ⊓ rconj (wA V V₁) g), D.B v w = 0 := by
  intro v hv w hw
  obtain ⟨e, heE, heU, rfl⟩ := (HatU.mem_hat D).mp hv
  obtain ⟨e', he'E, he'U, rfl⟩ := (HatU.mem_hat D).mp hw
  rw [D.B_spec e heU e' he'U]
  have hE : IsElemAbelian 2 (wA V V₁ ⊓ rconj (wA V V₁) g) :=
    (S.eleven_two hg).1
  have hcomm : e * e' = e' * e := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, heE⟩ ⟨e', he'E⟩)
  calc e * e' * e⁻¹ * e'⁻¹ = (e' * e) * e⁻¹ * e'⁻¹ := by rw [hcomm]
    _ = 1 := by group

theorem ten_four_rank {x : G} (hx : x ∈ rconj (centerOf (uA V V₁)) g)
    (hxN : x ∈ Subgroup.normalizer (uA V V₁ : Set G)) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((D.ρ ⟨x, hxN⟩ : D.V ≃ₗ[ZMod 2] D.V).toLinearMap - LinearMap.id)) ≤ 2 := by
  classical
  obtain ⟨z, hzZ, hz1, hall⟩ := S.exists_gen
  obtain ⟨a, haV, haZ⟩ := S.exists_mem_not_mem
  have hcases := S.V_cases hzZ hz1 haV haZ
  have hzV : z ∈ V := S.V₁_le hzZ
  have haU : a ∈ uA V V₁ := le_uA V V₁ haV
  obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uA V V₁, u₀ ∉ wA V V₁ := by
    by_contra hall'
    push Not at hall'
    exact S.not_le_centralizer_V fun u hu => (hall' u hu).2
  set Tm : D.V →ₗ[ZMod 2] D.V :=
    (D.ρ ⟨x, hxN⟩ : D.V ≃ₗ[ZMod 2] D.V).toLinearMap - LinearMap.id with hTm
  have hTmπ : ∀ u ∈ uA V V₁, Tm (D.π u) = D.π (x * u * x⁻¹ * u⁻¹) := by
    intro u hu
    have h1 : x * u * x⁻¹ * u⁻¹ ∈ uA V V₁ :=
      (uA V V₁).mul_mem (HatU.conj_mem hxN hu) ((uA V V₁).inv_mem hu)
    have h2 := D.π_mul _ h1 u hu
    have e : x * u * x⁻¹ * u⁻¹ * u = x * u * x⁻¹ := by group
    rw [e] at h2
    show D.ρ ⟨x, hxN⟩ (D.π u) - D.π u = _
    rw [D.ρ_π _ _ hu, h2]
    abel
  have hπz : D.π z = 0 := (HatU.π_eq_zero_iff D (le_uA V V₁ hzV)).mpr
    (S.V₁_le_centerOf hzZ)
  have hπZV : ∀ y ∈ centerOf (uA V V₁) ⊔ V,
      D.π y ∈ Submodule.span (ZMod 2) {D.π a} := by
    intro y hy
    obtain ⟨c, hc, v, hv, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute
      (A := centerOf (uA V V₁)) (B := V)
      (fun c hc v hv => (Subgroup.mem_centralizer_iff.mp hc.2 v (le_uA V V₁ hv)).symm) hy
    rw [D.π_mul c hc.1 v (le_uA V V₁ hv), (HatU.π_eq_zero_iff D hc.1).mpr hc, zero_add]
    rcases hcases v hv with h1 | h1 | h1 | h1
    · rw [h1, HatU.π_one D]
      exact Submodule.zero_mem _
    · rw [h1, hπz]
      exact Submodule.zero_mem _
    · rw [h1]
      exact Submodule.subset_span (Set.mem_singleton _)
    · rw [h1, D.π_mul z (le_uA V V₁ hzV) a haU, hπz, zero_add]
      exact Submodule.subset_span (Set.mem_singleton _)
  have hTW : ∀ u ∈ wA V V₁, Tm (D.π u) ∈ Submodule.span (ZMod 2) {D.π a} := by
    intro u hu
    rw [hTmπ u (wA_le_uA V V₁ hu)]
    have hcomm : ⁅u, x⁆ ∈ centerOf (uA V V₁) ⊔ V :=
      S.ten_four hg (Subgroup.commutator_mem_commutator hu hx)
    have hinv : x * u * x⁻¹ * u⁻¹ = ⁅u, x⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hinv]
    exact hπZV _ ((centerOf (uA V V₁) ⊔ V).inv_mem hcomm)
  have hrange : LinearMap.range Tm ≤ Submodule.span (ZMod 2) {D.π a, Tm (D.π u₀)} := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    by_cases huW : u ∈ wA V V₁
    · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) (hTW u huW)
    · have hw' : u₀⁻¹ * u ∈ wA V V₁ :=
        (S.mem_wA_or_inv_mul_mem hu₀U hu hu₀W).resolve_left huW
      have hπu : D.π u = D.π u₀ + D.π (u₀⁻¹ * u) := by
        rw [← D.π_mul u₀ hu₀U _ ((uA V V₁).mul_mem ((uA V V₁).inv_mem hu₀U) hu),
          mul_inv_cancel_left]
      rw [hπu, map_add]
      exact Submodule.add_mem _
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        (Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) (hTW _ hw'))
  calc Module.finrank (ZMod 2) (LinearMap.range Tm) ≤
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({D.π a, Tm (D.π u₀)} : Set D.V)) :=
      Submodule.finrank_mono hrange
    _ = Set.finrank (ZMod 2) ({D.π a, Tm (D.π u₀)} : Set D.V) := rfl
    _ ≤ 2 := by
      have h2 := finrank_span_finset_le_card (R := ZMod 2) ({D.π a, Tm (D.π u₀)} : Finset D.V)
      rw [Finset.coe_insert, Finset.coe_singleton] at h2
      exact h2.trans Finset.card_le_two

end

end Setting

end L128A

end CFSG.Quasithin.H13
