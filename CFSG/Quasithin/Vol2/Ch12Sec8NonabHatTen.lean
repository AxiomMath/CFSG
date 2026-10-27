module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatAct
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEleven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace HatModel

omit [Finite G] in
theorem lemma_12_8_8_two_symplectic (D : HatModel T M) :
    (∀ v : D.V, D.B v v = 0) ∧ (∀ v w : D.V, D.B v w = D.B w v) ∧
      (∀ v : D.V, (∀ w, D.B v w = 0) → v = 0) ∧
      ∀ (x : Subgroup.normalizer (uOfL22 T M : Set G)) (v w : D.V),
        D.B (D.rho x v) (D.rho x w) = D.B v w :=
  ⟨D.B_isAlt, D.B_symm, D.B_nondegenerate, D.B_rho⟩

end HatModel

namespace Hyp1281Two

section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g) (D : HatModel T M)

include h hU hg

theorem hat_isotropic : ∀ v ∈ D.hat (wOfU T M ⊓ rconj (wOfU T M) g),
    ∀ w ∈ D.hat (wOfU T M ⊓ rconj (wOfU T M) g), D.B v w = 0 := by
  intro v hv w hw
  obtain ⟨e, heE, heU, rfl⟩ := D.mem_hat.mp hv
  obtain ⟨e', he'E, he'U, rfl⟩ := D.mem_hat.mp hw
  rw [D.B_spec e heU e' he'U]
  have hE : IsElemAbelian 2 (wOfU T M ⊓ rconj (wOfU T M) g) :=
    (h.lemma_12_8_11_two hU hg).1
  have hcomm : e * e' = e' * e := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, heE⟩ ⟨e', he'E⟩)
  calc e * e' * e⁻¹ * e'⁻¹ = (e' * e) * e⁻¹ * e'⁻¹ := by rw [hcomm]
    _ = 1 := by group

theorem lemma_12_8_10_four_rank {x : G} (hx : x ∈ rconj (centerOf (uOfL22 T M)) g)
    (hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((D.rho ⟨x, hxN⟩ : D.V ≃ₗ[ZMod 2] D.V).toLinearMap - LinearMap.id)) ≤ 2 := by
  classical
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  have hcases := h.VZ_cases hzZ hz1 haV haZ
  have hzV : z ∈ VZ T M := omegaOneCenter_le_VZ T M hzZ
  have haU : a ∈ uOfL22 T M := VZ_le_uOfL22 T M haV
  obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uOfL22 T M, u₀ ∉ wOfU T M := by
    by_contra hall'
    push Not at hall'
    exact h.not_le_centralizer_VZ_of_nonabelian hU fun u hu => (hall' u hu).2
  set Tm : D.V →ₗ[ZMod 2] D.V :=
    (D.rho ⟨x, hxN⟩ : D.V ≃ₗ[ZMod 2] D.V).toLinearMap - LinearMap.id with hTm
  have hTmπ : ∀ u ∈ uOfL22 T M, Tm (D.π u) = D.π (x * u * x⁻¹ * u⁻¹) := by
    intro u hu
    have h1 : x * u * x⁻¹ * u⁻¹ ∈ uOfL22 T M :=
      (uOfL22 T M).mul_mem (HatModel.conj_mem_uOfL22 hxN hu) ((uOfL22 T M).inv_mem hu)
    have h2 := D.π_mul _ h1 u hu
    have e : x * u * x⁻¹ * u⁻¹ * u = x * u * x⁻¹ := by group
    rw [e] at h2
    show D.rho ⟨x, hxN⟩ (D.π u) - D.π u = _
    rw [D.rho_π _ hu, h2]
    abel
  have hπz : D.π z = 0 := (D.π_eq_zero_iff (VZ_le_uOfL22 T M hzV)).mpr
    (h.omegaOneCenter_le_centerOf_uOfL22 hzZ)
  have hπZV : ∀ y ∈ centerOf (uOfL22 T M) ⊔ VZ T M,
      D.π y ∈ Submodule.span (ZMod 2) {D.π a} := by
    intro y hy
    obtain ⟨c, hc, v, hv, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute
      (A := centerOf (uOfL22 T M)) (B := VZ T M)
      (fun c hc v hv => (Subgroup.mem_centralizer_iff.mp hc.2 v (VZ_le_uOfL22 T M hv)).symm) hy
    rw [D.π_mul c hc.1 v (VZ_le_uOfL22 T M hv), (D.π_eq_zero_iff hc.1).mpr hc, zero_add]
    rcases hcases v hv with h1 | h1 | h1 | h1
    · rw [h1, D.π_one]
      exact Submodule.zero_mem _
    · rw [h1, hπz]
      exact Submodule.zero_mem _
    · rw [h1]
      exact Submodule.subset_span (Set.mem_singleton _)
    · rw [h1, D.π_mul z (VZ_le_uOfL22 T M hzV) a haU, hπz, zero_add]
      exact Submodule.subset_span (Set.mem_singleton _)
  have hTW : ∀ u ∈ wOfU T M, Tm (D.π u) ∈ Submodule.span (ZMod 2) {D.π a} := by
    intro u hu
    rw [hTmπ u (wOfU_le_uOfL22 T M hu)]
    have hcomm : ⁅u, x⁆ ∈ centerOf (uOfL22 T M) ⊔ VZ T M :=
      h.lemma_12_8_10_four hU hg (Subgroup.commutator_mem_commutator hu hx)
    have hinv : x * u * x⁻¹ * u⁻¹ = ⁅u, x⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hinv]
    exact hπZV _ ((centerOf (uOfL22 T M) ⊔ VZ T M).inv_mem hcomm)
  have hrange : LinearMap.range Tm ≤ Submodule.span (ZMod 2) {D.π a, Tm (D.π u₀)} := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    by_cases huW : u ∈ wOfU T M
    · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) (hTW u huW)
    · have hw' : u₀⁻¹ * u ∈ wOfU T M :=
        (h.mem_wOfU_or_inv_mul_mem hu₀U hu hu₀W).resolve_left huW
      have hπu : D.π u = D.π u₀ + D.π (u₀⁻¹ * u) := by
        rw [← D.π_mul u₀ hu₀U _ ((uOfL22 T M).mul_mem ((uOfL22 T M).inv_mem hu₀U) hu),
          mul_inv_cancel_left]
      rw [hπu, map_add]
      exact Submodule.add_mem _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
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

end Hyp1281Two

end CFSG.Quasithin
