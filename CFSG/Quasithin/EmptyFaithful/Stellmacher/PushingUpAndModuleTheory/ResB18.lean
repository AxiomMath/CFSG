module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB17
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB14

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem Psi_not_P (h : ConfR δ μ U) (fr : OrthFrame δ μ) {s : G} (hsδ : s ∈ stab δ)
    (hs : s ∈ stab μ) (hsP : s ∉ Qv μ) :
    fr.Ψ ⟨s, hsδ⟩ ∈ S5Syl ∧ fr.Ψ ⟨s, hsδ⟩ ∉ S5That := by
  refine ⟨?_, fun hh => hsP ((h.frame_mem_P_iff fr ⟨s, hsδ⟩).mpr hh)⟩
  rw [← fr.syl]
  exact ⟨⟨s, hsδ⟩, Subgroup.mem_subgroupOf.mpr ⟨hsδ, hs⟩, rfl⟩

theorem Oo_eq_sup (h : ConfR δ μ U) (fr : OrthFrame δ μ) {cb : Perm (Fin 5)} (hc : IsThreeCyc cb)
    {V₀ : Subgroup G} (hV : V₀ = (planeOf cb).map fr.γ) {s : G} (hsδ : s ∈ stab δ)
    (hs : s ∈ stab μ) (hsP : s ∉ Qv μ) : V₀ ⊔ conjSub s V₀ = OoOf δ := by
  obtain ⟨hS, hT⟩ := h.Psi_not_P fr hsδ hs hsP
  have h1 := (planeOf_sup_conj hc hS hT).1
  have h2 : conjSub s V₀ = (actSub (fr.Ψ ⟨s, hsδ⟩) (planeOf cb)).map fr.γ := by
    rw [hV]; exact fr.conj_map ⟨s, hsδ⟩ _
  rw [h2, hV, ← Subgroup.map_sup, h1, fr.map_top]

theorem comm_P_eq (fr : OrthFrame δ μ) {cb : Perm (Fin 5)}
    {V₀ : Subgroup G} (hV : V₀ = (planeOf cb).map fr.γ) (hP : Qv μ ≤ stab δ) :
    ⁅Qv μ, V₀⁆ = (commW orth S5That (planeOf cb)).map fr.γ := by
  rw [hV, fr.comm_map _ hP, ← fr.mapP]
  rfl

theorem card_comm_P (fr : OrthFrame δ μ) {cb : Perm (Fin 5)} (hc : IsThreeCyc cb)
    {V₀ : Subgroup G} (hV : V₀ = (planeOf cb).map fr.γ) (hP : Qv μ ≤ stab δ) :
    Nat.card (⁅Qv μ, V₀⁆ : Subgroup G) = 2 := by
  rw [comm_P_eq fr hV hP, Subgroup.card_map_of_injective fr.inj, card_commW_planeOf hc]

theorem conj_comm_P_ne (h : ConfR δ μ U) (fr : OrthFrame δ μ) {cb : Perm (Fin 5)}
    (hc : IsThreeCyc cb) {V₀ : Subgroup G} (hV : V₀ = (planeOf cb).map fr.γ)
    (hP : Qv μ ≤ stab δ) {s : G} (hsδ : s ∈ stab δ) (hs : s ∈ stab μ) (hsP : s ∉ Qv μ) :
    conjSub s (⁅Qv μ, V₀⁆) ≠ ⁅Qv μ, V₀⁆ := by
  obtain ⟨hS, hT⟩ := h.Psi_not_P fr hsδ hs hsP
  rw [comm_P_eq fr hV hP, fr.conj_map ⟨s, hsδ⟩]
  intro e
  exact commW_planeOf_not_invariant hc hS hT (Subgroup.map_injective fr.inj e)

theorem centralizes_V0 (h : ConfR δ μ U) (fr : OrthFrame δ μ) {cb : Perm (Fin 5)}
    (hc : IsThreeCyc cb) {V₀ : Subgroup G} (hV : V₀ = (planeOf cb).map fr.γ)
    (k : ↥(stab δ)) (hk : (k : G) ∈ Qv μ) (hcen : ∀ v ∈ V₀, (k : G) * v = v * (k : G)) :
    fr.Ψ k ∈ Subgroup.zpowers (swap 0 2) ∨ fr.Ψ k ∈ Subgroup.zpowers (swap 1 3) := by
  refine fix_planeOf hc ((h.frame_mem_P_iff fr k).mp hk) fun w hw => ?_
  apply fr.inj
  have h1 := fr.equiv k w
  have h2 := hcen (fr.γ w) (by rw [hV]; exact ⟨w, hw, rfl⟩)
  rw [h1]
  calc (k : G) * fr.γ w * (k : G)⁻¹ = fr.γ w * (k : G) * (k : G)⁻¹ := by rw [h2]
    _ = fr.γ w := by group

theorem V0_le_ZU (h : ConfR δ μ U) (fr : OrthFrame δ μ) {c : G} (hcU : c ∈ U)
    (hc : IsThreeCyc (fr.Ψ ⟨c, h.sig.le_stab hcU⟩)) {V₀ : Subgroup G}
    (hV : V₀ = (planeOf (fr.Ψ ⟨c, h.sig.le_stab hcU⟩)).map fr.γ) (hA : F53Amalgam H M S) :
    V₀ ≤ CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U := by
  have hcX : c ∈ stab δ := h.sig.le_stab hcU
  have hPF : Qv μ ≤ stab δ := by
    have := h.sig.P_le_edge hA
    rw [h.inf_eq] at this
    exact this.trans inf_le_left
  set A0 : Subgroup G := (fixW orth S5That).map fr.γ with hA0
  have hA0Z : A0 ≤ quasithinOmegaOneCenter (Qv μ ⊓ U) := by
    rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h.inf_eq]
      exact h.Oo_le_Qv_mu hA (fr.mem w)
    · rw [h.inf_eq]
      refine Subgroup.mem_centralizer_iff.mpr fun p hp => ?_
      have hΨ := (h.frame_mem_P_iff fr ⟨p, hPF hp⟩).mp hp
      have := fr.equiv ⟨p, hPF hp⟩ w
      rw [hw _ hΨ] at this
      calc p * fr.γ w = (p * fr.γ w * p⁻¹) * p := by group
        _ = fr.γ w * p := by rw [← this]
    · rw [pow_two, ← map_mul, orth.sq w, map_one]
  have hZ : A0 ≤ CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U :=
    hA0Z.trans (CFSG.Quasithin.le_conjClosure _ _)
  have hcN : c ∈ Subgroup.normalizer
      ((CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U : Subgroup G) : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure _ _ hcU
  have hZc : conjSub c A0 ≤ CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U := by
    intro x hx
    have hx' : c⁻¹ * x * c ∈ A0 := mem_conjSub.mp hx
    have := (Subgroup.mem_normalizer_iff.mp hcN (c⁻¹ * x * c)).mp (hZ hx')
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e] at this
  have hsub : V₀ ≤ A0 ⊔ conjSub c A0 := by
    rw [hV, hA0, fr.conj_map ⟨c, hcX⟩, ← Subgroup.map_sup]
    exact Subgroup.map_mono (planeOf_le_fixW hc)
  exact hsub.trans (sup_le hZ hZc)

end ConfR

end CFSG.Quasithin.F53
