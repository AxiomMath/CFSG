module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7W4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open CFSG.Quasithin.F53.Stellmacher.S35.Fin
open scoped commutatorElement

namespace F53.Stellmacher.S35.G7

open CosetGeom F53

variable {G : Type} [Group G] [Finite G]

namespace WM

variable {H M S : Subgroup G} {β : Geo H M} {c : Ch.Chart β} {E K : Subgroup G}
  (b : WBase (stab β) E K (Wb β) c.θ) (hS : Sit H M S)

include hS in
theorem closure_conj_eq_top (hβ : vtype β = false) {l₀ : Geo H M} (hl₀ : l₀ ∈ nbrs β)
    {U : Subgroup b.mod.W} (hU : U = ((Wl l₀).subgroupOf (Wb β)).map b.proj) :
    Subgroup.closure {m : b.mod.W | ∃ σ : Perm (Fin 5), ∃ u ∈ U, m = b.mod.act σ u} = ⊤ := by
  set C := Subgroup.closure {m : b.mod.W | ∃ σ : Perm (Fin 5), ∃ u ∈ U, m = b.mod.act σ u}
    with hC
  have hWb : Wb β ≤ (C.comap b.proj).map (Wb β).subtype := by
    refine (Std.Wb_eq_iSup_Wl hS hβ).le.trans (iSup₂_le fun l hl x hx => ?_)
    obtain ⟨g, hg, rfl⟩ := stab_transitive_on_nbrs hl₀ hl
    have hy := conj_mem_Wl hx
    have hyW : (g : G)⁻¹ * x * (g : G) ∈ Wb β := Wl_le_Wb hS hβ hl₀ hy
    have hxW : x ∈ Wb β := Wl_le_Wb hS hβ hl hx
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    have hconj : (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ ∈ Wb β := by
      have : (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x := by group
      rwa [this]
    have heq : (⟨x, hxW⟩ : ↥(Wb β)) =
        ⟨(g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹, hconj⟩ := by
      apply Subtype.ext
      show x = _
      group
    show b.proj ⟨x, hxW⟩ ∈ C
    rw [heq, ← b.proj_conj ⟨(g : G), hg⟩ ⟨_, hyW⟩ hconj]
    refine Subgroup.subset_closure ⟨c.θ ⟨(g : G), hg⟩, b.proj ⟨_, hyW⟩, ?_, rfl⟩
    rw [hU]
    exact ⟨⟨_, hyW⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [eq_top_iff]
  intro m _
  obtain ⟨w, rfl⟩ := b.proj_surj m
  obtain ⟨w', hw', hww'⟩ := hWb w.2
  have : w' = w := Subtype.ext hww'
  rw [this] at hw'
  exact hw'

end WM


variable {H M S : Subgroup G}

theorem wmoduleExists : WModuleExists H M S := by
  intro hS hI hZ hR h6b β hβ hsec c l₀ hl₀ hS5 E K hnE hVE hEW hEL horth y hy hyQ hV2 hVE2 hE2 hnK
    hVK hKE hKl hKQ
  have hWX : Wb β ≤ stab β := (Std.Wb_le_Qv hS β).trans (Ch.Qv_le_stab' β)
  obtain ⟨b⟩ := WM.exists_wbase hsec hWX hVK hKE hEW hnK hnE horth (S35.C56.quot_five hS hβ)
    c.surj (c.ker_eq_Qv hS hβ) hKQ hy hyQ hV2 hE2
  have hKU : ∀ x : ↥(Wb β), (x : G) ∈ Wl l₀ → (x : G) ∈ E → b.proj x = 1 := fun x h1 h2 =>
    (b.proj_eq_one x).mpr (((hKl l₀ hl₀).2 ▸ (⟨h1, h2⟩ : (x : G) ∈ Wl l₀ ⊓ E) :
      (x : G) ∈ K))
  have hinj : ∀ u ∈ ((Wl l₀).subgroupOf (Wb β)).map b.proj, b.π u = 1 → u = 1 := by
    rintro _ ⟨x, hx, rfl⟩ h
    exact hKU x (Subgroup.mem_subgroupOf.mp hx) ((b.π_proj x).mp h)
  refine ⟨⟨b.mod, b.proj, b.proj_surj, b.proj_eq_one, b.proj_conj, b.faithful, b.t, b.idx_t, b.π,
    b.π_surj, b.π_act, ((Wl l₀).subgroupOf (Wb β)).map b.proj, rfl, ?_, hinj, ?_, ?_⟩⟩
  · intro s hs u hu
    rw [← hS5] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    obtain ⟨x, hx, rfl⟩ := hu
    have hW : (g : G) * (x : G) * (g : G)⁻¹ ∈ Wb β :=
      (Subgroup.mem_normalizer_iff.mp (Std.Wb_normal β g.2) x).mp x.2
    rw [b.proj_conj g x hW]
    have hg' : (g : G) ∈ stab l₀ := (Subgroup.mem_subgroupOf.mp hg).2
    exact ⟨⟨_, hW⟩, Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (Std.Wl_normal l₀ hg') _).mp
        (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
  · rw [← WM.card_map_eq_of_inj b.π _ hinj, Subgroup.map_map]
    have := WM.image_Wl b hS hI h6b hβ hl₀ hS5 hnE hVE hEW hEL
    unfold WM.fm at this
    rw [this]
    exact card_commW_z card_S5Syl ((isCentInv_std_iff zStd).mpr rfl)
  · exact WM.closure_conj_eq_top b hS hβ hl₀ rfl

end F53.Stellmacher.S35.G7

end CFSG.Quasithin
