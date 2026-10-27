module

public import CFSG.Quasithin.Recognition.Kleidman.F204.GeoBase2

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

variable {H M B S : Subgroup G}

@[expose] def ZCentral (δ : Geo H M) : Prop :=
  ∀ T : Subgroup G, IsSylowTwoOf T (stab δ) → Zv δ = quasithinOmegaOneCenter T

@[expose] def ZFaithful (δ : Geo H M) : Prop :=
  ∀ T : Subgroup G, IsSylowTwoOf T (stab δ) → T ⊓ Subgroup.centralizer (Zv δ : Set G) = Qv δ

namespace Amal

variable (hA : Amal H M B S)
include hA

private theorem eq_bot_core {α β : Geo H M} (g : ↥(H ⊔ M))
    (hg0 : g • γ₀ (H ⊔ M) H M = α) (hg1 : g • γ₁ (H ⊔ M) H M = β)
    {U : Subgroup G} (hU : U ≤ stab α ⊓ stab β)
    (hα : ∀ ε ∈ nbrs α, ∀ ε' ∈ nbrs α, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • α = α ∧ x • ε = ε')
    (hβ : ∀ ε ∈ nbrs β, ∀ ε' ∈ nbrs β, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • β = β ∧ x • ε = ε') : U = ⊥ := by
  have h₁ := hA.amalgam.le₁
  have h₂ := hA.amalgam.le₂
  have hadj : (graph (H ⊔ M) H M).Adj α β := by
    rw [← hg0, ← hg1]; exact (smul_adj g).mpr adj_γ₀_γ₁
  set U' : Subgroup G := conjSub (g : G)⁻¹ U with hU'def
  have hU' : U' ≤ H ⊓ M := by
    have e : stab α ⊓ stab β = conjSub (g : G) (H ⊓ M) := by
      rw [conjSub_inf, ← hg0, ← hg1, stab_smul, stab_smul, stab_γ₀ h₁, stab_γ₁ h₂]
    rw [hU'def, conjSub_le_iff, inv_inv, ← e]
    exact hU
  have hnorm : ∀ x : ↥(H ⊔ M), (x : G) ∈ Subgroup.normalizer (U : Set G) →
      ((g⁻¹ * x * g : ↥(H ⊔ M)) : G) ∈ Subgroup.normalizer (U' : Set G) := by
    intro x hx
    rw [hU'def, conjSub_normalizer, mem_conjSub]
    have : ((g : G)⁻¹)⁻¹ * ((g⁻¹ * x * g : ↥(H ⊔ M)) : G) * (g : G)⁻¹ = (x : G) := by
      simp [mul_assoc]
    rw [this]; exact hx
  have hN₁ : ∀ h ∈ H, ∃ n ∈ H ⊓ Subgroup.normalizer (U' : Set G), n⁻¹ * h ∈ M := by
    intro h hh
    set hh' : ↥(H ⊔ M) := ⟨h, h₁ hh⟩ with hhdef
    have hfix : hh' • γ₀ (H ⊔ M) H M = γ₀ (H ⊔ M) H M := smul_γ₀_of_mem h₁ hh
    have hn1 : hh' • γ₁ (H ⊔ M) H M ∈ nbrs (γ₀ (H ⊔ M) H M) := by
      have := (smul_adj hh').mpr (adj_γ₀_γ₁ (G₀ := H ⊔ M) (G₁ := H) (G₂ := M))
      rwa [hfix] at this
    have hn2 : g • (hh' • γ₁ (H ⊔ M) H M) ∈ nbrs α := by
      have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj (γ₀ (H ⊔ M) H M)
        (hh' • γ₁ (H ⊔ M) H M) from hn1)
      rwa [hg0] at this
    obtain ⟨x, hxN, hxα, hxβ⟩ := hα β hadj _ hn2
    refine ⟨((g⁻¹ * x * g : ↥(H ⊔ M)) : G), ⟨?_, hnorm x hxN⟩, ?_⟩
    · have : (g⁻¹ * x * g) • γ₀ (H ⊔ M) H M = γ₀ (H ⊔ M) H M := by
        rw [mul_smul, mul_smul, hg0, hxα, ← hg0, inv_smul_smul]
      have := mem_stab_of_smul_eq this
      rwa [stab_γ₀ h₁] at this
    · have hn : (g⁻¹ * x * g) • γ₁ (H ⊔ M) H M = hh' • γ₁ (H ⊔ M) H M := by
        rw [mul_smul, mul_smul, hg1, hxβ, inv_smul_smul]
      have : ((g⁻¹ * x * g)⁻¹ * hh') • γ₁ (H ⊔ M) H M = γ₁ (H ⊔ M) H M := by
        rw [mul_smul, ← hn, inv_smul_smul]
      have := mem_stab_of_smul_eq this
      rwa [stab_γ₁ h₂] at this
  have hN₂ : ∀ m ∈ M, ∃ n ∈ M ⊓ Subgroup.normalizer (U' : Set G), n⁻¹ * m ∈ H := by
    intro m hm
    set mm' : ↥(H ⊔ M) := ⟨m, h₂ hm⟩ with hmdef
    have hfix : mm' • γ₁ (H ⊔ M) H M = γ₁ (H ⊔ M) H M := smul_γ₁_of_mem h₂ hm
    have hn1 : mm' • γ₀ (H ⊔ M) H M ∈ nbrs (γ₁ (H ⊔ M) H M) := by
      have := (smul_adj mm').mpr (adj_γ₀_γ₁ (G₀ := H ⊔ M) (G₁ := H) (G₂ := M)).symm
      rwa [hfix] at this
    have hn2 : g • (mm' • γ₀ (H ⊔ M) H M) ∈ nbrs β := by
      have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj (γ₁ (H ⊔ M) H M)
        (mm' • γ₀ (H ⊔ M) H M) from hn1)
      rwa [hg1] at this
    obtain ⟨x, hxN, hxβ, hxα⟩ := hβ α hadj.symm _ hn2
    refine ⟨((g⁻¹ * x * g : ↥(H ⊔ M)) : G), ⟨?_, hnorm x hxN⟩, ?_⟩
    · have : (g⁻¹ * x * g) • γ₁ (H ⊔ M) H M = γ₁ (H ⊔ M) H M := by
        rw [mul_smul, mul_smul, hg1, hxβ, ← hg1, inv_smul_smul]
      have := mem_stab_of_smul_eq this
      rwa [stab_γ₁ h₂] at this
    · have hn : (g⁻¹ * x * g) • γ₀ (H ⊔ M) H M = mm' • γ₀ (H ⊔ M) H M := by
        rw [mul_smul, mul_smul, hg0, hxα, inv_smul_smul]
      have : ((g⁻¹ * x * g)⁻¹ * mm') • γ₀ (H ⊔ M) H M = γ₀ (H ⊔ M) H M := by
        rw [mul_smul, ← hn, inv_smul_smul]
      have := mem_stab_of_smul_eq this
      rwa [stab_γ₀ h₁] at this
  have := F112W.eq_bot_of_normalizer_transitive hA.amalgam hU' hN₁ hN₂
  rwa [hU'def, conjSub_eq_bot_iff] at this

theorem eq_bot_of_normalizer_transitive_vertex {α β : Geo H M}
    (hαβ : (graph (H ⊔ M) H M).Adj α β) {U : Subgroup G} (hU : U ≤ stab α ⊓ stab β)
    (hα : ∀ ε ∈ nbrs α, ∀ ε' ∈ nbrs α, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • α = α ∧ x • ε = ε')
    (hβ : ∀ ε ∈ nbrs β, ∀ ε' ∈ nbrs β, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • β = β ∧ x • ε = ε') : U = ⊥ := by
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hαβ
  · exact hA.eq_bot_core g hg0 hg1 hU hα hβ
  · exact hA.eq_bot_core g hg0 hg1 (by rwa [inf_comm]) hβ hα

theorem eq_bot_of_normalizes_both {α β : Geo H M}
    (hαβ : (graph (H ⊔ M) H M).Adj α β) {U : Subgroup G} (hU : U ≤ stab α ⊓ stab β)
    (hα : stab α ≤ Subgroup.normalizer (U : Set G))
    (hβ : stab β ≤ Subgroup.normalizer (U : Set G)) : U = ⊥ := by
  refine hA.eq_bot_of_normalizer_transitive_vertex hαβ hU ?_ ?_
  · intro ε hε ε' hε'
    obtain ⟨x, hx, hxε⟩ := stab_transitive_on_nbrs hε hε'
    exact ⟨x, hα hx, smul_eq_of_mem_stab hx, hxε⟩
  · intro ε hε ε' hε'
    obtain ⟨x, hx, hxε⟩ := stab_transitive_on_nbrs hε hε'
    exact ⟨x, hβ hx, smul_eq_of_mem_stab hx, hxε⟩

theorem Zv_le_Zv_of_ZCentral {δ μ : Geo H M} (h : μ ∈ nbrs δ) (hc : ZCentral δ) :
    Zv δ ≤ Zv μ := by
  obtain ⟨T, hT1, hT2, -⟩ := hA.exists_common_sylow h
  rw [hc T hT1]
  exact (hA.omegaOneCenter_le_Zv hT1 hT2).2.2

theorem not_ZCentral_both {δ μ : Geo H M} (h : μ ∈ nbrs δ) (hδ : ZCentral δ)
    (hμ : ZCentral μ) : False := by
  obtain ⟨T, hT1, hT2, -⟩ := hA.exists_common_sylow h
  have e : Zv δ = Zv μ := by rw [hδ T hT1, hμ T hT2]
  have hU : Zv δ ≤ stab δ ⊓ stab μ :=
    le_inf ((hA.Zv_le_Qv δ).trans (pCoreOf_le 2 _))
      ((hA.Zv_le_Qv δ).trans (hA.Qv_le_stab_of_mem_nbrs h))
  have hb := hA.eq_bot_of_normalizes_both (show (graph (H ⊔ M) H M).Adj δ μ from h) hU
    (hA.stab_le_normalizer_Zv δ) (e ▸ hA.stab_le_normalizer_Zv μ)
  exact hA.Zv_ne_bot δ hb

theorem not_ZCentral_of_bAt {δ : Geo H M} (h : bAt δ = bMin H M) : ¬ ZCentral δ := by
  intro hc
  obtain ⟨μ, hd, hn⟩ := hA.bAt_spec δ
  have hb := hA.bAt_pos δ
  obtain ⟨β, hβ, hdβ⟩ := exists_adj_dist_eq hA.amalgam.gen (α := μ) (δ := δ)
    (d := bAt δ - 1) (by rw [CosetGeom.dist_comm]; omega)
  have hle : Zv δ ≤ Zv β := hA.Zv_le_Zv_of_ZCentral (show β ∈ nbrs δ from hβ) hc
  have hnb : ¬ Zv β ≤ Qv μ := fun hh => hn (hle.trans hh)
  have h3 : bAt β ≤ CosetGeom.dist β μ := Nat.sInf_le ⟨μ, rfl, hnb⟩
  have h4 : bMin H M ≤ bAt β := bMin_le_bAt β
  rw [CosetGeom.dist_comm, hdβ] at h3
  omega

end Amal

end CFSG.Quasithin.Kleidman.F204
