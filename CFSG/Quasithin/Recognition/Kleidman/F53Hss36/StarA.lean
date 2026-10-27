module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaI

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher CFSG.Quasithin.F53Push
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem star_normal {δ l : Geo H M} (hl : l ∈ nbrs δ)
    (hQL : ⁅Qv δ, oTwoRes (stab δ)⁆ ≤ Qv l) :
    ∀ g ∈ stab δ, ∀ n ∈ Qv δ ⊓ Qv l, g * n * g⁻¹ ∈ Qv δ ⊓ Qv l := by
  have hQN : ∀ g ∈ stab δ, g ∈ Subgroup.normalizer (Qv δ : Set G) := fun g hg =>
    le_normalizer_pCoreOf 2 (stab δ) hg
  have hlN : ∀ g ∈ stab l, g ∈ Subgroup.normalizer (Qv l : Set G) := fun g hg =>
    le_normalizer_pCoreOf 2 (stab l) hg
  have hL : ∀ x ∈ oTwoRes (stab δ), ∀ n ∈ Qv δ ⊓ Qv l, x * n * x⁻¹ ∈ Qv δ ⊓ Qv l := by
    intro x hx n hn
    have hxs : x ∈ stab δ := oTwoRes_le _ hx
    have hc : ⁅x, n⁆ ∈ Qv l := by
      have h := Subgroup.commutator_mem_commutator hx hn.1
      rw [Subgroup.commutator_comm] at h
      exact hQL h
    have hxn : x * n * x⁻¹ ∈ Qv δ := (Subgroup.mem_normalizer_iff.mp (hQN x hxs) n).mp hn.1
    have e : x * n * x⁻¹ = ⁅x, n⁆ * n := by simp only [commutatorElement_def]; group
    refine ⟨hxn, ?_⟩
    rw [e]
    exact (Qv l).mul_mem hc hn.2
  have hB : ∀ h ∈ stab δ ⊓ stab l, ∀ n ∈ Qv δ ⊓ Qv l, h * n * h⁻¹ ∈ Qv δ ⊓ Qv l := by
    intro h hh n hn
    have := mem_normalizer_inf' (hQN h hh.1) (hlN h hh.2)
    exact (Subgroup.mem_normalizer_iff.mp this n).mp hn
  intro g hg n hn
  set g' : ↥(H ⊔ M) := ⟨g, stab_le δ hg⟩ with hg'
  obtain ⟨x, hxL, hxl⟩ := C.exists_oTwoRes_smul hl (smul_mem_nbrs_stab (g := g') hg hl)
  have hxs : (x : G) ∈ stab δ := oTwoRes_le _ hxL
  have hfix : (x⁻¹ * g') • l = l := by rw [mul_smul, ← hxl, inv_smul_smul]
  have hy1 : (x : G)⁻¹ * g ∈ stab l := by
    have := mem_stab_of_smul_eq hfix
    simpa [hg'] using this
  have hy2 : (x : G)⁻¹ * g ∈ stab δ := (stab δ).mul_mem ((stab δ).inv_mem hxs) hg
  have h1 := hB _ ⟨hy2, hy1⟩ n hn
  have h2 := hL _ hxL _ h1
  have e : g * n * g⁻¹ = (x : G) * (((x : G)⁻¹ * g) * n * ((x : G)⁻¹ * g)⁻¹) * (x : G)⁻¹ := by
    group
  rw [e]
  exact h2

theorem star_inf_eq {δ l : Geo H M} (hl : l ∈ nbrs δ)
    (hQL : ⁅Qv δ, oTwoRes (stab δ)⁆ ≤ Qv l) {μ : Geo H M} (hμ : μ ∈ nbrs δ) :
    Qv δ ⊓ Qv μ = Qv δ ⊓ Qv l := by
  have hnorm := C.star_normal hl hQL
  obtain ⟨g, hgst, hgl⟩ := stab_transitive_on_nbrs hl hμ
  have hQμ : ∀ x : G, x ∈ Qv μ ↔ (g : G)⁻¹ * x * (g : G) ∈ Qv l := fun x => by
    rw [← hgl, Qv_smul, mem_conjSub]
  have hQN : (g : G) ∈ Subgroup.normalizer (Qv δ : Set G) :=
    le_normalizer_pCoreOf 2 (stab δ) hgst
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    have hxg : (g : G)⁻¹ * x * (g : G) ∈ Qv δ ⊓ Qv l := by
      refine ⟨?_, (hQμ x).mp hx2⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hQN) x).mp hx1
      simpa using this
    have := hnorm _ hgst _ hxg
    simpa [mul_assoc] using this
  · rintro hx
    refine ⟨hx.1, (hQμ x).mpr ?_⟩
    have := hnorm _ ((stab δ).inv_mem hgst) _ hx
    simpa using this.2

theorem star_centralizes {δ l : Geo H M} (hδ : vtype δ = false) (hl : l ∈ nbrs δ)
    (hQL : ⁅Qv δ, oTwoRes (stab δ)⁆ ≤ Qv l) :
    ∀ n ∈ Qv δ ⊓ Qv l, ∀ v ∈ Vn δ, n * v = v * n := by
  intro n hn
  have hall : Vn δ ≤ Subgroup.centralizer ({n} : Set G) := by
    refine iSup₂_le fun μ hμ z hz => ?_
    have hnμ : n ∈ Qv μ := by
      have : n ∈ Qv δ ⊓ Qv μ := by rw [C.star_inf_eq hl hQL hμ]; exact hn
      exact this.2
    have hvμ := vtype_true_of_mem_nbrs_false hμ hδ
    have h1 := C.Qv_centralizes_Zv hvμ hnμ hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  intro v hv
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hall hv)).symm

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
