module

public import CFSG.LocalAnalysis.StandardType.PhanEChevModel
public import CFSG.LieType.Steinberg.BruhatWeyl
import Mathlib.Tactic.Group

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] (M : ChevModel2 D n H Fld)

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

theorem ChevModel2.conj_prod (ω : List (Fin D.rank)) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (c : Fld) :
    (ω.map n).prod * M.x γ c * ((ω.map n).prod)⁻¹ =
      M.x (weylAction D.isFiniteType ((cs).wordProd ω) γ) c := by
  induction ω with
  | nil =>
    rw [List.map_nil, List.prod_nil, CoxeterSystem.wordProd_nil, map_one, Module.End.one_apply]
    group
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, CoxeterSystem.wordProd_cons, map_mul, Module.End.mul_apply]
    rw [show n i * (ω.map n).prod * M.x γ c * (n i * (ω.map n).prod)⁻¹ =
        n i * ((ω.map n).prod * M.x γ c * ((ω.map n).prod)⁻¹) * (n i)⁻¹ by group,
      ih, M.nm_conj i _ (weylAction_mem_roots D.isFiniteType ((cs).wordProd ω) hγ) c]

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)

theorem ChevModel2.nrep_conj (w : W) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (c : Fld) :
    nrep hct w * M.x γ c * (nrep hct w)⁻¹ = M.x (weylAction D.isFiniteType w γ) c := by
  obtain ⟨ω, hω, rfl⟩ := (cs).exists_isReduced w
  rw [nrep_wordProd hct hω]
  exact M.conj_prod ω hγ c

theorem ChevModel2.nrep_inv_conj (w : W) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (c : Fld) :
    (nrep hct w)⁻¹ * M.x γ c * nrep hct w = M.x (weylAction D.isFiniteType w⁻¹ γ) c := by
  have hγ' : weylAction D.isFiniteType w⁻¹ γ ∈ D.roots :=
    weylAction_mem_roots D.isFiniteType w⁻¹ hγ
  have h := M.nrep_conj hct w hγ' c
  rw [weylAction_apply_inv_apply] at h
  rw [← h]
  group

theorem ChevModel2.torus_conj {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {h : K}
    (hh : h ∈ ⨆ i, H i) : ∃ s : Fld, s ≠ 0 ∧ ∀ c, h * M.x γ c * h⁻¹ = M.x γ (s * c) := by
  refine Subgroup.iSup_induction H (C := fun h => ∃ s : Fld, s ≠ 0 ∧
    ∀ c, h * M.x γ c * h⁻¹ = M.x γ (s * c)) hh ?_ ?_ ?_
  · intro i t ht
    rw [← M.hh_range i] at ht
    obtain ⟨u, rfl⟩ := ht
    exact ⟨((u ^ (∑ j, D.cartan i j * γ j) : Fldˣ) : Fld), Units.ne_zero _,
      fun c => M.hh_conj i u γ hγ c⟩
  · exact ⟨1, one_ne_zero, by intro c; rw [one_mul, inv_one, mul_one, one_mul]⟩
  · rintro h1 h2 ⟨s1, hs1, e1⟩ ⟨s2, hs2, e2⟩
    refine ⟨s1 * s2, mul_ne_zero hs1 hs2, fun c => ?_⟩
    rw [show (h1 * h2) * M.x γ c * (h1 * h2)⁻¹ =
        h1 * (h2 * M.x γ c * h2⁻¹) * h1⁻¹ by group, e2 c, e1 (s2 * c), mul_assoc]

end CFSG.ClassicalInvolution.Phan.PhanE
