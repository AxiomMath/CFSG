module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_2_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_1

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7

universe v
universe u

@[expose] public def theorem_7_3_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) : Prop :=
  hypothesis_7_1_statement A L H →
    Section1.IsClassFunction χ →
      weightedProjectionEnergy A L H χ ≤
        normalizedSupportEnergy (dadeProjectionSupport A H) χ ∧
          (weightedProjectionEnergy A L H χ =
              normalizedSupportEnergy (dadeProjectionSupport A H) χ ↔
            constantOnDadeFibres A H χ)

/-- Peterfalvi Hypothesis `(7.4)`. -/


private noncomputable def supportTrunc_pf73
    {G : Type u} [Group G]
    (A : Set G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) : Section1.ClassFunction G :=
  by
    classical
    exact fun g => if g ∈ dadeProjectionSupport A H then χ g else 0

private noncomputable def subgroupTrunc_pf73
    {G : Type u} [Group G]
    (A : Set G) (L : Subgroup G)
    (χ : Section1.ClassFunction G) : Section1.ClassFunction L :=
  by
    classical
    exact fun l => if (l : G) ∈ A then χ l else 0

private theorem dadeSupport_conj_mem_iff_pf73
    {G : Type u} [Group G]
    {A : Set G} {H : G → Subgroup G} (x g : G) :
    x * g * x⁻¹ ∈ dadeProjectionSupport A H ↔
      g ∈ dadeProjectionSupport A H := by
  constructor
  · rintro ⟨a, ha, h, hh, y, hy⟩
    refine ⟨a, ha, h, hh, y * x, ?_⟩
    simpa [dadeProjectionSupport, Section2.conjBy, mul_assoc] using hy
  · rintro ⟨a, ha, h, hh, y, hy⟩
    refine ⟨a, ha, h, hh, y * x⁻¹, ?_⟩
    simpa [dadeProjectionSupport, Section2.conjBy, mul_assoc] using hy

private theorem supportTrunc_isClassFunction_pf73
    {G : Type u} [Group G]
    {A : Set G} {H : G → Subgroup G}
    (χ : Section1.ClassFunction G) (hχclass : Section1.IsClassFunction χ) :
    Section1.IsClassFunction (supportTrunc_pf73 A H χ) := by
  intro x g
  have hxiff := dadeSupport_conj_mem_iff_pf73 (A := A) (H := H) x g
  by_cases hg : g ∈ dadeProjectionSupport A H
  · have hxg : x * g * x⁻¹ ∈ dadeProjectionSupport A H := hxiff.2 hg
    simp [supportTrunc_pf73, hxg, hg, hχclass x g]
  · have hxg : x * g * x⁻¹ ∉ dadeProjectionSupport A H := fun hxg => hg (hxiff.1 hxg)
    simp [supportTrunc_pf73, hxg, hg]

private theorem subgroupTrunc_CFon_pf73
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Section2.Hypothesis2 A L H) (χ : Section1.ClassFunction G)
    (hχclass : Section1.IsClassFunction χ) :
    Section2.CFOn L A (subgroupTrunc_pf73 A L χ) := by
  constructor
  · intro x a
    have hxAiff : ((x * a * x⁻¹ : L) : G) ∈ A ↔ (a : G) ∈ A := by
      change Section2.conjBy (x : G) (a : G) ∈ A ↔ (a : G) ∈ A
      exact h.L_le_normalizer x.2 (a : G)
    by_cases ha : (a : G) ∈ A
    · have hxa : ((x * a * x⁻¹ : L) : G) ∈ A := hxAiff.2 ha
      have hxa' : (↑x * ↑a * (↑x)⁻¹ : G) ∈ A := by
        simpa using hxa
      simp [subgroupTrunc_pf73, hxa', ha, hχclass x a]
    · have hxa : ((x * a * x⁻¹ : L) : G) ∉ A := fun hmem => ha (hxAiff.1 hmem)
      have hxa' : (↑x * ↑a * (↑x)⁻¹ : G) ∉ A := by
        simpa using hxa
      simp [subgroupTrunc_pf73, hxa', ha]
  · intro a ha
    simp [subgroupTrunc_pf73, ha]

private theorem mem_dadeProjectionSupport_mul_pf73
    {G : Type u} [Group G]
    {A : Set G} {H : G → Subgroup G}
    {a h : G} (ha : a ∈ A) (hh : h ∈ H a) :
    a * h ∈ dadeProjectionSupport A H := by
  refine ⟨a, ha, h, hh, 1, ?_⟩
  simp [Section2.conjBy]

private theorem mem_dadeProjectionSupport_self_pf73
    {G : Type u} [Group G]
    {A : Set G} {H : G → Subgroup G}
    {a : G} (ha : a ∈ A) :
    a ∈ dadeProjectionSupport A H := by
  simpa using mem_dadeProjectionSupport_mul_pf73 (A := A) (H := H) ha
    ((H a).one_mem)

private theorem dadeProjectionOn_supportTrunc_eq_pf73
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) :
    dadeProjectionOn A L H (supportTrunc_pf73 A H χ) =
      dadeProjectionOn A L H χ := by
  ext a
  by_cases ha : (a : G) ∈ A
  · unfold dadeProjectionOn dadeProjection Section2.dadeAveragingFunction supportTrunc_pf73
    simp only [ha, ↓reduceIte]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _hx
    have hxS : (a : G) * (x : G) ∈ dadeProjectionSupport A H :=
      mem_dadeProjectionSupport_mul_pf73 (A := A) (H := H) ha x.2
    simp [hxS]
  · simp [dadeProjectionOn, ha]

private theorem cfNormSq_eq_inv_card_mul_sum_normSq_pf73
    {G : Type*} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    Section5.cfNormSq φ = (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (φ g) := by
  unfold Section5.cfNormSq Section1.scalarProduct
  have hcast : ((Nat.card G : ℂ)⁻¹) = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  calc
    Complex.re (φ g * star (φ g)) = Complex.re (star (φ g) * φ g) := by
      rw [mul_comm]
    _ = Complex.re ((Complex.normSq (φ g) : ℝ) : ℂ) := by
          congr 1
          simpa using (Complex.normSq_eq_conj_mul_self (z := φ g)).symm
    _ = Complex.normSq (φ g) := by
          simp

private theorem supportTrunc_pf73_eq_normalizedSupportEnergy
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (H : G → Subgroup G) (χ : Section1.ClassFunction G) :
    Section5.cfNormSq (supportTrunc_pf73 A H χ) =
      normalizedSupportEnergy (dadeProjectionSupport A H) χ := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf73, normalizedSupportEnergy, supportEnergy]
  unfold supportTrunc_pf73
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  by_cases hg : g ∈ dadeProjectionSupport A H <;> simp [hg]

private theorem supportTrunc_image_iff_constant_pf73
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Section2.Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (χ : Section1.ClassFunction G) (hχclass : Section1.IsClassFunction χ) :
    (∃ α : Section1.ClassFunction L,
        Section2.CFOn L A α ∧ supportTrunc_pf73 A H χ = Section2.dadeTransform H hAL α) ↔
      constantOnDadeFibres A H χ := by
  constructor
  · rintro ⟨α, hα, hχimage⟩ a h₀ ha hh₀
    have hmem_ah : a * h₀ ∈ dadeProjectionSupport A H :=
      mem_dadeProjectionSupport_mul_pf73 (A := A) (H := H) ha hh₀
    have hmem_a : a ∈ dadeProjectionSupport A H :=
      mem_dadeProjectionSupport_self_pf73 (A := A) (H := H) ha
    have htrans_ah :
        Section2.dadeTransform H hAL α (a * h₀) = α ⟨a, hAL a ha⟩ := by
      exact ((Section2.definition_2_5 A L H h hAL α hα).1)
        (g := a * h₀) (a := a) (h' := h₀) ha hh₀
        ⟨1, by simp [Section2.conjBy]⟩
    have htrans_a :
        Section2.dadeTransform H hAL α a = α ⟨a, hAL a ha⟩ := by
      have hconj : Section2.conjugateIn a (a * 1) := ⟨1, by simp [Section2.conjBy]⟩
      exact ((Section2.definition_2_5 A L H h hAL α hα).1)
        (g := a) (a := a) (h' := 1) ha (H a).one_mem hconj
    calc
      χ (a * h₀) = supportTrunc_pf73 A H χ (a * h₀) := by
        simp [supportTrunc_pf73, hmem_ah]
      _ = Section2.dadeTransform H hAL α (a * h₀) := by
        rw [hχimage]
      _ = α ⟨a, hAL a ha⟩ := htrans_ah
      _ = Section2.dadeTransform H hAL α a := htrans_a.symm
      _ = supportTrunc_pf73 A H χ a := by
        rw [hχimage]
      _ = χ a := by
        simp [supportTrunc_pf73, hmem_a]
  · intro hconst
    let α : Section1.ClassFunction L := subgroupTrunc_pf73 A L χ
    have hα : Section2.CFOn L A α :=
      subgroupTrunc_CFon_pf73 h χ hχclass
    refine ⟨α, hα, ?_⟩
    ext g
    by_cases hg : g ∈ dadeProjectionSupport A H
    · have hgS : g ∈ dadeProjectionSupport A H := hg
      rcases hg with ⟨a, ha, h₀, hh₀, hconj⟩
      have hleft : supportTrunc_pf73 A H χ g = χ g := by
        simp [supportTrunc_pf73, hgS]
      have hright :
          Section2.dadeTransform H hAL α g = α ⟨a, hAL a ha⟩ := by
        exact ((Section2.definition_2_5 A L H h hAL α hα).1)
          (g := g) (a := a) (h' := h₀) ha hh₀ hconj
      have hχga : χ g = χ a := by
        rcases hconj with ⟨x, hx⟩
        have hclass : χ (Section2.conjBy x g) = χ g := by
          simpa [Section2.conjBy] using hχclass x g
        have hgh : χ g = χ (a * h₀) := hclass.symm.trans (congrArg χ hx)
        exact hgh.trans (hconst ha hh₀)
      calc
        supportTrunc_pf73 A H χ g = χ g := hleft
        _ = χ a := hχga
        _ = α ⟨a, hAL a ha⟩ := by
          simp [α, subgroupTrunc_pf73, ha]
        _ = Section2.dadeTransform H hAL α g := hright.symm
    · have hleft : supportTrunc_pf73 A H χ g = 0 := by
        simp [supportTrunc_pf73, hg]
      have hright : Section2.dadeTransform H hAL α g = 0 :=
        (Section2.definition_2_5 A L H h hAL α hα).2 g (by
          simpa [dadeProjectionSupport] using hg)
      rw [hleft, hright]

public theorem theorem_7_3
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) :
    theorem_7_3_statement A L H χ := by
  intro h71 hχclass
  let hAL : ∀ a ∈ A, a ∈ L := fun a ha => h71.subset_L a ha
  let χ₁ : Section1.ClassFunction G := supportTrunc_pf73 A H χ
  have hχ₁class : Section1.IsClassFunction χ₁ :=
    supportTrunc_isClassFunction_pf73 χ hχclass
  have hproj :
      dadeProjectionOn A L H χ₁ = dadeProjectionOn A L H χ := by
    simpa [χ₁] using dadeProjectionOn_supportTrunc_eq_pf73 A L H χ
  have hχ₁norm :
      Section5.cfNormSq χ₁ =
        normalizedSupportEnergy (dadeProjectionSupport A H) χ := by
    simpa [χ₁] using supportTrunc_pf73_eq_normalizedSupportEnergy A H χ
  have h72 := theorem_7_2_b A L H hAL h71 χ₁ hχ₁class
  constructor
  · simpa [weightedProjectionEnergy, hproj, hχ₁norm] using h72.1
  · constructor
    · intro heq
      have heq' :
          Section5.cfNormSq (dadeProjectionOn A L H χ₁) = Section5.cfNormSq χ₁ := by
        simpa [weightedProjectionEnergy, hproj, hχ₁norm] using heq
      exact (supportTrunc_image_iff_constant_pf73 h71 hAL χ hχclass).1 (h72.2.1 heq')
    · intro hconst
      have himage :
          ∃ α : Section1.ClassFunction L,
            Section2.CFOn L A α ∧ χ₁ = Section2.dadeTransform H hAL α := by
        simpa [χ₁] using
          (supportTrunc_image_iff_constant_pf73 h71 hAL χ hχclass).2 hconst
      have heq' :
          Section5.cfNormSq (dadeProjectionOn A L H χ₁) = Section5.cfNormSq χ₁ :=
        h72.2.2 himage
      simpa [weightedProjectionEnergy, hproj, hχ₁norm] using heq'

end CFSG.Section7
