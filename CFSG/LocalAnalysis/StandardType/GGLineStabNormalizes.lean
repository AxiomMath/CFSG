module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.GroupTheory.GL52.SylowTools

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGLineStabNormalizesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ (hx : x ∈ Bs), ∀ φ ∈ ggAutomizer ⊤ Bs,
        φ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) →
        φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs))

theorem ggAutomizer_mem_normalizer_of_zpowers (ha₀ : GGLNoncyclicInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} (hI : GGThmIHyp p B x L)
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hfix : φ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) := by
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hnc := ha₀ G p B x L hI
  have hgx : g * x * g⁻¹ ∈ Subgroup.zpowers x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfix
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 := congrArg Subtype.val hk
    rw [hφg] at h1
    simpa using h1
  have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_sstar' hS hnc
      (CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem hgx)
  have hφi := inv_apply_of_forall hφg
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
    refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgL l).mp hl,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN), fun b => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hψl, hφi]
    group
  · intro hψ
    obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
    have hgL' := Subgroup.inv_mem _ hgL
    have hgN' := Subgroup.inv_mem _ hgN
    refine mem_ggAutomizer_iff.mpr ⟨g⁻¹ * l * g, ?_, ?_, fun b => ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hgL' l).mp hl
    · simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN' hlN) hgN
    · have hψeq : ψ = φ⁻¹ * (φ * ψ * φ⁻¹) * φ := by group
      rw [hψeq, MulAut.mul_apply, MulAut.mul_apply, hφi, hψl, hφg]
      group

theorem ggLineStabNormalizesInput_of_noncyclic (ha₀ : GGLNoncyclicInput) :
    GGLineStabNormalizesInput := by
  intro G _ _ p B Bs x L D J hH hx φ hφ hfix
  exact ggAutomizer_mem_normalizer_of_zpowers ha₀ hH.1.1 hx hφ hfix

end CFSG.StandardType
