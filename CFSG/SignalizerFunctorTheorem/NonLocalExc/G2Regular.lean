module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Regular
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.HallHigman

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge

variable {K : Type} [Field K]

theorem xUnit_mem_rootSpan_single'
    {τ : Tag} (k : Fin τ.rank) (c : K) :
    xUnit τ K k c ∈ rootSpan τ K {(Pi.single k 1 : Fin τ.rank → ℤ)} := by
  rw [← pinnedX_single]
  exact pinnedX_mem_rootSpan (Set.mem_singleton _) c

theorem canonicalRep_conj_mem_rootSpan_singleton'
    {τ : Tag} (w : WeylGroup τ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {x : ModGL τ K} (hx : x ∈ rootSpan τ K {γ}) :
    canonicalRep (coxeterSystem τ) K w * x * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      rootSpan τ K {w • γ} := by
  have h := canonicalRep_conj_mem_rootSpan (w := w) (S := {γ}) (by rintro _ rfl; exact hγ) hx
  rwa [Set.image_singleton] at h

@[expose] def g2e0 : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def g2e1 : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem g2_fin_cases (i : Fin Tag.G2.rank) : i = g2e0 ∨ i = g2e1 := by
  rcases i with ⟨v, hv⟩
  have : v < 2 := hv
  interval_cases v <;> simp [g2e0, g2e1]

theorem hasCoord_zero_of_mem_unipComplement
    {τ : Tag} {i : Fin τ.rank}
    {y : ModGL τ K} (hy : y ∈ unipComplement τ K i) : HasCoord i y 0 :=
  ⟨y, hy, by rw [xUnit_zero, one_mul]⟩

theorem hasCoord_zero_of_mem_rootSpan_singleton
    {τ : Tag} {i : Fin τ.rank}
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpos : 0 < height γ)
    (hne : γ ≠ Pi.single i 1) {y : ModGL τ K} (hy : y ∈ rootSpan τ K {γ}) : HasCoord i y 0 := by
  have hle : rootSpan τ K {γ} ≤ unipComplement τ K i :=
    biSup_mono (Set.singleton_subset_iff.2 ⟨hγ, hpos, hne⟩)
  exact hasCoord_zero_of_mem_unipComplement (hle hy)

theorem mem_posUnipotent_of_mem_rootSpan_singleton
    {τ : Tag} {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hpos : 0 < height γ) {y : ModGL τ K} (hy : y ∈ rootSpan τ K {γ}) :
    y ∈ posUnipotent τ K :=
  rootSpan_le_posUnipotent
    (fun β hβ => by rw [Set.mem_singleton_iff] at hβ; subst hβ; exact ⟨hγ, hpos⟩) hy

theorem g2_reflect_facts :
    (0 < height (reflect .G2 g2e0 (Pi.single g2e1 1)) ∧
      reflect .G2 g2e0 (Pi.single g2e1 1) ≠ Pi.single g2e0 1 ∧
      reflect .G2 g2e0 (Pi.single g2e1 1) ≠ Pi.single g2e1 1) ∧
    (0 < height (reflect .G2 g2e1 (Pi.single g2e0 1)) ∧
      reflect .G2 g2e1 (Pi.single g2e0 1) ≠ Pi.single g2e0 1 ∧
      reflect .G2 g2e1 (Pi.single g2e0 1) ≠ Pi.single g2e1 1) := by
  decide +kernel

theorem exists_regular_mem_commutator
    [Finite K] (σ : K ≃+* K) :
    ∃ u : ModGL .G2 K, u ∈ ⁅fixedFieldImage .G2 σ, fixedFieldImage .G2 σ⁆ ∧
      IsRegularUnipotent u := by
  classical
  obtain ⟨⟨hp0, hne00, hne01⟩, ⟨hp1, hne10, hne11⟩⟩ := g2_reflect_facts
  have hX1 : xUnit .G2 K g2e1 1 ∈ fixedFieldImage .G2 σ :=
    xUnit_mem_fixedFieldImage g2e1 (map_one σ)
  have hX0 : xUnit .G2 K g2e0 1 ∈ fixedFieldImage .G2 σ :=
    xUnit_mem_fixedFieldImage g2e0 (map_one σ)
  have hN0 : canonicalRep (coxeterSystem .G2) K (simple .G2 g2e0) ∈ fixedFieldImage .G2 σ :=
    canonicalRep_mem_fixedFieldImage _
  have hN1 : canonicalRep (coxeterSystem .G2) K (simple .G2 g2e1) ∈ fixedFieldImage .G2 σ :=
    canonicalRep_mem_fixedFieldImage _
  refine ⟨⁅xUnit .G2 K g2e1 1, canonicalRep (coxeterSystem .G2) K (simple .G2 g2e0)⁆ *
      ⁅xUnit .G2 K g2e0 1, canonicalRep (coxeterSystem .G2) K (simple .G2 g2e1)⁆,
    mul_mem (Subgroup.commutator_mem_commutator hX1 hN0)
      (Subgroup.commutator_mem_commutator hX0 hN1), ?_⟩
  set n0 := canonicalRep (coxeterSystem .G2) K (simple .G2 g2e0) with hn0
  set n1 := canonicalRep (coxeterSystem .G2) K (simple .G2 g2e1) with hn1
  have hy0 : n0 * (xUnit .G2 K g2e1 1)⁻¹ * n0⁻¹ ∈
      rootSpan .G2 K {reflect .G2 g2e0 (Pi.single g2e1 1)} := by
    have := canonicalRep_conj_mem_rootSpan_singleton' (K := K) (simple .G2 g2e0)
      (isRoot_single .G2 g2e1) (inv_mem (xUnit_mem_rootSpan_single' g2e1 (1 : K)))
    rwa [simple_smul] at this
  have hy1 : n1 * (xUnit .G2 K g2e0 1)⁻¹ * n1⁻¹ ∈
      rootSpan .G2 K {reflect .G2 g2e1 (Pi.single g2e0 1)} := by
    have := canonicalRep_conj_mem_rootSpan_singleton' (K := K) (simple .G2 g2e1)
      (isRoot_single .G2 g2e0) (inv_mem (xUnit_mem_rootSpan_single' g2e0 (1 : K)))
    rwa [simple_smul] at this
  have hr0 : IsRoot .G2 (reflect .G2 g2e0 (Pi.single g2e1 1)) :=
    IsRoot.reflect g2e0 (isRoot_single _ g2e1)
  have hr1 : IsRoot .G2 (reflect .G2 g2e1 (Pi.single g2e0 1)) :=
    IsRoot.reflect g2e1 (isRoot_single _ g2e0)
  set y0 := n0 * (xUnit .G2 K g2e1 1)⁻¹ * n0⁻¹ with hy0def
  set y1 := n1 * (xUnit .G2 K g2e0 1)⁻¹ * n1⁻¹ with hy1def
  have hu : ⁅xUnit .G2 K g2e1 1, n0⁆ * ⁅xUnit .G2 K g2e0 1, n1⁆ =
      (xUnit .G2 K g2e1 1 * y0) * (xUnit .G2 K g2e0 1 * y1) := by
    simp only [commutatorElement_def, hy0def, hy1def]
    group
  rw [hu]
  have hU1 : xUnit .G2 K g2e1 1 ∈ posUnipotent .G2 K := xUnit_mem_posUnipotent g2e1 1
  have hU0 : xUnit .G2 K g2e0 1 ∈ posUnipotent .G2 K := xUnit_mem_posUnipotent g2e0 1
  have hUy0 : y0 ∈ posUnipotent .G2 K := mem_posUnipotent_of_mem_rootSpan_singleton hr0 hp0 hy0
  have hUy1 : y1 ∈ posUnipotent .G2 K := mem_posUnipotent_of_mem_rootSpan_singleton hr1 hp1 hy1
  refine ⟨mul_mem (mul_mem hU1 hUy0) (mul_mem hU0 hUy1), fun i => ⟨1, one_ne_zero, ?_⟩⟩
  have key : ∀ (a b c d : K) (i : Fin Tag.G2.rank),
      HasCoord i (xUnit .G2 K g2e1 1) a → HasCoord i y0 b → HasCoord i (xUnit .G2 K g2e0 1) c →
        HasCoord i y1 d → HasCoord i ((xUnit .G2 K g2e1 1 * y0) * (xUnit .G2 K g2e0 1 * y1))
          (a + b + (c + d)) :=
    fun a b c d i h1 h2 h3 h4 => (h1.mul h2).mul (h3.mul h4)
  have hne0 : (Pi.single g2e1 1 : Fin Tag.G2.rank → ℤ) ≠ Pi.single g2e0 1 := by decide +kernel
  have hne1 : (Pi.single g2e0 1 : Fin Tag.G2.rank → ℤ) ≠ Pi.single g2e1 1 := by decide +kernel
  rcases g2_fin_cases i with rfl | rfl
  · have h1 : HasCoord g2e0 (xUnit .G2 K g2e1 1) 0 :=
      hasCoord_zero_of_mem_rootSpan_singleton (isRoot_single .G2 g2e1)
        (by rw [height_single]; exact one_pos) hne0 (xUnit_mem_rootSpan_single' g2e1 1)
    have h2 : HasCoord g2e0 y0 0 := hasCoord_zero_of_mem_rootSpan_singleton hr0 hp0 hne00 hy0
    have h3 : HasCoord g2e0 (xUnit .G2 K g2e0 1) 1 := hasCoord_xUnit g2e0 1
    have h4 : HasCoord g2e0 y1 0 := hasCoord_zero_of_mem_rootSpan_singleton hr1 hp1 hne10 hy1
    have := key 0 0 1 0 g2e0 h1 h2 h3 h4
    simpa using this
  · have h1 : HasCoord g2e1 (xUnit .G2 K g2e1 1) 1 := hasCoord_xUnit g2e1 1
    have h2 : HasCoord g2e1 y0 0 := hasCoord_zero_of_mem_rootSpan_singleton hr0 hp0 hne01 hy0
    have h3 : HasCoord g2e1 (xUnit .G2 K g2e0 1) 0 :=
      hasCoord_zero_of_mem_rootSpan_singleton (isRoot_single .G2 g2e0)
        (by rw [height_single]; exact one_pos) hne1 (xUnit_mem_rootSpan_single' g2e0 1)
    have h4 : HasCoord g2e1 y1 0 := hasCoord_zero_of_mem_rootSpan_singleton hr1 hp1 hne11 hy1
    have := key 1 0 0 0 g2e1 h1 h2 h3 h4
    simpa using this

end CFSG.SignalizerFunctorTheorem.NonLocalExc
