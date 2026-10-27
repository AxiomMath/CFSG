module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic

public section

namespace CFSG.StandardType

namespace LayerFacts

open Matrix
open scoped commutatorElement

section Der

variable {G : Type*} [Group G]

@[expose] def ggDer (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | k + 1 => ⁅ggDer H k, ggDer H k⁆

theorem ggDer_zero (H : Subgroup G) : ggDer H 0 = H := rfl

theorem ggDer_succ (H : Subgroup G) (k : ℕ) : ggDer H (k + 1) = ⁅ggDer H k, ggDer H k⁆ := rfl

theorem ggDer_mono {H K : Subgroup G} (h : H ≤ K) (k : ℕ) : ggDer H k ≤ ggDer K k := by
  induction k with
  | zero => exact h
  | succ k ih => exact Subgroup.commutator_mono ih ih

theorem ggDer_succ' (H : Subgroup G) (k : ℕ) : ggDer H (k + 1) = ggDer ⁅H, H⁆ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ggDer_succ, ih, ggDer_succ]

theorem ggDer_of_perfect {X : Subgroup G} (hX : ⁅X, X⁆ = X) (k : ℕ) : ggDer X k = X := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ggDer_succ, ih, hX]

theorem map_ggDer {G' : Type*} [Group G'] (f : G →* G') (H : Subgroup G) (k : ℕ) :
    (ggDer H k).map f = ggDer (H.map f) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ggDer_succ, Subgroup.map_commutator, ih, ggDer_succ]

theorem ggDer_top (k : ℕ) : ggDer (⊤ : Subgroup G) k = derivedSeries G k := by
  induction k with
  | zero => exact (derivedSeries_zero G).symm
  | succ k ih => rw [ggDer_succ, ih, derivedSeries_succ]

end Der

theorem ggCommutatorElement_center_mul {L : Type*} [Group L] {a b z w : L}
    (hz : z ∈ Subgroup.center L) (hw : w ∈ Subgroup.center L) : ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hzc : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  have hwc : ∀ g, w * g = g * w := fun g => (Subgroup.mem_center_iff.mp hw g).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * (w * b) * (z * a)⁻¹ * (w * b)⁻¹
      = z * (a * w * b * a⁻¹) * z⁻¹ * b⁻¹ * w⁻¹ := by group
    _ = a * w * b * a⁻¹ * b⁻¹ * w⁻¹ := by rw [hzc (a * w * b * a⁻¹), mul_inv_cancel_right]
    _ = a * (w * (b * a⁻¹ * b⁻¹)) * w⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hwc (b * a⁻¹ * b⁻¹)]; group

section Lift

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem toGL_conjSL (A : GL (Fin (m + 1)) F) (u : SpecialLinearGroup (Fin (m + 1)) F) :
    SpecialLinearGroup.toGL (InnerDiagA.conjSL A u) = A * SpecialLinearGroup.toGL u * A⁻¹ :=
  Units.ext (by
    rw [SpecialLinearGroup.coe_GL_coe_matrix, InnerDiagA.coe_conjSL, Units.val_mul,
      Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix])

theorem conjSL_eq_iff_commute (A : GL (Fin (m + 1)) F) (u : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL A u = u ↔ A * SpecialLinearGroup.toGL u = SpecialLinearGroup.toGL u * A := by
  rw [← SpecialLinearGroup.toGL_injective.eq_iff, toGL_conjSL, mul_inv_eq_iff_eq_mul]

variable (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G) (E : Subgroup G)

@[expose] def ggCentSL : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
  (Subgroup.centralizer (LinTorus.inducedMatrices ψ E : Set (GL (Fin (m + 1)) F))).comap
    SpecialLinearGroup.toGL

variable {ψ E}

theorem mem_ggCentSL {u : SpecialLinearGroup (Fin (m + 1)) F} :
    u ∈ ggCentSL ψ E ↔ ∀ A ∈ LinTorus.inducedMatrices ψ E, InnerDiagA.conjSL A u = u := by
  simp only [ggCentSL, Subgroup.mem_comap, Subgroup.mem_centralizer_iff, conjSL_eq_iff_commute,
    SetLike.mem_coe]

theorem conjSL_eq_mul_of_mem_centralizer
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {u : SpecialLinearGroup (Fin (m + 1)) F} (hu : ψ u ∈ Subgroup.centralizer (E : Set G))
    {A : GL (Fin (m + 1)) F} (hA : A ∈ LinTorus.inducedMatrices ψ E) :
    ∃ z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F),
      InnerDiagA.conjSL A u = z * u := by
  obtain ⟨e, he, hpair⟩ := LinTorus.mem_inducedMatrices.mp hA
  refine ⟨InnerDiagA.conjSL A u * u⁻¹, hker ?_, by group⟩
  have h1 := LinFusion.mem_ggInducedPairs.mp hpair u
  have h2 : e * ψ u = ψ u * e := Subgroup.mem_centralizer_iff.mp hu e he
  rw [MonoidHom.mem_ker, map_mul, map_inv, ← h1, h2, mul_inv_cancel_right, mul_inv_cancel]

theorem map_ggCentSL_le (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ) :
    (ggCentSL ψ E).map ψ ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) := by
  rintro _ ⟨c, hc, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
  obtain ⟨A, hA⟩ := hEA e he
  have h1 := LinFusion.mem_ggInducedPairs.mp hA c
  rw [mem_ggCentSL.mp hc A (LinTorus.mem_inducedMatrices.mpr ⟨e, he, hA⟩)] at h1
  calc e * ψ c = e * ψ c * e⁻¹ * e := by group
    _ = ψ c * e := by rw [h1]

theorem commutator_le_map_ggCentSL
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    ⁅ψ.range ⊓ Subgroup.centralizer (E : Set G), ψ.range ⊓ Subgroup.centralizer (E : Set G)⁆ ≤
      (ggCentSL ψ E).map ψ := by
  rw [Subgroup.commutator_le]
  rintro x hx y hy
  obtain ⟨⟨u, rfl⟩, hu⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨⟨v, rfl⟩, hv⟩ := Subgroup.mem_inf.mp hy
  refine ⟨⁅u, v⁆, mem_ggCentSL.mpr fun A hA => ?_, map_commutatorElement ψ u v⟩
  obtain ⟨z, hz, hzu⟩ := conjSL_eq_mul_of_mem_centralizer hker hu hA
  obtain ⟨w, hw, hwv⟩ := conjSL_eq_mul_of_mem_centralizer hker hv hA
  rw [map_commutatorElement, hzu, hwv, ggCommutatorElement_center_mul hz hw]

theorem conj_mem_ggCentSL (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {v : SpecialLinearGroup (Fin (m + 1)) F} (hv : ψ v ∈ Subgroup.centralizer (E : Set G))
    {c : SpecialLinearGroup (Fin (m + 1)) F} (hc : c ∈ ggCentSL ψ E) :
    v * c * v⁻¹ ∈ ggCentSL ψ E := by
  refine mem_ggCentSL.mpr fun A hA => ?_
  obtain ⟨z, hz, hzv⟩ := conjSL_eq_mul_of_mem_centralizer hker hv hA
  have hzc : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  rw [map_mul, map_mul, map_inv, hzv, mem_ggCentSL.mp hc A hA]
  calc z * v * c * (z * v)⁻¹ = z * (v * c * v⁻¹) * z⁻¹ := by group
    _ = v * c * v⁻¹ := by rw [hzc, mul_inv_cancel_right]

theorem normal_map_ggCentSL (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    (((ggCentSL ψ E).map ψ).subgroupOf (ψ.range ⊓ Subgroup.centralizer (E : Set G))).Normal := by
  constructor
  intro x hx h
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨c, hc, hcx⟩ := hx
  obtain ⟨⟨v, hv⟩, hvc⟩ := Subgroup.mem_inf.mp h.2
  refine ⟨v * c * v⁻¹, conj_mem_ggCentSL hker (hv ▸ hvc) hc, ?_⟩
  simp only [map_mul, map_inv, hcx, hv, Subgroup.coe_mul, Subgroup.coe_inv]

end Lift

end LayerFacts

end CFSG.StandardType
