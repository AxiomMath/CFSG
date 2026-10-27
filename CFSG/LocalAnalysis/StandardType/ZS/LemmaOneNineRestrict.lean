module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineHomology
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction

public section

namespace CFSG.StandardType.ZS

section Field

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

theorem isCompl_sup_span_inf_ker {W Y : Submodule K U} (hc : IsCompl W Y) {y : U} (hy : y ∈ Y)
    {φ : Module.Dual K U} (hφ : φ y ≠ 0) :
    IsCompl (W ⊔ Submodule.span K {y}) (Y ⊓ LinearMap.ker φ) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro z hz
    rw [Submodule.mem_bot]
    obtain ⟨hzM, hzN⟩ := Submodule.mem_inf.mp hz
    obtain ⟨hzY, hzker⟩ := Submodule.mem_inf.mp hzN
    obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp hzM
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht
    have hwY : w ∈ Y := by
      have h : w = (w + a • y) - a • y := by abel
      rw [h]
      exact Y.sub_mem hzY (Y.smul_mem a hy)
    have hw0 : w = 0 := by
      have hmem : w ∈ W ⊓ Y := Submodule.mem_inf.mpr ⟨hw, hwY⟩
      rw [hc.inf_eq_bot] at hmem
      simpa using hmem
    have hker : φ (a • y) = 0 := by
      have hz' : φ (w + a • y) = 0 := hzker
      rwa [hw0, zero_add] at hz'
    have ha : a = 0 := by
      have h : a * φ y = 0 := by simpa [map_smul, smul_eq_mul] using hker
      exact (mul_eq_zero.mp h).resolve_right hφ
    rw [hw0, ha, zero_smul, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro u _
    have hu : u ∈ W ⊔ Y := by
      simp [hc.sup_eq_top]
    obtain ⟨w, hw, y', hy', hsum⟩ := Submodule.mem_sup.mp hu
    rw [← hsum]
    let c : K := (φ y)⁻¹ * φ y'
    have hp : y' - c • y ∈ Y ⊓ LinearMap.ker φ := by
      refine Submodule.mem_inf.mpr ⟨Y.sub_mem hy' (Y.smul_mem c hy), ?_⟩
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
      have hcoef : c * φ y = φ y' := by
        simp only [c]
        field_simp
      rw [hcoef, sub_self]
    have hq0 : c • y ∈ Submodule.span K {y} := by
      exact Submodule.smul_mem (Submodule.span K {y}) c
        (Submodule.subset_span (Set.mem_singleton y))
    have hq : c • y ∈ W ⊔ Submodule.span K {y} := Submodule.mem_sup_right hq0
    have hwq : w + c • y ∈ W ⊔ Submodule.span K {y} :=
      Submodule.add_mem _ (Submodule.mem_sup_left hw) hq
    have hdecomp : w + y' = (w + c • y) + (y' - c • y) := by abel
    rw [hdecomp]
    exact Submodule.add_mem_sup hwq hp

theorem IsHomologyWith.restrict {R : Subgroup (U ≃ₗ[K] U)} {M : Submodule K U}
    (hM : ∀ r ∈ R, ∀ m ∈ M, r m ∈ M) {τ : K} {g : R} {c : U} {φ : Module.Dual K U}
    (h : IsHomologyWith τ (g : U ≃ₗ[K] U) c φ) (hc : c ∈ M) :
    IsHomologyWith τ (ZS.restrictHom R M hM g) ⟨c, hc⟩ (φ ∘ₗ M.subtype) := by
  constructor
  · simpa using h.1
  · intro v
    apply Subtype.ext
    simpa [ZS.restrictHom_apply] using h.2 (v : U)

end Field

section PrimeField

variable {p : ℕ} [Fact p.Prime] {U : Type*} [AddCommGroup U] [Module (ZMod p) U]

private theorem isTransvectionLin_of_restrictHom {R : Subgroup (U ≃ₗ[ZMod p] U)}
    {M Y : Submodule (ZMod p) U} (hc : IsCompl M Y)
    (hM : ∀ r ∈ R, ∀ m ∈ M, r m ∈ M) (hY : ∀ r ∈ R, ∀ y ∈ Y, r y = y) {r : R}
    (h : QTwoLin.IsTransvectionLin (ZS.restrictHom R M hM r)) :
    QTwoLin.IsTransvectionLin (r : U ≃ₗ[ZMod p] U) := by
  obtain ⟨u, ψ, hu, hψ, hψu, hgv⟩ := h
  let π := M.projectionOnto Y hc
  let ψ' : Module.Dual (ZMod p) U := ψ.comp π
  refine ⟨(u : U), ψ', ?_, ?_, ?_, ?_⟩
  · intro h0
    exact hu (Subtype.ext h0)
  · intro h0
    apply hψ
    ext m
    have hπm : π (m : U) = m := Submodule.projectionOnto_apply_of_mem_left hc m.2
    have hzero : ψ' (m : U) = 0 := by rw [h0]; rfl
    simpa [ψ', hπm] using hzero
  · have hπu : π (u : U) = u := Submodule.projectionOnto_apply_of_mem_left hc u.2
    simpa [ψ', hπu] using hψu
  · intro v
    have hv : v ∈ M ⊔ Y := by
      simp [hc.sup_eq_top]
    obtain ⟨m, hm, y, hy, hsum⟩ := Submodule.mem_sup.mp hv
    subst v
    have hrm : (r : U ≃ₗ[ZMod p] U) (m : U) =
        (m : U) + ψ ⟨m, hm⟩ • (u : U) := by
      have h' := congrArg (fun z : M => (z : U)) (hgv ⟨m, hm⟩)
      simpa [ZS.restrictHom_apply] using h'
    have hry : (r : U ≃ₗ[ZMod p] U) (y : U) = y := hY r r.2 y hy
    have hπ : π (m + y) = ⟨m, hm⟩ := by
      rw [map_add, Submodule.projectionOnto_apply_of_mem_left hc hm,
        Submodule.projectionOnto_apply_of_mem_right hc hy, add_zero]
    rw [map_add, hrm, hry]
    have hψ' : ψ' (m + y) = ψ ⟨m, hm⟩ := by simp [ψ', hπ]
    rw [hψ']
    abel

theorem transvectionFree_scalarHull_range_restrictHom {H R : Subgroup (U ≃ₗ[ZMod p] U)}
    (htv : QTwoLin.TransvectionFree H) (hRH : R ≤ H) {M Y₃ : Submodule (ZMod p) U}
    (hc : IsCompl M Y₃) (hM : ∀ r ∈ R, ∀ m ∈ M, r m ∈ M) (hY : ∀ r ∈ R, ∀ y ∈ Y₃, r y = y) :
    QTwoLin.TransvectionFree (scalarHull (ZS.restrictHom R M hM).range) := by
  have hfree : QTwoLin.TransvectionFree (ZS.restrictHom R M hM).range := by
    rintro g ⟨r, rfl⟩ htrans
    exact htv (r : U ≃ₗ[ZMod p] U) (hRH r.2)
      (isTransvectionLin_of_restrictHom hc hM hY htrans)
  exact transvectionFree_scalarHull hfree

end PrimeField

end CFSG.StandardType.ZS

end
