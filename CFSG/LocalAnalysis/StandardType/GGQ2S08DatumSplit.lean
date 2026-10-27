module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open Module

theorem ggQ2s08d_full_split {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hF : M.ShapeFull) :
    M.xV ≠ 0 ∧ IsCompl M.coSpan (Submodule.span (ZMod 3) {M.xV}) ∧
      Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 ∧
      (∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model), ∀ h ∈ M.coSpan, w h ∈ M.coSpan) ∧
      (∀ v, (∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model), w v = v) ↔
        v ∈ Submodule.span (ZMod 3) {M.xV}) := by
  obtain ⟨_hxL, hindep, hxVnot, hsup⟩ := hF
  have hxV_ne : M.xV ≠ 0 := by
    intro h0
    exact hxVnot (by rw [h0]; exact M.coSpan.zero_mem)
  have hα : ∀ i, M.root i (M.coroot i) = (2 : ZMod 3) := by
    intro i
    rw [M.pairing i i, M.isCartan.1 i]
    norm_num
  have hlin : ∀ i, ggLin (p := 3) M.model (M.simple i) = reflection (hα i) := fun i =>
    ggLin_eq_reflection M.model (hα i) (M.simple_apply i)
  have hgen_inv : ∀ i, (ggLin (p := 3) M.model (M.simple i))⁻¹ =
      ggLin (p := 3) M.model (M.simple i) := by
    intro i
    have h2 : ggLin (p := 3) M.model (M.simple i) * ggLin (p := 3) M.model (M.simple i) = 1 := by
      rw [hlin i]
      ext v
      simp [LinearEquiv.mul_apply, involutive_reflection (hα i) v]
    rw [← mul_one (ggLin (p := 3) M.model (M.simple i))⁻¹, ← h2, ← mul_assoc, inv_mul_cancel,
      one_mul]
  have hP : ∀ φ ∈ ggAutomizer L Bs, ∀ h ∈ M.coSpan,
      ggLin (p := 3) M.model φ h ∈ M.coSpan ∧
        ggLin (p := 3) M.model (φ⁻¹) h ∈ M.coSpan := by
    intro φ hφ
    rw [M.automizer_L] at hφ
    refine Subgroup.closure_induction (p := fun ψ _ => ∀ h ∈ M.coSpan,
      ggLin (p := 3) M.model ψ h ∈ M.coSpan ∧
        ggLin (p := 3) M.model (ψ⁻¹) h ∈ M.coSpan) ?_ ?_ ?_ ?_ hφ
    · rintro ψ ⟨i, rfl⟩ h hh
      have hmem : ggLin (p := 3) M.model (M.simple i) h ∈ M.coSpan := by
        rw [M.simple_apply i h]
        exact M.coSpan.sub_mem hh
          (M.coSpan.smul_mem _ (Submodule.subset_span (Set.mem_range_self i)))
      exact ⟨hmem, by rw [map_inv, hgen_inv i]; exact hmem⟩
    · intro h hh
      simpa [map_one, inv_one] using And.intro hh hh
    · intro a b _ _ ha hb h hh
      obtain ⟨hah, hah'⟩ := ha h hh
      obtain ⟨hbh, _hbh'⟩ := hb h hh
      refine ⟨?_, ?_⟩
      · have h1 : ggLin (p := 3) M.model (a * b) h =
            ggLin (p := 3) M.model a (ggLin (p := 3) M.model b h) := by
          rw [map_mul, LinearEquiv.mul_apply]
        rw [h1]
        exact (ha _ hbh).1
      · have h2 : ggLin (p := 3) M.model ((a * b)⁻¹) h =
            ggLin (p := 3) M.model (b⁻¹) (ggLin (p := 3) M.model (a⁻¹) h) := by
          rw [mul_inv_rev, map_mul, LinearEquiv.mul_apply]
        rw [h2]
        exact (hb _ hah').2
    · intro a _ ha h hh
      exact ⟨(ha h hh).2, by rw [inv_inv]; exact (ha h hh).1⟩
  have hWpres : ∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model), ∀ h ∈ M.coSpan,
      w h ∈ M.coSpan := by
    intro w hw h hh
    obtain ⟨φ, hφ, hφw⟩ := Subgroup.mem_map.mp hw
    rw [← hφw]
    exact (hP φ hφ h hh).1
  have hdisj : Disjoint M.coSpan (Submodule.span (ZMod 3) {M.xV}) :=
    Submodule.disjoint_span_singleton_of_notMem hxVnot
  have hcompl : IsCompl M.coSpan (Submodule.span (ZMod 3) {M.xV}) :=
    ⟨hdisj, codisjoint_iff.mpr hsup⟩
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
  have hfinrank : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 := by
    have hcs : Module.finrank (ZMod 3) M.coSpan = Fintype.card M.Λ := by
      rw [GGQ2LDatum.coSpan]
      exact finrank_span_eq_card hindep
    have hx1 : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {M.xV}) = 1 :=
      finrank_span_singleton hxV_ne
    have hinf : M.coSpan ⊓ Submodule.span (ZMod 3) {M.xV} = ⊥ := disjoint_iff.mp hdisj
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq M.coSpan
      (Submodule.span (ZMod 3) {M.xV})
    rw [hinf, finrank_bot, add_zero] at hsum
    rw [← finrank_top, ← hsup, hsum, hcs, hx1]
  have hfix : ∀ v, (∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model), w v = v) ↔
      v ∈ Submodule.span (ZMod 3) {M.xV} := by
    have hfix_eq : ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) =
        Submodule.span (ZMod 3) {M.xV} := M.fixed_x
    intro v
    rw [← hfix_eq]
    constructor
    · intro hv
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      exact hv (ggLin (p := 3) M.model φ) (Subgroup.mem_map_of_mem _ hφ)
    · intro hv
      rw [mem_ggFixedSubmodule_iff] at hv
      intro w hw
      obtain ⟨φ, hφ, hφw⟩ := Subgroup.mem_map.mp hw
      rw [← hφw]
      exact hv φ hφ
  exact ⟨hxV_ne, hcompl, hfinrank, hWpres, hfix⟩

end CFSG.StandardType

end
