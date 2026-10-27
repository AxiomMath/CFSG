module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.RankThree.Classical

open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups

section Field

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

@[expose] def IsTransvectionWith (t : V ≃ₗ[F] V) (v : V) (f : Module.Dual F V) : Prop :=
  v ≠ 0 ∧ f ≠ 0 ∧ f v = 0 ∧ ∀ x, t x = x + f x • v

theorem IsTransvectionWith.inv_apply {t : V ≃ₗ[F] V} {v : V} {f : Module.Dual F V}
    (ht : IsTransvectionWith t v f) (x : V) : t⁻¹ x = x - f x • v := by
  change t.symm x = _
  rw [LinearEquiv.symm_apply_eq, ht.2.2.2, map_sub, map_smul, ht.2.2.1, smul_eq_mul, mul_zero,
    sub_zero]
  abel

theorem IsTransvectionWith.pow_apply {t : V ≃ₗ[F] V} {v : V} {f : Module.Dual F V}
    (ht : IsTransvectionWith t v f) (n : ℕ) (x : V) : (t ^ n) x = x + ((n : F) * f x) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, ht.2.2.2, map_add, map_smul, ht.2.2.1, smul_eq_mul,
      mul_zero, add_zero]
    push_cast
    module

theorem commutatorElement_apply_of_transvection {t₁ t₂ : V ≃ₗ[F] V} {v w : V}
    {f g : Module.Dual F V} (h₁ : IsTransvectionWith t₁ v f) (h₂ : IsTransvectionWith t₂ w g)
    (hgv : g v = 0) (x : V) : ⁅t₁, t₂⁆ x = x + (f w * g x) • v := by
  rw [commutatorElement_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    h₂.inv_apply, h₁.inv_apply, h₂.2.2.2, h₁.2.2.2]
  simp only [map_sub, map_smul, map_add, h₁.2.2.1, h₂.2.2.1, hgv, smul_eq_mul, mul_zero,
    sub_zero]
  module

theorem isTransvectionWith_commutatorElement {t₁ t₂ : V ≃ₗ[F] V} {v w : V}
    {f g : Module.Dual F V} (h₁ : IsTransvectionWith t₁ v f) (h₂ : IsTransvectionWith t₂ w g)
    (hgv : g v = 0) (hfw : f w ≠ 0) : IsTransvectionWith ⁅t₁, t₂⁆ v (f w • g) :=
  ⟨h₁.1, smul_ne_zero hfw h₂.2.1, by rw [LinearMap.smul_apply, hgv, smul_zero], fun x => by
    rw [commutatorElement_apply_of_transvection h₁ h₂ hgv, LinearMap.smul_apply, smul_eq_mul]⟩

theorem exists_mem_apply_center_ne_zero {H : Subgroup (V ≃ₗ[F] V)}
    (hirr : ∀ W : Submodule F V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    {S : Set (V ≃ₗ[F] V)} (hSne : S.Nonempty)
    (hS : ∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) (hHS : H = Subgroup.closure S)
    {e : Module.Dual F V} (he : e ≠ 0) :
    ∃ t ∈ S, ∃ v f, IsTransvectionWith t v f ∧ e v ≠ 0 := by
  by_contra hall
  push Not at hall
  let W := Submodule.span F {x | ∃ t ∈ S, ∃ f, IsTransvectionWith t x f}
  have hinv : ∀ h ∈ H, ∀ x ∈ W, h x ∈ W := by
    intro h hh
    rw [hHS] at hh
    refine Subgroup.closure_induction'' (p := fun h _ => ∀ x ∈ W, h x ∈ W) ?_ ?_ ?_ ?_ hh
    · intro t ht x hx
      obtain ⟨v, f, hvf⟩ := hS t ht
      rw [hvf.2.2.2]
      exact W.add_mem hx (W.smul_mem _ (Submodule.subset_span ⟨t, ht, f, hvf⟩))
    · intro t ht x hx
      obtain ⟨v, f, hvf⟩ := hS t ht
      rw [hvf.inv_apply]
      exact W.sub_mem hx (W.smul_mem _ (Submodule.subset_span ⟨t, ht, f, hvf⟩))
    · intro x hx
      exact hx
    · intro a b _ _ ha hb x hx
      rw [LinearEquiv.mul_apply]
      exact ha _ (hb x hx)
  have hW : W = ⊤ := by
    refine (hirr W hinv).resolve_left fun hbot => ?_
    obtain ⟨t, ht⟩ := hSne
    obtain ⟨v, f, hvf⟩ := hS t ht
    have hv : v ∈ W := Submodule.subset_span ⟨t, ht, f, hvf⟩
    rw [hbot, Submodule.mem_bot] at hv
    exact hvf.1 hv
  apply he
  have hle : W ≤ LinearMap.ker e := by
    rw [Submodule.span_le]
    rintro x ⟨t, ht, f, hvf⟩
    exact hall t ht x f hvf
  rw [hW, top_le_iff, LinearMap.ker_eq_top] at hle
  exact hle

theorem isCompl_span_pair_ker_inf_ker {v w : V} {f g : Module.Dual F V} (hfv : f v = 0)
    (hgw : g w = 0) (hfw : f w ≠ 0) (hgv : g v ≠ 0) :
    IsCompl (Submodule.span F {v, w}) (LinearMap.ker f ⊓ LinearMap.ker g) := by
  refine ⟨Submodule.disjoint_def.mpr fun x hxU hxL => ?_, codisjoint_iff.mpr ?_⟩
  · obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hxU
    obtain ⟨hf, hg⟩ := Submodule.mem_inf.mp hxL
    rw [LinearMap.mem_ker, map_add, map_smul, map_smul, hfv, smul_eq_mul, smul_eq_mul, mul_zero,
      zero_add] at hf
    rw [LinearMap.mem_ker, map_add, map_smul, map_smul, hgw, smul_eq_mul, smul_eq_mul, mul_zero,
      add_zero] at hg
    rw [(mul_eq_zero.mp hf).resolve_right hfw, (mul_eq_zero.mp hg).resolve_right hgv, zero_smul,
      zero_smul, add_zero]
  · refine eq_top_iff.mpr fun x _ => Submodule.mem_sup.mpr ?_
    refine ⟨(g x / g v) • v + (f x / f w) • w, Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩,
      x - ((g x / g v) • v + (f x / f w) • w), Submodule.mem_inf.mpr ⟨?_, ?_⟩, by abel⟩
    · rw [LinearMap.mem_ker, map_sub, map_add, map_smul, map_smul, hfv, smul_eq_mul, smul_eq_mul,
        mul_zero, zero_add, div_mul_cancel₀ _ hfw, sub_self]
    · rw [LinearMap.mem_ker, map_sub, map_add, map_smul, map_smul, hgw, smul_eq_mul, smul_eq_mul,
        mul_zero, add_zero, div_mul_cancel₀ _ hgv, sub_self]

end Field

section Prime

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem IsTransvectionWith.exists_pow_eq {t : V ≃ₗ[ZMod p] V} {v : V} {f : Module.Dual (ZMod p) V}
    (ht : IsTransvectionWith t v f) (c : ZMod p) :
    ∃ n : ℕ, ∀ x, (t ^ n) x = x + (c * f x) • v :=
  ⟨c.val, fun x => by rw [ht.pow_apply, ZMod.natCast_zmod_val]⟩

noncomputable def pairBasis {v w : V} (hvw : LinearIndependent (ZMod p) ![v, w]) :
    Module.Basis (Fin 2) (ZMod p) (Submodule.span (ZMod p) {v, w}) :=
  Module.Basis.mk (v := ![⟨v, Submodule.subset_span (by simp)⟩,
      ⟨w, Submodule.subset_span (by simp)⟩])
    (LinearIndependent.of_comp (Submodule.span (ZMod p) {v, w}).subtype (by
      convert hvw using 1
      ext i
      fin_cases i <;> rfl))
    (by
      rintro ⟨x, hx⟩ -
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
      have : (⟨a • v + b • w, hx⟩ : Submodule.span (ZMod p) {v, w}) =
          a • (⟨v, Submodule.subset_span (by simp)⟩ : Submodule.span (ZMod p) {v, w}) +
            b • ⟨w, Submodule.subset_span (by simp)⟩ := rfl
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))

theorem coe_pairBasis_zero {v w : V} (hvw : LinearIndependent (ZMod p) ![v, w]) :
    (pairBasis hvw 0 : V) = v := by
  rw [pairBasis, Module.Basis.mk_apply]
  rfl

theorem coe_pairBasis_one {v w : V} (hvw : LinearIndependent (ZMod p) ![v, w]) :
    (pairBasis hvw 1 : V) = w := by
  rw [pairBasis, Module.Basis.mk_apply]
  rfl

theorem toMatrix_restrict_eq {v w : V} (hvw : LinearIndependent (ZMod p) ![v, w])
    (h : V →ₗ[ZMod p] V)
    (hU : ∀ x ∈ Submodule.span (ZMod p) {v, w}, h x ∈ Submodule.span (ZMod p) {v, w})
    (a b c d : ZMod p) (hv : h v = a • v + c • w) (hw : h w = b • v + d • w) :
    LinearMap.toMatrix (pairBasis hvw) (pairBasis hvw) (h.restrict hU) = !![a, b; c, d] := by
  set B := pairBasis hvw
  have h0 : h.restrict hU (B 0) = a • B 0 + c • B 1 := by
    apply Subtype.ext
    change h (B 0 : V) = a • (B 0 : V) + c • (B 1 : V)
    rw [coe_pairBasis_zero, coe_pairBasis_one]
    exact hv
  have h1 : h.restrict hU (B 1) = b • B 0 + d • B 1 := by
    apply Subtype.ext
    change h (B 1 : V) = b • (B 0 : V) + d • (B 1 : V)
    rw [coe_pairBasis_zero, coe_pairBasis_one]
    exact hw
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [h0, h1, Module.Basis.repr_self]

theorem exists_mem_of_det_eq_one {H : Subgroup (V ≃ₗ[ZMod p] V)} {t₁ t₂ : V ≃ₗ[ZMod p] V}
    {v w : V} {f g : Module.Dual (ZMod p) V} (h₁ : IsTransvectionWith t₁ v f)
    (h₂ : IsTransvectionWith t₂ w g) (ht₁ : t₁ ∈ H) (ht₂ : t₂ ∈ H) (hfw : f w ≠ 0)
    (hgv : g v ≠ 0) (φ : Submodule.span (ZMod p) {v, w} →ₗ[ZMod p] Submodule.span (ZMod p) {v, w})
    (hφ : LinearMap.det φ = 1) :
    ∃ h ∈ H, (∀ u : Submodule.span (ZMod p) {v, w}, h (u : V) = (φ u : V)) ∧
      ∀ x ∈ LinearMap.ker f ⊓ LinearMap.ker g, h x = x := by
  have hvw : LinearIndependent (ZMod p) ![v, w] := LinearIndependent.pair_iff.mpr fun s t hst => by
    have hf := congrArg f hst
    rw [map_add, map_smul, map_smul, h₁.2.2.1, smul_eq_mul, smul_eq_mul, mul_zero, zero_add,
      map_zero] at hf
    have ht : t = 0 := (mul_eq_zero.mp hf).resolve_right hfw
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right h₁.1, ht⟩
  set B := pairBasis hvw
  have hvU : v ∈ Submodule.span (ZMod p) {v, w} := Submodule.subset_span (by simp)
  have hwU : w ∈ Submodule.span (ZMod p) {v, w} := Submodule.subset_span (by simp)
  let P : SL(2, ZMod p) → Prop := fun A => ∃ h ∈ H,
    ∃ hU : ∀ x ∈ Submodule.span (ZMod p) {v, w}, h x ∈ Submodule.span (ZMod p) {v, w},
    (∀ x ∈ LinearMap.ker f ⊓ LinearMap.ker g, h x = x) ∧
      LinearMap.toMatrix B B ((h : V →ₗ[ZMod p] V).restrict hU) = (A : Matrix (Fin 2) (Fin 2) _)
  have hupper : ∀ d, P (sl2Upper (ZMod p) d) := by
    intro d
    obtain ⟨n, hn⟩ := h₁.exists_pow_eq (d / f w)
    have hU : ∀ x ∈ Submodule.span (ZMod p) {v, w},
        (t₁ ^ n) x ∈ Submodule.span (ZMod p) {v, w} := fun x hx => by
      rw [hn]
      exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hvU)
    refine ⟨t₁ ^ n, H.pow_mem ht₁ n, hU, fun x hx => ?_, ?_⟩
    · rw [hn, (Submodule.mem_inf.mp hx).1, mul_zero, zero_smul, add_zero]
    · rw [coe_sl2Upper]
      refine toMatrix_restrict_eq hvw _ hU 1 d 0 1 ?_ ?_
      · change (t₁ ^ n) v = _
        rw [hn, h₁.2.2.1, mul_zero, zero_smul, add_zero, one_smul, zero_smul, add_zero]
      · change (t₁ ^ n) w = _
        rw [hn, div_mul_cancel₀ _ hfw, one_smul, add_comm]
  have hlower : ∀ d, P (sl2Lower (ZMod p) d) := by
    intro d
    obtain ⟨n, hn⟩ := h₂.exists_pow_eq (d / g v)
    have hU : ∀ x ∈ Submodule.span (ZMod p) {v, w},
        (t₂ ^ n) x ∈ Submodule.span (ZMod p) {v, w} := fun x hx => by
      rw [hn]
      exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hwU)
    refine ⟨t₂ ^ n, H.pow_mem ht₂ n, hU, fun x hx => ?_, ?_⟩
    · rw [hn, (Submodule.mem_inf.mp hx).2, mul_zero, zero_smul, add_zero]
    · rw [coe_sl2Lower]
      refine toMatrix_restrict_eq hvw _ hU 1 0 d 1 ?_ ?_
      · change (t₂ ^ n) v = _
        rw [hn, div_mul_cancel₀ _ hgv, one_smul]
      · change (t₂ ^ n) w = _
        rw [hn, h₂.2.2.1, mul_zero, zero_smul, add_zero, zero_smul, zero_add, one_smul]
  have hP : ∀ A, P A := by
    intro A
    have hA : A ∈ Subgroup.closure
        (Set.range (sl2Upper (ZMod p)) ∪ Set.range (sl2Lower (ZMod p))) := by
      rw [sl2_closure_upper_lower]
      exact Subgroup.mem_top A
    refine Subgroup.closure_induction'' (p := fun A _ => P A) ?_ ?_ ?_ ?_ hA
    · rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
      · exact hupper d
      · exact hlower d
    · rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
      · rw [← sl2Upper_neg]
        exact hupper (-d)
      · rw [← sl2Lower_neg]
        exact hlower (-d)
    · refine ⟨1, H.one_mem, fun x hx => hx, fun x _ => rfl, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_one, ← LinearMap.toMatrix_id B]
      congr 1
    · rintro A A' - - ⟨h, hh, hU, hL, hM⟩ ⟨h', hh', hU', hL', hM'⟩
      have hU'' : ∀ x ∈ Submodule.span (ZMod p) {v, w},
          (h * h') x ∈ Submodule.span (ZMod p) {v, w} := fun x hx => by
        rw [LinearEquiv.mul_apply]
        exact hU _ (hU' x hx)
      refine ⟨h * h', H.mul_mem hh hh', hU'', fun x hx => by
        rw [LinearEquiv.mul_apply, hL' x hx, hL x hx], ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hM, ← hM', ← LinearMap.toMatrix_comp]
      congr 1
  have hdet : (LinearMap.toMatrix B B φ).det = 1 := by rw [LinearMap.det_toMatrix, hφ]
  obtain ⟨h, hh, hU, hL, hM⟩ := hP ⟨LinearMap.toMatrix B B φ, hdet⟩
  have hres : (h : V →ₗ[ZMod p] V).restrict hU = φ := (LinearMap.toMatrix B B).injective hM
  refine ⟨h, hh, fun u => ?_, hL⟩
  rw [← hres, LinearMap.restrict_apply]
  rfl

theorem prime_three_space_transvection_reciprocal_pair [FiniteDimensional (ZMod p) V]
    (hV : Module.finrank (ZMod p) V = 3) (H : Subgroup (V ≃ₗ[ZMod p] V))
    (_hSL : ∀ h ∈ H, LinearMap.det (h : V →ₗ[ZMod p] V) = 1)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), S.Nonempty ∧
      (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧ H = Subgroup.closure S) :
    ∃ (t₁ t₂ : V ≃ₗ[ZMod p] V) (v w : V) (f g : Module.Dual (ZMod p) V),
      t₁ ∈ H ∧ t₂ ∈ H ∧ IsTransvectionWith t₁ v f ∧ IsTransvectionWith t₂ w g ∧
      f w * g v ≠ 0 ∧
      IsCompl (Submodule.span (ZMod p) {v, w}) (LinearMap.ker f ⊓ LinearMap.ker g) ∧
      ∀ φ : Submodule.span (ZMod p) {v, w} →ₗ[ZMod p] Submodule.span (ZMod p) {v, w},
        LinearMap.det φ = 1 → ∃ h ∈ H, (∀ u : Submodule.span (ZMod p) {v, w},
          h (u : V) = (φ u : V)) ∧ ∀ x ∈ LinearMap.ker f ⊓ LinearMap.ker g, h x = x := by
  obtain ⟨S, hSne, hS, hHS⟩ := hgen
  have hmem : ∀ t ∈ S, t ∈ H := fun t ht => hHS ▸ Subgroup.subset_closure ht
  suffices hpair : ∃ (t₁ t₂ : V ≃ₗ[ZMod p] V) (v w : V) (f g : Module.Dual (ZMod p) V),
      t₁ ∈ H ∧ t₂ ∈ H ∧ IsTransvectionWith t₁ v f ∧ IsTransvectionWith t₂ w g ∧
      f w * g v ≠ 0 by
    obtain ⟨t₁, t₂, v, w, f, g, ht₁, ht₂, h₁, h₂, hfg⟩ := hpair
    have hfw : f w ≠ 0 := left_ne_zero_of_mul hfg
    have hgv : g v ≠ 0 := right_ne_zero_of_mul hfg
    exact ⟨t₁, t₂, v, w, f, g, ht₁, ht₂, h₁, h₂, hfg,
      isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv,
      fun φ hφ => exists_mem_of_det_eq_one h₁ h₂ ht₁ ht₂ hfw hgv φ hφ⟩
  obtain ⟨t₁, ht₁S⟩ := hSne
  obtain ⟨v, f, h₁⟩ := hS t₁ ht₁S
  obtain ⟨t₂, ht₂S, w, g, h₂, hfw⟩ :=
    exists_mem_apply_center_ne_zero hirr ⟨t₁, ht₁S⟩ hS hHS h₁.2.1
  by_cases hgv : g v ≠ 0
  · exact ⟨t₁, t₂, v, w, f, g, hmem t₁ ht₁S, hmem t₂ ht₂S, h₁, h₂, mul_ne_zero hfw hgv⟩
  push Not at hgv
  have h₃ := isTransvectionWith_commutatorElement h₁ h₂ hgv hfw
  have ht₃ : ⁅t₁, t₂⁆ ∈ H := H.mul_mem (H.mul_mem (H.mul_mem (hmem t₁ ht₁S) (hmem t₂ ht₂S))
    (H.inv_mem (hmem t₁ ht₁S))) (H.inv_mem (hmem t₂ ht₂S))
  obtain ⟨t₄, ht₄S, u, e, h₄, hgu⟩ :=
    exists_mem_apply_center_ne_zero hirr ⟨t₁, ht₁S⟩ hS hHS h₂.2.1
  by_cases hew : e w ≠ 0
  · exact ⟨t₂, t₄, w, u, g, e, hmem t₂ ht₂S, hmem t₄ ht₄S, h₂, h₄, mul_ne_zero hgu hew⟩
  by_cases hev : e v ≠ 0
  · refine ⟨⁅t₁, t₂⁆, t₄, v, u, f w • g, e, ht₃, hmem t₄ ht₄S, h₃, h₄, ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero hfw hgu) hev
  push Not at hew hev
  exfalso
  have hli : LinearIndependent (ZMod p) ![v, w, u] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hc
    have hg := congrArg g hc
    rw [map_add, map_add, map_smul, map_smul, map_smul, hgv, h₂.2.2.1, map_zero, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, zero_add, zero_add] at hg
    have hc2 : c 2 = 0 := (mul_eq_zero.mp hg).resolve_right hgu
    have hf := congrArg f hc
    rw [map_add, map_add, map_smul, map_smul, map_smul, h₁.2.2.1, hc2, map_zero, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, mul_zero, zero_mul, zero_add, add_zero] at hf
    have hc1 : c 1 = 0 := (mul_eq_zero.mp hf).resolve_right hfw
    rw [hc1, hc2, zero_smul, zero_smul, add_zero, add_zero] at hc
    have hc0 : c 0 = 0 := (smul_eq_zero.mp hc).resolve_right h₁.1
    intro i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hV])
  apply h₄.2.1
  have hle : Submodule.span (ZMod p) (Set.range ![v, w, u]) ≤ LinearMap.ker e := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hev
    · exact hew
    · exact h₄.2.2.1
  rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
  exact hle

end Prime

end CFSG.RankThree.Classical
