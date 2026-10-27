module

public import CFSG.LocalAnalysis.StandardType.GGWAutOrthCosets
public import CFSG.LocalAnalysis.StandardType.GGWAutCommon

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section OrthOdd

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private lemma ggWAutO_polar_isom {Q : QuadraticForm (ZMod 3) V} {g : V ≃ₗ[ZMod 3] V}
    (h : ZS.IsIsom 3 Q g) (x y : V) :
    QuadraticMap.polarBilin Q (g x) (g y) = QuadraticMap.polarBilin Q x y := by
  have hxy : Q (g x + g y) = Q (x + y) := by
    rw [← map_add, h (x + y)]
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hxy, h x, h y]

private lemma ggWAutO_det_omega (Q : QuadraticForm (ZMod 3) V) :
    ∀ ω ∈ ggOmega Q, LinearEquiv.det ω = 1 := by
  intro ω hω
  have hker : ggOmega Q ≤ (LinearEquiv.det : (V ≃ₗ[ZMod 3] V) →* (ZMod 3)ˣ).ker := by
    rw [ggOmega]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨g, h, hg, hh, rfl⟩ := hx
    exact MonoidHom.mem_ker.mpr (by
      apply Units.ext
      simp only [Units.val_mul, Units.val_one, map_mul, map_inv, Units.val_inv_eq_inv_val]
      have hg : ((LinearEquiv.det g : (ZMod 3)ˣ) : ZMod 3) ≠ 0 := (LinearEquiv.det g).ne_zero
      have hh : ((LinearEquiv.det h : (ZMod 3)ˣ) : ZMod 3) ≠ 0 := (LinearEquiv.det h).ne_zero
      field_simp)
  exact MonoidHom.mem_ker.mp (hker hω)

private lemma ggWAutO_det_refl [Module.Finite (ZMod 3) V] {t : V ≃ₗ[ZMod 3] V} (h : IsReflLin t) :
    LinearEquiv.det t = -1 := by
  obtain ⟨c, φ, hc, rfl⟩ := h
  exact Module.det_reflection hc

theorem ggWAut_form_unique [Module.Finite (ZMod 3) V] (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R)
    (Q Q' : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQ' : (QuadraticMap.polarBilin Q').Nondegenerate) (h : ∀ g ∈ R, ZS.IsIsom 3 Q g)
    (h' : ∀ g ∈ R, ZS.IsIsom 3 Q' g) : ∃ c : ZMod 3, c ≠ 0 ∧ ∀ v, Q' v = c * Q v := by
  classical
  set B : LinearMap.BilinForm (ZMod 3) V := QuadraticMap.polarBilin Q with hBdef
  set B' : LinearMap.BilinForm (ZMod 3) V := QuadraticMap.polarBilin Q' with hB'def
  let φ : V →ₗ[ZMod 3] V := LinearMap.BilinForm.symmCompOfNondegenerate B' B hQ
  have hφ : ∀ x y : V, B (φ x) y = B' x y := fun x y =>
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply B' hQ y x
  have hinv : ∀ g ∈ R, ∀ x y : V, B (g x) (g y) = B x y := fun g hg x y =>
    ggWAutO_polar_isom (Q := Q) (h g hg) x y
  have hinv' : ∀ g ∈ R, ∀ x y : V, B' (g x) (g y) = B' x y := fun g hg x y =>
    ggWAutO_polar_isom (Q := Q') (h' g hg) x y
  have hcomm : ∀ g ∈ R, φ ∘ₗ (g : V →ₗ[ZMod 3] V) = (g : V →ₗ[ZMod 3] V) ∘ₗ φ := by
    intro g hg
    ext x
    apply sub_eq_zero.mp
    apply hQ.1
    intro y
    rw [LinearMap.comp_apply, LinearMap.comp_apply, map_sub, LinearMap.sub_apply, sub_eq_zero]
    calc B (φ (g x)) y = B' (g x) y := hφ (g x) y
      _ = B' (g x) (g ((g : V ≃ₗ[ZMod 3] V).symm y)) := by rw [LinearEquiv.apply_symm_apply]
      _ = B' x ((g : V ≃ₗ[ZMod 3] V).symm y) := hinv' g hg x _
      _ = B (φ x) ((g : V ≃ₗ[ZMod 3] V).symm y) := (hφ x _).symm
      _ = B (g (φ x)) (g ((g : V ≃ₗ[ZMod 3] V).symm y)) := (hinv g hg (φ x) _).symm
      _ = B (g (φ x)) y := by rw [LinearEquiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := habs.2 φ hcomm
  have hBc : ∀ x y : V, B' x y = c * B x y := by
    intro x y
    rw [← hφ x y, hc]
    simp
  have hQc : ∀ v : V, Q' v = c * Q v := by
    intro v
    have h2 : (2 : ZMod 3) * Q' v = (2 : ZMod 3) * (c * Q v) := by
      calc (2 : ZMod 3) * Q' v = 2 • Q' v := by simp
        _ = QuadraticMap.polar (⇑Q') v v := (QuadraticMap.polar_self Q' v).symm
        _ = B' v v := by rw [hB'def, QuadraticMap.polarBilin_apply_apply]
        _ = c * B v v := hBc v v
        _ = c * (2 • Q v) := by
              rw [hBdef, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
        _ = c * ((2 : ZMod 3) * Q v) := by simp
        _ = (2 : ZMod 3) * (c * Q v) := by ring
    exact mul_left_cancel₀ (show (2 : ZMod 3) ≠ 0 by decide) h2
  by_cases hc0 : c = 0
  · refine ⟨1, one_ne_zero, fun v => ?_⟩
    have hB'zero : B' = 0 := by
      ext x y
      rw [hBc, hc0]
      simp
    have hzero : ∀ x : V, x = 0 := fun x => hQ'.1 x (by rw [hB'zero]; simp)
    rw [hzero v]
    simp
  · exact ⟨c, hc0, hQc⟩

theorem ggWAut_normalizer_isom_odd [Module.Finite (ZMod 3) V] (hodd : Odd (Module.finrank (ZMod 3) V))
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R) (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hR : ∀ g ∈ R, ZS.IsIsom 3 Q g)
    (a : V ≃ₗ[ZMod 3] V) (ha : a ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) :
    ZS.IsIsom 3 Q a := by
  classical
  set B : LinearMap.BilinForm (ZMod 3) V := QuadraticMap.polarBilin Q with hBdef
  set Q' : QuadraticForm (ZMod 3) V := Q.comp (a : V →ₗ[ZMod 3] V) with hQ'def
  have hR' : ∀ g ∈ R, ZS.IsIsom 3 Q' g := by
    intro g hg v
    have hconj : a * g * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp ha g).mp hg
    have h1 : a (g v) = (a * g * a⁻¹) (a v) := by
      simp [mul_assoc]
    show Q (a (g v)) = Q (a v)
    rw [h1]
    exact hR _ hconj _
  have hB'form : ∀ x y : V, QuadraticMap.polarBilin Q' x y = B (a x) (a y) := by
    intro x y
    rw [hQ'def, QuadraticMap.polarBilin_comp, hBdef]
    rfl
  have hQ' : (QuadraticMap.polarBilin Q').Nondegenerate := by
    constructor
    · intro x hx
      have hx' : a x = 0 := hQ.1 (a x) (fun z => by
        have h := hx (a.symm z)
        rwa [hB'form x (a.symm z), LinearEquiv.apply_symm_apply] at h)
      exact a.injective (by simpa using hx')
    · intro y hy
      have hy' : a y = 0 := hQ.2 (a y) (fun z => by
        have h := hy (a.symm z)
        rwa [hB'form (a.symm z) y, LinearEquiv.apply_symm_apply] at h)
      exact a.injective (by simpa using hy')
  obtain ⟨c, hc0, hcQ⟩ := ggWAut_form_unique R habs Q Q' hQ hQ' hR hR'
  have hB'c : QuadraticMap.polarBilin Q' = c • B := by
    ext x y
    have hQp : QuadraticMap.polar (⇑Q') x y = c * QuadraticMap.polar (⇑Q) x y := by
      simp only [QuadraticMap.polar, hcQ]
      ring
    have h1 : B (a x) (a y) = QuadraticMap.polar Q' x y := by
      rw [← hB'form x y, QuadraticMap.polarBilin_apply_apply]
    have h2 : B x y = QuadraticMap.polar Q x y := by
      rw [hBdef, QuadraticMap.polarBilin_apply_apply]
    rw [hB'form x y, h1, hQp]
    simp [LinearMap.smul_apply, smul_eq_mul, h2]
  set n : ℕ := Module.finrank (ZMod 3) V with hn
  let b : Module.Basis (Fin n) (ZMod 3) V := Module.finBasis (ZMod 3) V
  let G : Matrix (Fin n) (Fin n) (ZMod 3) := LinearMap.BilinForm.toMatrix b B
  let G' : Matrix (Fin n) (Fin n) (ZMod 3) :=
    LinearMap.BilinForm.toMatrix b (QuadraticMap.polarBilin Q')
  let A : Matrix (Fin n) (Fin n) (ZMod 3) := LinearMap.toMatrix b b (a : V →ₗ[ZMod 3] V)
  have hG' : G' = A.transpose * G * A := by
    have hB'comp : QuadraticMap.polarBilin Q' =
        B.comp (a : V →ₗ[ZMod 3] V) (a : V →ₗ[ZMod 3] V) := by
      ext x y
      rw [hB'form x y]
      rfl
    show LinearMap.BilinForm.toMatrix b (QuadraticMap.polarBilin Q') =
      (LinearMap.toMatrix b b (a : V →ₗ[ZMod 3] V)).transpose *
        LinearMap.BilinForm.toMatrix b B * LinearMap.toMatrix b b (a : V →ₗ[ZMod 3] V)
    rw [hB'comp, LinearMap.BilinForm.toMatrix_comp b b B
      (a : V →ₗ[ZMod 3] V) (a : V →ₗ[ZMod 3] V)]
  have hG'smul : G' = c • G := by
    show LinearMap.BilinForm.toMatrix b (QuadraticMap.polarBilin Q') =
      c • LinearMap.BilinForm.toMatrix b B
    rw [hB'c, map_smul]
  have hdetG : G.det ≠ 0 := by
    rw [← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
    exact hQ
  have hdet_smul : G'.det = c ^ n * G.det := by
    rw [hG'smul, Matrix.det_smul, Fintype.card_fin]
  have hdet_mul : G'.det = A.det * G.det * A.det := by
    rw [hG', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hAsq : A.det * A.det = c ^ n := by
    have h : A.det * A.det * G.det = c ^ n * G.det := by
      calc A.det * A.det * G.det = A.det * G.det * A.det := by ring
        _ = G'.det := hdet_mul.symm
        _ = c ^ n * G.det := hdet_smul
    exact mul_right_cancel₀ hdetG h
  have hunit : IsUnit A.det := by
    rw [LinearMap.det_toMatrix b (a : V →ₗ[ZMod 3] V)]
    exact LinearEquiv.isUnit_det' a
  have hAsq1 : A.det * A.det = 1 :=
    (by decide : ∀ y : ZMod 3, y ≠ 0 → y * y = 1) A.det hunit.ne_zero
  have hcn : c ^ n = c := by
    rcases (by decide : ∀ y : ZMod 3, y ≠ 0 → y = 1 ∨ y = -1) c hc0 with rfl | rfl
    · simp
    · simpa using Odd.neg_one_pow (α := ZMod 3) hodd
  have hc1 : c = 1 := by
    have h : c ^ n = 1 := by rw [← hAsq, hAsq1]
    rw [hcn] at h
    exact h
  intro v
  have hv : Q' v = Q (a v) := rfl
  rw [← hv, hcQ v, hc1, one_mul]

theorem ggWAut_orth_cosets_mem [Module.Finite (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (A R : Subgroup (V ≃ₗ[ZMod 3] V))
    (hRA : R ≤ A) (hR : R = reflGp A) (hR1 : R ≠ ⊥) (hΩ : ggOmega Q ≤ R)
    (hA : ∀ a ∈ A, ZS.IsIsom 3 Q a) : A ≤ R := by
  classical
  have hn : 1 ≤ Module.finrank (ZMod 3) V := by
    by_contra hlt
    have h0 : Module.finrank (ZMod 3) V = 0 := by omega
    have : Subsingleton V := Module.finrank_zero_iff.mp h0
    have : Subsingleton (V ≃ₗ[ZMod 3] V) :=
      ⟨fun f g => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
    exact hR1 ((Subgroup.eq_bot_iff_forall R).mpr fun x _ => Subsingleton.elim _ _)
  obtain ⟨t₁, t₂, ⟨hrefl₁, hisom₁⟩, ⟨hrefl₂, hisom₂⟩, hdec⟩ := ggWAut_orth_cosets Q hQ hn
  have hmemR : ∀ {t : V ≃ₗ[ZMod 3] V}, t ∈ A → IsReflLin t → t ∈ R := by
    intro t htA ht
    rw [hR]
    exact Subgroup.subset_closure ⟨htA, ht⟩
  have hne : ∃ t : V ≃ₗ[ZMod 3] V, t ∈ A ∧ IsReflLin t := by
    by_contra hemp
    have hle : Subgroup.closure {t : V ≃ₗ[ZMod 3] V | t ∈ A ∧ IsReflLin t} ≤ ⊥ := by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      exact absurd ⟨x, hx⟩ hemp
    have hbot : reflGp A = ⊥ := le_antisymm hle bot_le
    exact hR1 (hR.trans hbot)
  obtain ⟨tc, htcA, htcRefl⟩ := hne
  have htcR : tc ∈ R := hmemR htcA htcRefl
  have hdetOm : ∀ ω ∈ ggOmega Q, LinearEquiv.det ω = 1 := ggWAutO_det_omega Q
  have hdet₁ : LinearEquiv.det t₁ = -1 := ggWAutO_det_refl hrefl₁
  have hdet₂ : LinearEquiv.det t₂ = -1 := ggWAutO_det_refl hrefl₂
  have hdettc : LinearEquiv.det tc = -1 := ggWAutO_det_refl htcRefl
  have hone : (1 : (ZMod 3)ˣ) ≠ -1 := by decide
  have hneg : (-1 : (ZMod 3)ˣ) * (-1) = 1 := by
    apply Units.ext
    simp
  have hclass : ∀ {x : V ≃ₗ[ZMod 3] V}, ZS.IsIsom 3 Q x → LinearEquiv.det x = -1 →
      ∃ ω ∈ ggOmega Q, x = ω * t₁ ∨ x = ω * t₂ := by
    intro x hx hdet
    obtain ⟨ω, hω, hx'⟩ := hdec x hx
    rcases hx' with h | h | h | h
    · have h1 : LinearEquiv.det ω = 1 := hdetOm ω hω
      rw [h, h1] at hdet
      exact absurd hdet hone
    · exact ⟨ω, hω, Or.inl h⟩
    · exact ⟨ω, hω, Or.inr h⟩
    · have h1 : LinearEquiv.det (ω * (t₁ * t₂)) = 1 := by
        rw [map_mul, map_mul, hdetOm ω hω, hdet₁, hdet₂]
        simp [hneg]
      rw [h, h1] at hdet
      exact absurd hdet hone
  intro a ha
  have haIsom : ZS.IsIsom 3 Q a := hA a ha
  obtain ⟨ω, hω, ha'⟩ := hdec a haIsom
  have hωR : ω ∈ R := hΩ hω
  rcases ha' with h | h | h | h
  · rw [h]
    exact hωR
  · have ht1A : t₁ ∈ A := by
      have h1 : t₁ = ω⁻¹ * a := by rw [h]; group
      rw [h1]
      exact A.mul_mem (hRA (R.inv_mem hωR)) ha
    rw [h]
    exact R.mul_mem hωR (hmemR ht1A hrefl₁)
  · have ht2A : t₂ ∈ A := by
      have h1 : t₂ = ω⁻¹ * a := by rw [h]; group
      rw [h1]
      exact A.mul_mem (hRA (R.inv_mem hωR)) ha
    rw [h]
    exact R.mul_mem hωR (hmemR ht2A hrefl₂)
  ·
    have hdet_a : LinearEquiv.det a = 1 := by
      rw [h, map_mul, map_mul, hdetOm ω hω, hdet₁, hdet₂]
      simp [hneg]
    have hatcA : a * tc ∈ A := A.mul_mem ha (hRA htcR)
    have hdet_atc : LinearEquiv.det (a * tc) = -1 := by
      rw [map_mul, hdet_a, hdettc]
      simp
    obtain ⟨ωc, hωc, hc⟩ := hclass (hA tc htcA) hdettc
    obtain ⟨ω₂, hω₂, hd⟩ := hclass (hA (a * tc) hatcA) hdet_atc
    have hωcR : ωc ∈ R := hΩ hωc
    have hω₂R : ω₂ ∈ R := hΩ hω₂
    rcases hc with hc | hc <;> rcases hd with hd | hd
    ·
      have hkey : a = ω₂ * ωc⁻¹ := by
        calc a = a * tc * tc⁻¹ := by group
          _ = (ω₂ * t₁) * (ωc * t₁)⁻¹ := by rw [hd, hc]
          _ = ω₂ * ωc⁻¹ := by group
      rw [hkey]
      exact hΩ ((ggOmega Q).mul_mem hω₂ ((ggOmega Q).inv_mem hωc))
    ·
      have ht1A : t₁ ∈ A := by
        have h1 : t₁ = ωc⁻¹ * tc := by rw [hc]; group
        rw [h1]
        exact A.mul_mem (hRA (hΩ ((ggOmega Q).inv_mem hωc))) (hRA htcR)
      have ht2A : t₂ ∈ A := by
        have h1 : t₂ = ω₂⁻¹ * (a * tc) := by rw [hd]; group
        rw [h1]
        exact A.mul_mem (hRA (hΩ ((ggOmega Q).inv_mem hω₂))) hatcA
      rw [h]
      exact R.mul_mem hωR (R.mul_mem (hmemR ht1A hrefl₁) (hmemR ht2A hrefl₂))
    ·
      have ht2A : t₂ ∈ A := by
        have h1 : t₂ = ωc⁻¹ * tc := by rw [hc]; group
        rw [h1]
        exact A.mul_mem (hRA (hΩ ((ggOmega Q).inv_mem hωc))) (hRA htcR)
      have ht1A : t₁ ∈ A := by
        have h1 : t₁ = ω₂⁻¹ * (a * tc) := by rw [hd]; group
        rw [h1]
        exact A.mul_mem (hRA (hΩ ((ggOmega Q).inv_mem hω₂))) hatcA
      rw [h]
      exact R.mul_mem hωR (R.mul_mem (hmemR ht1A hrefl₁) (hmemR ht2A hrefl₂))
    ·
      have hkey : a = ω₂ * ωc⁻¹ := by
        calc a = a * tc * tc⁻¹ := by group
          _ = (ω₂ * t₂) * (ωc * t₂)⁻¹ := by rw [hd, hc]
          _ = ω₂ * ωc⁻¹ := by group
      rw [hkey]
      exact hΩ ((ggOmega Q).mul_mem hω₂ ((ggOmega Q).inv_mem hωc))

end OrthOdd

theorem ggWAut_orthOdd {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (hodd : Odd (Module.finrank (ZMod 3) V)) (A R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRA : R ≤ A)
    (hR : R = reflGp A) (habs : ZS.AbsIrred 3 R) (hO : GGOrthType R) :
    ∀ a ∈ A, ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  classical
  rcases eq_or_ne (Module.finrank (ZMod 3) V) 1 with hdim1 | hdim1
  ·
    intro a _
    obtain ⟨c, hc, -⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one (R := ZMod 3) hdim1
        (a : V →ₗ[ZMod 3] V)
    have : Nontrivial V :=
      Module.finrank_pos_iff (R := ZMod 3) (M := V) |>.mp (by rw [hdim1]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have haev : ∀ w : V, a w = c • w := by
      intro w
      have h : (a : V →ₗ[ZMod 3] V) w = c • w := by rw [hc]; simp
      exact h
    have hc0 : c ≠ 0 := by
      intro hc0
      have hzero : a v = 0 := by rw [haev v, hc0]; simp
      exact hv (a.injective (by simpa using hzero))
    rcases (by decide : ∀ y : ZMod 3, y ≠ 0 → y = 1 ∨ y = -1) c hc0 with hc1 | hcneg
    · refine ⟨1, R.one_mem, Or.inl ?_⟩
      intro w
      rw [haev w, hc1]
      simp
    · refine ⟨1, R.one_mem, Or.inr ?_⟩
      intro w
      rw [haev w, hcneg]
      simp
  ·
    have hfin2 : 2 ≤ Module.finrank (ZMod 3) V := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have : Nontrivial V := Module.finrank_pos_iff (R := ZMod 3) (M := V) |>.mp (by omega)
    have hR1 : R ≠ ⊥ := by
      intro hbot
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      let W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) ({v} : Set V)
      have hWfin : Module.finrank (ZMod 3) W = 1 := finrank_span_singleton hv
      have hWinv : ∀ a ∈ R, ∀ w ∈ W, a w ∈ W := by
        intro a ha w hw
        have ha1 : a = 1 := by
          have : a ∈ (⊥ : Subgroup (V ≃ₗ[ZMod 3] V)) := by rwa [← hbot]
          exact Subgroup.mem_bot.mp this
        rw [ha1]
        simpa using hw
      rcases habs.1 W hWinv with hW | hW
      · have hvW : v ∈ W := Submodule.subset_span (by simp)
        rw [hW] at hvW
        exact hv (by simpa using hvW)
      · have : Module.finrank (ZMod 3) V = 1 := by
          rw [← hWfin, hW, finrank_top]
        omega
    obtain ⟨Q, hQ, hRQ, hcomm⟩ := hO
    have hΩ : ggOmega Q ≤ R := by
      rw [ggOmega]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      obtain ⟨g, h, hg, hh, rfl⟩ := hx
      exact hcomm g h hg hh
    have hA : ∀ a ∈ A, ZS.IsIsom 3 Q a := by
      intro a ha
      refine ggWAut_normalizer_isom_odd hodd R habs Q hQ hRQ a ?_
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hh' : h ∈ reflGp A := by rwa [← hR]
        have := ggWAut_reflGp_conj A ha hh'
        rwa [hR]
      · intro hh
        have hh' : a * h * a⁻¹ ∈ reflGp A := by rwa [← hR]
        have hconj := ggWAut_reflGp_conj A (A.inv_mem ha) hh'
        have heq : a⁻¹ * (a * h * a⁻¹) * (a⁻¹)⁻¹ = h := by group
        rw [heq] at hconj
        rwa [hR]
    have hAR : A ≤ R := ggWAut_orth_cosets_mem Q hQ A R hRA hR hR1 hΩ hA
    intro a ha
    exact ⟨a, hAR ha, Or.inl fun _ => rfl⟩

end CFSG.StandardType

end
