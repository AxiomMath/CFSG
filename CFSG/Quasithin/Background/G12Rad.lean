module

public import CFSG.Quasithin.Background.G12Stmts

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem g12_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem g12_add_eq_one_of_ne : ∀ c c' : ZMod 2, c ≠ c' → c + c' = 1 := by decide

theorem g12_eq_zero_or_one : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem g12_eq_one_of_ne_zero : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

theorem g12_vadd_self (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem IsSymplectic.symm' {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B) (x y : V) :
    B x y = B y x := by
  have h1 := h.1 (x + y)
  simp only [map_add, LinearMap.add_apply, h.1 x, h.1 y, zero_add, add_zero] at h1
  have : B x y + B y x = 0 := by rw [add_comm]; exact h1
  have h2 := g12_add_self (B y x)
  calc B x y = B x y + (B y x + B y x) := by rw [h2, add_zero]
      _ = (B x y + B y x) + B y x := by rw [add_assoc]
      _ = B y x := by rw [this, zero_add]

theorem IsSymplectic.isRefl {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B) :
    B.IsRefl := fun x y hxy => by
  rw [h.symm']; exact hxy

theorem IsSymplectic.nondegenerate {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B) :
    B.Nondegenerate := by
  refine ⟨fun x hx => h.2 x hx, fun y hy => h.2 y fun x => ?_⟩
  rw [h.symm']; exact hy x

theorem mem_perp_iff {B : LinearMap.BilinForm (ZMod 2) V} {v x : V} : x ∈ perp B v ↔ B v x = 0 :=
  LinearMap.mem_ker

theorem perp_eq_orthogonal (B : LinearMap.BilinForm (ZMod 2) V) (v : V) :
    perp B v = B.orthogonal (Submodule.span (ZMod 2) {v}) := by
  ext x
  simp only [mem_perp_iff, LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_span_singleton]
  constructor
  · rintro hx _ ⟨c, rfl⟩
    simp [hx]
  · intro hx
    simpa using hx v ⟨1, one_smul _ _⟩

section Finite

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}

theorem IsSymplectic.orthogonal_perp (h : IsSymplectic B) (v : V) :
    B.orthogonal (perp B v) = Submodule.span (ZMod 2) {v} := by
  rw [perp_eq_orthogonal, LinearMap.BilinForm.orthogonal_orthogonal h.nondegenerate h.isRefl]

theorem IsSymplectic.finrank_perp (h : IsSymplectic B) {v : V} (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (perp B v) + 1 = Module.finrank (ZMod 2) V := by
  have := LinearMap.BilinForm.finrank_orthogonal h.nondegenerate (Submodule.span (ZMod 2) {v})
  rw [← perp_eq_orthogonal, finrank_span_singleton hv] at this
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) ≤ Module.finrank (ZMod 2) V :=
    Submodule.finrank_le _
  rw [finrank_span_singleton hv] at h2
  omega

omit [Finite V] in
theorem IsSymplectic.exists_B_eq_one (h : IsSymplectic B) {v : V} (hv : v ≠ 0) :
    ∃ x, B x v = 1 := by
  by_contra hcon
  simp only [not_exists] at hcon
  apply hv
  apply h.2 v
  intro y
  rw [h.symm']
  by_contra hy
  exact hcon y (g12_eq_one_of_ne_zero _ hy)

theorem IsSymplectic.exists_rep (h : IsSymplectic B) (F : V →ₗ[ZMod 2] ZMod 2) :
    ∃ a, ∀ x, B x a = F x := by
  refine ⟨(B.toDual h.nondegenerate).symm F, fun x => ?_⟩
  rw [h.symm', LinearMap.BilinForm.apply_toDual_symm_apply]

theorem IsSymplectic.exists_rep_perp (h : IsSymplectic B) {v : V} (hv : v ∈ perp B v)
    (f : perp B v →ₗ[ZMod 2] ZMod 2) (hf : f ⟨v, hv⟩ = 0) :
    ∃ a, B v a = 0 ∧ ∀ u : perp B v, B u a = f u := by
  obtain ⟨F, hF⟩ := LinearMap.exists_extend f
  obtain ⟨a, ha⟩ := h.exists_rep F
  have hFu : ∀ u : perp B v, F u = f u := fun u => by
    have := congrArg (fun g => g u) hF
    simpa using this
  refine ⟨a, ?_, fun u => ?_⟩
  · rw [ha v]
    have := hFu ⟨v, hv⟩
    simp only at this
    rw [this, hf]
  · rw [ha u, hFu u]

end Finite

@[expose] def radLin (B : LinearMap.BilinForm (ZMod 2) V) (v a : V) (c : ZMod 2) :
    V →ₗ[ZMod 2] V where
  toFun x := x + B x v • a + (B x a + c * B x v) • v
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, add_smul, mul_add]
    abel
  map_smul' t x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    module

theorem radLin_apply (B : LinearMap.BilinForm (ZMod 2) V) (v a : V) (c : ZMod 2) (x : V) :
    radLin B v a c x = x + B x v • a + (B x a + c * B x v) • v := rfl

section Rad

variable {B : LinearMap.BilinForm (ZMod 2) V} {v a : V} {c : ZMod 2}

theorem radLin_invol (h : IsSymplectic B) (hva : B v a = 0) (x : V) :
    radLin B v a c (radLin B v a c x) = x := by
  have hav : B a v = 0 := by rw [h.symm' a v]; exact hva
  have hvv : B v v = 0 := h.1 v
  have haa : B a a = 0 := h.1 a
  have e1 : B (radLin B v a c x) v = B x v := by
    rw [radLin_apply]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hav,
      hvv, mul_zero, add_zero]
  have e2 : B (radLin B v a c x) a = B x a := by
    rw [radLin_apply]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, haa,
      hva, mul_zero, add_zero]
  rw [radLin_apply B v a c (radLin B v a c x), e1, e2, radLin_apply]
  have h1 := g12_vadd_self (B x v • a)
  have h2 := g12_vadd_self ((B x a + c * B x v) • v)
  calc x + B x v • a + (B x a + c * B x v) • v + B x v • a + (B x a + c * B x v) • v
      = x + (B x v • a + B x v • a) + ((B x a + c * B x v) • v + (B x a + c * B x v) • v) := by
        abel
    _ = x := by rw [h1, h2]; simp

open Classical in
@[expose] noncomputable def radE (B : LinearMap.BilinForm (ZMod 2) V) (v a : V) (c : ZMod 2) :
    GLV V :=
  if h : IsSymplectic B ∧ B v a = 0 then
    LinearEquiv.ofInvolutive (radLin B v a c) (fun x => radLin_invol h.1 h.2 x)
  else 1

theorem radE_apply (h : IsSymplectic B) (hva : B v a = 0) (x : V) :
    radE B v a c x = x + B x v • a + (B x a + c * B x v) • v := by
  simp only [radE, h, hva, and_self, dite_true]
  rfl

theorem radE_apply_v (h : IsSymplectic B) (hva : B v a = 0) : radE B v a c v = v := by
  rw [radE_apply h hva]
  simp [h.1 v, hva]

theorem radE_mul (h : IsSymplectic B) {a' : V} {c' : ZMod 2} (hva : B v a = 0) (hva' : B v a' = 0) :
    radE B v a c * radE B v a' c' = radE B v (a + a') (c + c' + B a a') := by
  have hv : B v (a + a') = 0 := by rw [map_add, hva, hva', add_zero]
  refine LinearEquiv.ext fun x => ?_
  show radE B v a c (radE B v a' c' x) = radE B v (a + a') (c + c' + B a a') x
  have hav' : B a' v = 0 := by rw [h.symm' a' v]; exact hva'
  rw [radE_apply h hva, radE_apply h hva', radE_apply h hv]
  have hs : B a' a = B a a' := h.symm' a' a
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    hav', h.1 v, hva, hs, mul_zero, add_zero]
  module

theorem radE_conj (h : IsSymplectic B) {g : GLV V} (hg : g ∈ spSub B) (hva : B v a = 0) :
    g * radE B v a c * g⁻¹ = radE B (g v) (g a) c := by
  have hg' : ∀ x y, B (g x) (g y) = B x y := hg
  have hva2 : B (g v) (g a) = 0 := by rw [hg']; exact hva
  refine LinearEquiv.ext fun x => ?_
  show g (radE B v a c (g.symm x)) = radE B (g v) (g a) c x
  rw [radE_apply h hva, radE_apply h hva2, map_add, map_add, map_smul, map_smul]
  have e1 : B (g.symm x) v = B x (g v) := by
    have := hg' (g.symm x) v
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have e2 : B (g.symm x) a = B x (g a) := by
    have := hg' (g.symm x) a
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e1, e2, LinearEquiv.apply_symm_apply]

theorem radE_mem_spSub (h : IsSymplectic B) (hva : B v a = 0) : radE B v a c ∈ spSub B := by
  intro x y
  rw [radE_apply h hva, radE_apply h hva]
  have hav : B a v = 0 := by rw [h.symm' a v]; exact hva
  have e1 := h.symm' a y
  have e2 := h.symm' v y
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h.1 a,
    h.1 v, hva, hav, e1, e2, mul_zero, add_zero]
  have two0 : (2 : ZMod 2) = 0 := rfl
  linear_combination (B x v * B y a + B x a * B y v + c * B x v * B y v) * two0

theorem radE_zero_zero (h : IsSymplectic B) : radE B v 0 0 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [radE_apply h (by simp)]
  simp

theorem radE_mul_self (h : IsSymplectic B) (hva : B v a = 0) :
    radE B v a c * radE B v a c = 1 := by
  rw [radE_mul h hva hva, g12_vadd_self a, g12_add_self c, h.1 a, add_zero]
  exact radE_zero_zero h

theorem radE_unique (h : IsSymplectic B) (hva : B v a = 0) {Γ : Subgroup (GLV V)}
    (hΓ : radE B v 0 1 ∉ Γ) {c c' : ZMod 2} (h1 : radE B v a c ∈ Γ) (h2 : radE B v a c' ∈ Γ) :
    c = c' := by
  by_contra hne
  apply hΓ
  have := Γ.mul_mem h1 h2
  rw [radE_mul h hva hva, g12_vadd_self a, h.1 a, add_zero] at this
  have hc : c + c' = 1 := g12_add_eq_one_of_ne c c' hne
  rwa [hc] at this

theorem radE_zero_apply (h : IsSymplectic B) (x : V) :
    radE B v 0 c x = x + (c * B x v) • v := by
  rw [radE_apply h (by simp)]
  simp

end Rad

section Star

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}

omit [Finite V] in
theorem radE_mem_QSub (h : IsSymplectic B) {v a : V} {c : ZMod 2} (hva : B v a = 0)
    (hΓ : radE B v a c ∈ Γ) : radE B v a c ∈ QSub Γ v (perp B v) := by
  refine ⟨hΓ, radE_apply_v h hva, fun x hx => ?_⟩
  have hxv : B x v = 0 := by rw [h.symm']; exact mem_perp_iff.1 hx
  have e : radE B v a c x = x + B x a • v := by
    rw [radE_apply h hva, hxv]; simp
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [mem_perp_iff, map_add, map_smul, mem_perp_iff.1 hx, h.1 v]; simp
  · rw [add_sub_cancel_left]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem eq_radE_of_fix (h : IsSymplectic B) {v a : V} (hva : B v a = 0)
    {y : GLV V} (hy : y ∈ spSub B)
    (hyu : ∀ u ∈ perp B v, y u = u + B u a • v) : ∃ c, y = radE B v a c := by
  by_cases hv0 : v = 0
  · subst hv0
    refine ⟨0, ?_⟩
    have h1 : radE B 0 a 0 = 1 := by
      refine LinearEquiv.ext fun x => ?_
      rw [radE_apply h hva]
      simp
    rw [h1]
    refine LinearEquiv.ext fun x => ?_
    have := hyu x (by simp [mem_perp_iff])
    simpa using this
  have hr0 : radE B v a 0 ∈ spSub B := radE_mem_spSub h hva
  have hy' : radE B v a 0 * y ∈ spSub B := (spSub B).mul_mem hr0 hy
  have hfix : ∀ u ∈ perp B v, (radE B v a 0 * y) u = u := by
    intro u hu
    have huv : B u v = 0 := by rw [h.symm']; exact mem_perp_iff.1 hu
    show radE B v a 0 (y u) = u
    rw [hyu u hu, map_add, map_smul, radE_apply_v h hva, radE_apply h hva, huv]
    have h2 := g12_vadd_self (B u a • v)
    calc u + (0 : ZMod 2) • a + (B u a + 0 * 0) • v + B u a • v
        = u + (B u a • v + B u a • v) := by simp [add_assoc]
      _ = u := by rw [h2, add_zero]
  obtain ⟨x0, hx0⟩ := h.exists_B_eq_one hv0
  have hz : (radE B v a 0 * y) x0 - x0 ∈ B.orthogonal (perp B v) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have h1 : B w ((radE B v a 0 * y) x0) = B w x0 := by
      have := hy' w x0
      rwa [hfix w hw] at this
    rw [map_sub, h1, sub_self]
  rw [h.orthogonal_perp, Submodule.mem_span_singleton] at hz
  obtain ⟨t, ht⟩ := hz
  have hall : ∀ x, (radE B v a 0 * y) x = x + (t * B x v) • v := by
    intro x
    have hmem : x - B x v • x0 ∈ perp B v := by
      rw [mem_perp_iff, map_sub, map_smul, smul_eq_mul, h.symm' v x0, hx0, mul_one, h.symm' v x,
        sub_self]
    have h1 := hfix _ hmem
    have h2 : (radE B v a 0 * y) x0 = x0 + t • v := by
      rw [ht]; abel
    have h3 : (radE B v a 0 * y) x = (radE B v a 0 * y) (x - B x v • x0) +
        B x v • (radE B v a 0 * y) x0 := by
      rw [← map_smul, ← map_add]; congr 1; abel
    rw [h3, h1, h2]
    simp only [smul_add, smul_smul, mul_comm t]
    abel
  have heq : radE B v a 0 * y = radE B v 0 t := by
    refine LinearEquiv.ext fun x => ?_
    rw [hall x, radE_zero_apply h x]
  refine ⟨t, ?_⟩
  have : y = radE B v a 0 * radE B v 0 t := by
    rw [← heq, ← mul_assoc, radE_mul_self h hva, one_mul]
  have e := radE_mul (c := (0 : ZMod 2)) (c' := t) h hva (show B v 0 = 0 by simp)
  rw [add_zero, map_zero, add_zero, zero_add] at e
  rw [← e, this]

theorem exists_radE_of_fix (h : IsSymplectic B) (hΓ : Γ ≤ spSub B) {v a : V} (hva : B v a = 0)
    {y : GLV V} (hy : y ∈ Γ)
    (hyu : ∀ u ∈ perp B v, y u = u + B u a • v) : ∃ c, radE B v a c ∈ Γ := by
  obtain ⟨c, hc⟩ := eq_radE_of_fix h hva (hΓ hy) hyu
  exact ⟨c, hc ▸ hy⟩

theorem isStarVec_iff_rad (h : IsSymplectic B) (hΓ : Γ ≤ spSub B) {v : V} :
    IsStarVec B Γ v ↔ v ≠ 0 ∧ ∀ a, B v a = 0 → ∃ c, radE B v a c ∈ Γ := by
  constructor
  · rintro ⟨hv0, hv, hft⟩
    refine ⟨hv0, fun a hva => ?_⟩
    let f : perp B v →ₗ[ZMod 2] ZMod 2 := (B.flip a).comp (perp B v).subtype
    have hf : f ⟨v, hv⟩ = 0 := hva
    obtain ⟨y, hy, hyu⟩ := hft.2 f hf
    exact exists_radE_of_fix h hΓ hva hy.1 (fun u hu => hyu ⟨u, hu⟩)
  · rintro ⟨hv0, H⟩
    have hv : v ∈ perp B v := mem_perp_iff.2 (h.1 v)
    refine ⟨hv0, hv, ?_, ?_⟩
    · intro y hy
      obtain ⟨x0, hx0⟩ := h.exists_B_eq_one hv0
      let φ : V →ₗ[ZMod 2] V := (y : V →ₗ[ZMod 2] V) - LinearMap.id
      refine ⟨(B x0).comp (φ.comp (perp B v).subtype), ?_, fun u => ?_⟩
      · show B x0 (y v - v) = 0
        rw [hy.2.1, sub_self, map_zero]
      · obtain ⟨-, hyu⟩ := hy.2.2 u u.2
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hyu
        have hfu : (B x0).comp (φ.comp (perp B v).subtype) u = t := by
          show B x0 (y u - u) = t
          rw [← ht, map_smul, hx0, smul_eq_mul, mul_one]
        rw [hfu, ht]
        abel
    · intro f hf
      obtain ⟨a, hva, ha⟩ := h.exists_rep_perp hv f hf
      obtain ⟨c, hc⟩ := H a hva
      refine ⟨radE B v a c, radE_mem_QSub h hva hc, fun u => ?_⟩
      have huv : B u v = 0 := by rw [h.symm']; exact mem_perp_iff.1 u.2
      rw [radE_apply h hva, huv, ha u]
      simp

theorem IsStarVec.conj (h : IsSymplectic B) (hΓ : Γ ≤ spSub B) {g : GLV V} (hg : g ∈ Γ) {v : V}
    (hv : IsStarVec B Γ v) : IsStarVec B Γ (g v) := by
  rw [isStarVec_iff_rad h hΓ] at hv ⊢
  obtain ⟨hv0, H⟩ := hv
  refine ⟨fun h0 => hv0 (by simpa using h0), fun a' ha' => ?_⟩
  have hgi : ∀ x y, B (g x) (g y) = B x y := hΓ hg
  have hva : B v (g.symm a') = 0 := by
    rw [← hgi, LinearEquiv.apply_symm_apply]; exact ha'
  obtain ⟨c, hc⟩ := H _ hva
  refine ⟨c, ?_⟩
  have := Γ.mul_mem (Γ.mul_mem hg hc) (Γ.inv_mem hg)
  rw [radE_conj h (hΓ hg) hva, LinearEquiv.apply_symm_apply] at this
  exact this

omit [Finite V] in
theorem radE_conj_mem (h : IsSymplectic B) (hΓ : Γ ≤ spSub B) {g : GLV V} (hg : g ∈ Γ) {v a : V}
    {c : ZMod 2} (hva : B v a = 0) (hc : radE B v a c ∈ Γ) : radE B (g v) (g a) c ∈ Γ := by
  have := Γ.mul_mem (Γ.mul_mem hg hc) (Γ.inv_mem hg)
  rwa [radE_conj h (hΓ hg) hva] at this

end Star

section Extra

variable {B : LinearMap.BilinForm (ZMod 2) V}

theorem radE_one_apply (h : IsSymplectic B) {v : V} (x : V) :
    radE B v 0 1 x = x + B x v • v := by
  rw [radE_zero_apply h x, one_mul]

theorem IsSymplectic.exists_perp_one (h : IsSymplectic B) {v w : V} (hw : w ≠ 0) (hvw : v ≠ w) :
    ∃ a, B v a = 0 ∧ B w a = 1 := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  obtain ⟨b, hb⟩ := h.exists_B_eq_one hw
  have hb' : B w b = 1 := by rw [h.symm']; exact hb
  have hvb : B v b = 1 := by
    by_contra hne
    exact hcon b (by
      rcases g12_eq_zero_or_one (B v b) with h0 | h1
      · exact h0
      · exact absurd h1 hne) hb'
  have key : ∀ a, B v a = B w a := by
    intro a
    rcases g12_eq_zero_or_one (B v a) with h0 | h1
    · have h2 : B w a ≠ 1 := hcon a h0
      rw [h0, show B w a = 0 from by
        rcases g12_eq_zero_or_one (B w a) with h3 | h3
        · exact h3
        · exact absurd h3 h2]
    · rw [h1]
      by_contra hne
      have h4 : B w a = 0 := by
        rcases g12_eq_zero_or_one (B w a) with h3 | h3
        · exact h3
        · exact absurd h3.symm hne
      have h5 : B v (a + b) = 0 := by
        rw [map_add, h1, hvb]; decide
      have h6 := hcon (a + b) h5
      apply h6
      rw [map_add, h4, hb']; decide
  apply hvw
  have : v + w = 0 := by
    apply h.2 (v + w)
    intro y
    rw [map_add, LinearMap.add_apply, key y, g12_add_self]
  calc v = v + (w + w) := by rw [g12_vadd_self, add_zero]
    _ = (v + w) + w := by rw [add_assoc]
    _ = w := by rw [this, zero_add]

theorem IsSymplectic.exists_B_eq_one_one (h : IsSymplectic B) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ x, B x v = 1 ∧ B x w = 1 := by
  obtain ⟨x, hx⟩ := h.exists_B_eq_one hv
  obtain ⟨y, hy⟩ := h.exists_B_eq_one hw
  rcases g12_eq_zero_or_one (B x w) with h0 | h1
  · rcases g12_eq_zero_or_one (B y v) with h2 | h3
    · refine ⟨x + y, ?_, ?_⟩
      · rw [map_add, LinearMap.add_apply, hx, h2]; decide
      · rw [map_add, LinearMap.add_apply, h0, hy]; decide
    · exact ⟨y, h3, hy⟩
  · exact ⟨x, hx, h1⟩

variable [Finite V] in
theorem IsStarVec.mono (h : IsSymplectic B) {Γ Γ' : Subgroup (GLV V)} (hΓ : Γ ≤ spSub B)
    (hΓ' : Γ' ≤ spSub B) (hle : Γ ≤ Γ') {v : V} (hv : IsStarVec B Γ v) : IsStarVec B Γ' v := by
  rw [isStarVec_iff_rad h hΓ] at hv
  rw [isStarVec_iff_rad h hΓ']
  exact ⟨hv.1, fun a ha => (hv.2 a ha).imp fun c hc => hle hc⟩

end Extra

end NoInst

end CFSG.Quasithin.G11
