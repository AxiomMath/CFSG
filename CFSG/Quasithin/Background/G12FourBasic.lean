module

public import CFSG.Quasithin.Background.G12Twelve

public section

namespace CFSG.Quasithin.G11

open scoped commutatorElement

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V}

theorem g12f_tv_mul_self (hB : IsSymplectic B) (x : V) : radE B x 0 1 * radE B x 0 1 = 1 :=
  radE_mul_self hB (by simp)

theorem g12f_tv_inv (hB : IsSymplectic B) (x : V) : (radE B x 0 1)⁻¹ = radE B x 0 1 :=
  inv_eq_of_mul_eq_one_right (g12f_tv_mul_self hB x)

theorem g12f_tv_mem (hB : IsSymplectic B) (x : V) : radE B x 0 1 ∈ spSub B :=
  radE_mem_spSub hB (by simp)

theorem g12f_tv_zero (hB : IsSymplectic B) : radE B (0 : V) 0 1 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  rw [radE_one_apply hB]
  simp

theorem g12f_tv_conj (hB : IsSymplectic B) {g : GLV V} (hg : g ∈ spSub B) (x : V) :
    g * radE B x 0 1 * g⁻¹ = radE B (g x) 0 1 := by
  rw [radE_conj hB hg (by simp), map_zero]

theorem g12f_tv_conj_tv (hB : IsSymplectic B) {x y : V} (hyx : B y x = 1) :
    radE B x 0 1 * radE B y 0 1 * radE B x 0 1 = radE B (x + y) 0 1 := by
  have h := g12f_tv_conj hB (g12f_tv_mem hB x) y
  rw [g12f_tv_inv hB, radE_one_apply hB, hyx, one_smul, add_comm] at h
  exact h

theorem g12f_tv_mul_eq_commutator (hB : IsSymplectic B) {x y : V} (hxy : B x y = 1) :
    radE B x 0 1 * radE B y 0 1 = ⁅radE B y 0 1, radE B x 0 1⁆ := by
  have hyx : B y x = 1 := by rw [hB.symm']; exact hxy
  rw [commutatorElement_def, g12f_tv_inv hB, g12f_tv_inv hB]
  have h1 := g12f_tv_conj_tv hB hyx
  have h2 := g12f_tv_conj_tv hB hxy
  calc radE B x 0 1 * radE B y 0 1
      = radE B x 0 1 * radE B y 0 1 * radE B x 0 1 * radE B x 0 1 := by
        simp only [mul_assoc, g12f_tv_mul_self hB, mul_one]
    _ = radE B (x + y) 0 1 * radE B x 0 1 := by rw [h1]
    _ = radE B y 0 1 * radE B x 0 1 * radE B y 0 1 * radE B x 0 1 := by rw [h2, add_comm y x]

theorem g12f_radE_add_eq (hB : IsSymplectic B) {x y : V} (hxy : B x y = 0) :
    radE B (x + y) x 1 = radE B x 0 1 * radE B y 0 1 := by
  have hyx : B y x = 0 := by rw [hB.symm']; exact hxy
  have hm : B (x + y) x = 0 := by
    rw [map_add, LinearMap.add_apply, hB.1 x, hyx, add_zero]
  refine LinearEquiv.ext fun z => ?_
  show radE B (x + y) x 1 z = radE B x 0 1 (radE B y 0 1 z)
  rw [radE_apply hB hm, radE_one_apply hB, radE_one_apply hB]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hyx,
    mul_zero, add_zero, one_mul]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (norm := module) (B z x + B z y) • h2 • x + B z x • h2 • y

@[expose] def FourTvProd (B : LinearMap.BilinForm (ZMod 2) V) : Set (GLV V) :=
  {g | ∃ x y, x ≠ 0 ∧ y ≠ 0 ∧ g = radE B x 0 1 * radE B y 0 1}

@[expose] def FourN0 (B : LinearMap.BilinForm (ZMod 2) V) : Subgroup (GLV V) :=
  Subgroup.closure (FourTvProd B)

theorem g12f_tvProd_conj (hB : IsSymplectic B) {g : GLV V} (hg : g ∈ spSub B) {s : GLV V}
    (hs : s ∈ FourTvProd B) : g * s * g⁻¹ ∈ FourTvProd B := by
  obtain ⟨x, y, hx, hy, rfl⟩ := hs
  refine ⟨g x, g y, fun h => hx (by simpa using h), fun h => hy (by simpa using h), ?_⟩
  rw [← g12f_tv_conj hB hg x, ← g12f_tv_conj hB hg y]
  group

theorem g12f_N0_conj (hB : IsSymplectic B) {g : GLV V} (hg : g ∈ spSub B) {n : GLV V}
    (hn : n ∈ FourN0 B) : g * n * g⁻¹ ∈ FourN0 B := by
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (g12f_tvProd_conj hB hg hx)
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact (FourN0 B).mul_mem ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact (FourN0 B).inv_mem ha

theorem g12f_N0_le_commutator (hB : IsSymplectic B) : FourN0 B ≤ ⁅spSub B, spSub B⁆ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, y, hx, hy, rfl⟩
  obtain ⟨c, hcx, hcy⟩ := hB.exists_B_eq_one_one hx hy
  have hxc : B x c = 1 := by rw [hB.symm']; exact hcx
  have e : radE B x 0 1 * radE B y 0 1 =
      (radE B x 0 1 * radE B c 0 1) * (radE B c 0 1 * radE B y 0 1) := by
    rw [mul_assoc, ← mul_assoc (radE B c 0 1), g12f_tv_mul_self hB, one_mul]
  rw [e, g12f_tv_mul_eq_commutator hB hxc, g12f_tv_mul_eq_commutator hB hcy]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (g12f_tv_mem hB c)
    (g12f_tv_mem hB x)) (Subgroup.commutator_mem_commutator (g12f_tv_mem hB y)
    (g12f_tv_mem hB c))

section Fin

variable [Finite V]

theorem g12f_mem_or_mul_mem (hB : IsSymplectic B) {x0 : V} (hx0 : x0 ≠ 0) {g : GLV V}
    (hg : g ∈ spSub B) : g ∈ FourN0 B ∨ g * radE B x0 0 1 ∈ FourN0 B := by
  have ht : radE B x0 0 1 ∈ spSub B := g12f_tv_mem hB x0
  have hti : (radE B x0 0 1)⁻¹ ∈ spSub B := (spSub B).inv_mem ht
  have htt : radE B x0 0 1 * radE B x0 0 1 = 1 := g12f_tv_mul_self hB x0
  have htinv : (radE B x0 0 1)⁻¹ = radE B x0 0 1 := g12f_tv_inv hB x0
  set t := radE B x0 0 1 with ht_def
  have hg' := spSub_le_closure_tv hB hg
  clear hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    by_cases hy : y = 0
    · left
      rw [hy, g12f_tv_zero hB]
      exact (FourN0 B).one_mem
    · right
      exact Subgroup.subset_closure ⟨y, x0, hy, hx0, rfl⟩
  | one => exact Or.inl (FourN0 B).one_mem
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl ((FourN0 B).mul_mem ha hb)
    · right
      rw [mul_assoc]
      exact (FourN0 B).mul_mem ha hb
    · right
      have e : a * b * t = (a * t) * (t⁻¹ * b * t⁻¹⁻¹) := by group
      rw [e]
      exact (FourN0 B).mul_mem ha (g12f_N0_conj hB hti hb)
    · left
      have e : a * b = (a * t) * (t⁻¹ * (b * t) * t⁻¹⁻¹) := by
        rw [show (a * t) * (t⁻¹ * (b * t) * t⁻¹⁻¹) = a * b * (t * t) by group, htt, mul_one]
      rw [e]
      exact (FourN0 B).mul_mem ha (g12f_N0_conj hB hti hb)
  | inv a _ ha =>
    rcases ha with ha | ha
    · exact Or.inl ((FourN0 B).inv_mem ha)
    · right
      have e : a⁻¹ * t = t * (a * t)⁻¹ * t⁻¹ := by
        rw [show t * (a * t)⁻¹ * t⁻¹ = a⁻¹ * t⁻¹ by group, htinv]
      rw [e]
      exact g12f_N0_conj hB ht ((FourN0 B).inv_mem ha)

theorem g12f_commutator_le_N0 (hB : IsSymplectic B) {x0 : V} (hx0 : x0 ≠ 0) :
    ⁅spSub B, spSub B⁆ ≤ FourN0 B := by
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  have hti : (radE B x0 0 1)⁻¹ ∈ spSub B := (spSub B).inv_mem (g12f_tv_mem hB x0)
  set t := radE B x0 0 1 with ht_def
  rcases g12f_mem_or_mul_mem hB hx0 hg1 with h1 | h1
  · have e : ⁅g1, g2⁆ = g1 * (g2 * g1⁻¹ * g2⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (FourN0 B).mul_mem h1 (g12f_N0_conj hB hg2 ((FourN0 B).inv_mem h1))
  · rcases g12f_mem_or_mul_mem hB hx0 hg2 with h2 | h2
    · have e : ⁅g1, g2⁆ = (g1 * g2 * g1⁻¹) * g2⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact (FourN0 B).mul_mem (g12f_N0_conj hB hg1 h2) ((FourN0 B).inv_mem h2)
    · have e : ⁅g1, g2⁆ = (g1 * t) * (t⁻¹ * ((g2 * t) * (g1 * t)⁻¹) * t⁻¹⁻¹) * (g2 * t)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact (FourN0 B).mul_mem ((FourN0 B).mul_mem h1 (g12f_N0_conj hB hti
        ((FourN0 B).mul_mem h2 ((FourN0 B).inv_mem h1)))) ((FourN0 B).inv_mem h2)

theorem g12f_N0_eq_commutator (hB : IsSymplectic B) {x0 : V} (hx0 : x0 ≠ 0) :
    FourN0 B = ⁅spSub B, spSub B⁆ :=
  le_antisymm (g12f_N0_le_commutator hB) (g12f_commutator_le_N0 hB hx0)

theorem g12f_eq_commutator_of_tvProd (hB : IsSymplectic B) {Γ : Subgroup (GLV V)}
    (hΓ : Γ ≤ spSub B) {x0 : V} (hx0 : x0 ≠ 0) (ht : radE B x0 0 1 ∉ Γ)
    (hprod : FourTvProd B ⊆ Γ) : Γ = ⁅spSub B, spSub B⁆ := by
  rw [← g12f_N0_eq_commutator hB hx0]
  have hN : FourN0 B ≤ Γ := (Subgroup.closure_le _).2 hprod
  refine le_antisymm (fun g hg => ?_) hN
  rcases g12f_mem_or_mul_mem hB hx0 (hΓ hg) with h | h
  · exact h
  · exfalso
    apply ht
    have := Γ.mul_mem (Γ.inv_mem hg) (hN h)
    simpa using this

end Fin

theorem g12f_radE_self_zero (hB : IsSymplectic B) (v : V) : radE B v v 0 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  show radE B v v 0 x = x
  rw [radE_apply hB (hB.1 v)]
  simp only [zero_mul, add_zero]
  rw [add_assoc, g12_vadd_self, add_zero]

theorem g12f_radE_add_self (hB : IsSymplectic B) {v a : V} (hva : B v a = 0) (c : ZMod 2) :
    radE B v (a + v) c = radE B v a c := by
  have hav : B a v = 0 := by rw [hB.symm']; exact hva
  have h := radE_mul (c := c) (c' := 0) hB hva (hB.1 v)
  rw [g12f_radE_self_zero hB, mul_one, hav, add_zero, add_zero] at h
  exact h.symm

theorem g12f_radE_conj_iff (hB : IsSymplectic B) {Γ : Subgroup (GLV V)} (hΓ : Γ ≤ spSub B)
    {g : GLV V} (hg : g ∈ Γ) {w a : V} {c : ZMod 2} (hwa : B w a = 0) :
    radE B (g w) (g a) c ∈ Γ ↔ radE B w a c ∈ Γ := by
  refine ⟨fun h => ?_, fun h => radE_conj_mem hB hΓ hg hwa h⟩
  have hgi : ∀ x y, B (g x) (g y) = B x y := hΓ hg
  have hwa' : B (g w) (g a) = 0 := by rw [hgi]; exact hwa
  have := radE_conj_mem hB hΓ (Γ.inv_mem hg) hwa' h
  have e1 : (g⁻¹ : GLV V) (g w) = w := by simp
  have e2 : (g⁻¹ : GLV V) (g a) = a := by simp
  rwa [e1, e2] at this

theorem g12f_tv_not_mem (hB : IsSymplectic B) {Γ : Subgroup (GLV V)} (hΓ : Γ ≤ spSub B) {v : V}
    (htv : radE B v 0 1 ∉ Γ) (htr : ∀ w, w ≠ 0 → ∃ g ∈ Γ, g v = w) {w : V} (hw : w ≠ 0) :
    radE B w 0 1 ∉ Γ := by
  obtain ⟨g, hg, rfl⟩ := htr w hw
  intro h
  apply htv
  have := (g12f_radE_conj_iff hB hΓ hg (w := v) (a := 0) (c := 1) (by simp)).1
  rw [map_zero] at this
  exact this h

@[expose] def FourElliptic (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (w : V) :
    Prop :=
  ∀ a, B w a = 0 → a ≠ 0 → a ≠ w → radE B w a 1 ∈ Γ

theorem g12f_elliptic_conj (hB : IsSymplectic B) {Γ : Subgroup (GLV V)} (hΓ : Γ ≤ spSub B)
    {g : GLV V} (hg : g ∈ Γ) {w : V} : FourElliptic B Γ (g w) ↔ FourElliptic B Γ w := by
  have hgi : ∀ x y, B (g x) (g y) = B x y := hΓ hg
  constructor
  · intro h a hwa ha0 haw
    have := h (g a) (by rw [hgi]; exact hwa) (fun h0 => ha0 (by simpa using h0))
      (fun h1 => haw (g.injective h1))
    exact (g12f_radE_conj_iff hB hΓ hg hwa).1 this
  · intro h a hwa ha0 haw
    have hwa' : B w (g.symm a) = 0 := by
      rw [← hgi, LinearEquiv.apply_symm_apply]; exact hwa
    have := h (g.symm a) hwa' (fun h0 => ha0 (by simpa using h0))
      (fun h1 => haw (by rw [← h1, LinearEquiv.apply_symm_apply]))
    rw [← g12f_radE_conj_iff hB hΓ hg hwa', LinearEquiv.apply_symm_apply] at this
    exact this

section Ell

variable [Finite V]

theorem g12f_radE_symm (hB : IsSymplectic B) {Γ : Subgroup (GLV V)} (hΓ : Γ ≤ spSub B)
    {w a : V} (hw : w ≠ 0) (ha : IsStarVec B Γ a) (haw : a ≠ w) (hwa : B w a = 0)
    (hm : radE B w a 1 ∈ Γ) : radE B a w 1 ∈ Γ := by
  obtain ⟨y, hay, hwy⟩ := hB.exists_perp_one (v := a) (w := w) hw haw
  obtain ⟨c, hc⟩ := ((isStarVec_iff_rad hB hΓ).1 ha).2 y hay
  have hav : B a w = 0 := by rw [hB.symm']; exact hwa
  have hyw : B y w = 1 := by rw [hB.symm']; exact hwy
  have hya : B y a = 0 := by rw [hB.symm']; exact hay
  have h1 := radE_conj_mem hB hΓ hm hay hc
  have e1 : radE B w a 1 a = a := by
    rw [radE_apply hB hwa, hav, hB.1 a]
    simp
  have e2 : radE B w a 1 y = y + a + w := by
    rw [radE_apply hB hwa, hyw, hya]
    simp
  rw [e1, e2] at h1
  have hm2 : B a (y + a + w) = 0 := by
    rw [map_add, map_add, hay, hB.1 a, hav, add_zero, add_zero]
  have h2 := Γ.mul_mem hc h1
  rw [radE_mul hB hay hm2, g12_add_self c, zero_add] at h2
  have e3 : y + (y + a + w) = w + a := by
    rw [add_comm w a, ← add_assoc, ← add_assoc, g12_vadd_self, zero_add]
  have e4 : B y (y + a + w) = 1 := by
    rw [map_add, map_add, hB.1 y, hya, hyw]
    decide
  rw [e3, e4, g12f_radE_add_self hB hav] at h2
  exact h2

theorem g12f_eq_commutator_of_elliptic (hB : IsSymplectic B) {Γ : Subgroup (GLV V)}
    (hΓ : Γ ≤ spSub B) (hd : 4 ≤ Module.finrank (ZMod 2) V) {v : V} (hv0 : v ≠ 0)
    (htv : radE B v 0 1 ∉ Γ) (hell : ∀ w, w ≠ 0 → FourElliptic B Γ w) :
    Γ = ⁅spSub B, spSub B⁆ := by
  have horth : ∀ x y : V, x ≠ 0 → y ≠ 0 → B x y = 0 →
      radE B x 0 1 * radE B y 0 1 ∈ Γ := by
    intro x y hx hy hxy
    by_cases hxy' : x = y
    · rw [hxy', g12f_tv_mul_self hB]
      exact Γ.one_mem
    · rw [← g12f_radE_add_eq hB hxy]
      have hs0 : x + y ≠ 0 := fun h => hxy' (by
        calc x = x + (y + y) := by rw [g12_vadd_self, add_zero]
          _ = (x + y) + y := by rw [add_assoc]
          _ = y := by rw [h, zero_add])
      refine hell (x + y) hs0 x ?_ hx ?_
      · rw [map_add, LinearMap.add_apply, hB.1 x, hB.symm' y x, hxy, add_zero]
      · intro h
        apply hy
        calc y = x + x + y := by rw [g12_vadd_self, zero_add]
          _ = x + (x + y) := by rw [add_assoc]
          _ = x + x := by rw [← h]
          _ = 0 := g12_vadd_self x
  refine g12f_eq_commutator_of_tvProd hB hΓ hv0 htv ?_
  rintro _ ⟨x, y, hx, hy, rfl⟩
  rcases g12_eq_zero_or_one (B x y) with h0 | h1
  · exact horth x y hx hy h0
  · obtain ⟨c, -, hc0, hxc, hyc⟩ := g12_exists_mem_hyperplane_inter hB hd
      (hB.finrank_perp hx) hx hy
    have e : radE B x 0 1 * radE B y 0 1 =
        (radE B x 0 1 * radE B c 0 1) * (radE B c 0 1 * radE B y 0 1) := by
      rw [mul_assoc, ← mul_assoc (radE B c 0 1), g12f_tv_mul_self hB, one_mul]
    rw [e]
    have hcy : B c y = 0 := by rw [hB.symm']; exact hyc
    exact Γ.mul_mem (horth x c hx hc0 hxc) (horth c y hc0 hy hcy)

end Ell

end NoInst

end CFSG.Quasithin.G11
