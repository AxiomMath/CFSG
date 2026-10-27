module

public import CFSG.Quasithin.Background.G12FourModel
public import CFSG.Quasithin.Background.G12FourBasic

public section

namespace CFSG.Quasithin.G11

open Matrix

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Abstract

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V}

theorem g12f_elliptic_of_pair (hB : IsSymplectic B) {Γ : Subgroup (GLV V)} {w a b : V}
    (hwa : B w a = 0) (hwb : B w b = 0) (hab : B a b = 1) (ha : radE B w a 1 ∈ Γ)
    (hb : radE B w b 1 ∈ Γ)
    (hcov : ∀ x, B w x = 0 → x ≠ 0 → x ≠ w →
      x = a ∨ x = b ∨ x = a + b ∨ x = a + w ∨ x = b + w ∨ x = a + b + w) :
    FourElliptic B Γ w := by
  have hab' : radE B w (a + b) 1 ∈ Γ := by
    have := Γ.mul_mem ha hb
    rwa [radE_mul hB hwa hwb, hab, show (1 + 1 + 1 : ZMod 2) = 1 from rfl] at this
  have hwab : B w (a + b) = 0 := by rw [map_add, hwa, hwb, add_zero]
  intro x hx hx0 hxw
  rcases hcov x hx hx0 hxw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hab'
  · rw [g12f_radE_add_self hB hwa]; exact ha
  · rw [g12f_radE_add_self hB hwb]; exact hb
  · rw [g12f_radE_add_self hB hwab]; exact hab'

variable [Finite V]

theorem g12f_exists_isometry (hB : IsSymplectic B) (hd : Module.finrank (ZMod 2) V = 4)
    {v a u y : V} (hva : B v a = 0) (hvu : B v u = 1) (hvy : B v y = 0) (hau : B a u = 0)
    (hay : B a y = 1) (huy : B u y = 0) :
    ∃ φ : FourV ≃ₗ[ZMod 2] V, (∀ x z, B (φ x) (φ z) = fourB x z) ∧
      φ (fourBasisVec 0) = v ∧ φ (fourBasisVec 1) = a ∧ φ (fourBasisVec 2) = u ∧ φ (fourBasisVec 3) = y := by
  have hav : B a v = 0 := by rw [hB.symm']; exact hva
  have huv : B u v = 1 := by rw [hB.symm']; exact hvu
  have hyv : B y v = 0 := by rw [hB.symm']; exact hvy
  have hua : B u a = 0 := by rw [hB.symm']; exact hau
  have hya : B y a = 1 := by rw [hB.symm']; exact hay
  have hyu : B y u = 0 := by rw [hB.symm']; exact huy
  let f : FourV →ₗ[ZMod 2] V :=
    { toFun := fun x => x 0 • v + x 1 • a + x 2 • u + x 3 • y
      map_add' := fun x z => by simp only [Pi.add_apply, add_smul]; abel
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add] }
  have hiso : ∀ x z, B (f x) (f z) = fourB x z := by
    intro x z
    show B (x 0 • v + x 1 • a + x 2 • u + x 3 • y) (z 0 • v + z 1 • a + z 2 • u + z 3 • y) = _
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hva,
      hvu, hvy, hau, hay, huy, hav, huv, hyv, hua, hya, hyu, hB.1 v, hB.1 a, hB.1 u, hB.1 y,
      fourB_apply]
    ring
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact isSymplectic_fourB.2 x fun z => by rw [← hiso, hx, map_zero, LinearMap.zero_apply]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun, hd])).1 hinj
  have hf : ∀ x, f x = x 0 • v + x 1 • a + x 2 • u + x 3 • y := fun _ => rfl
  have h0 : f (fourBasisVec 0) = v := by rw [hf]; simp [fourBasisVec]
  have h1 : f (fourBasisVec 1) = a := by rw [hf]; simp [fourBasisVec]
  have h2 : f (fourBasisVec 2) = u := by rw [hf]; simp [fourBasisVec]
  have h3 : f (fourBasisVec 3) = y := by rw [hf]; simp [fourBasisVec]
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, hiso, h0, h1, h2, h3⟩

end Abstract

theorem fourB_fe0 : ∀ x : FourV, fourB (fourBasisVec 0) x = x 2 := by decide

theorem fourCov0 : ∀ x : FourV, fourB (fourBasisVec 0) x = 0 → x ≠ 0 → x ≠ fourBasisVec 0 →
    x = fourBasisVec 1 ∨ x = fourBasisVec 3 ∨ x = fourBasisVec 1 + fourBasisVec 3 ∨ x = fourBasisVec 1 + fourBasisVec 0 ∨ x = fourBasisVec 3 + fourBasisVec 0 ∨
      x = fourBasisVec 1 + fourBasisVec 3 + fourBasisVec 0 := by decide

theorem fourCov1 : ∀ x : FourV, fourB (fourBasisVec 1) x = 0 → x ≠ 0 → x ≠ fourBasisVec 1 →
    x = fourBasisVec 0 ∨ x = fourBasisVec 2 ∨ x = fourBasisVec 0 + fourBasisVec 2 ∨ x = fourBasisVec 0 + fourBasisVec 1 ∨ x = fourBasisVec 2 + fourBasisVec 1 ∨
      x = fourBasisVec 0 + fourBasisVec 2 + fourBasisVec 1 := by decide

theorem fourCov2 : ∀ x : FourV, fourB (fourBasisVec 2) x = 0 → x ≠ 0 → x ≠ fourBasisVec 2 →
    x = fourBasisVec 3 ∨ x = fourBasisVec 1 ∨ x = fourBasisVec 3 + fourBasisVec 1 ∨ x = fourBasisVec 3 + fourBasisVec 2 ∨ x = fourBasisVec 1 + fourBasisVec 2 ∨
      x = fourBasisVec 3 + fourBasisVec 1 + fourBasisVec 2 := by decide

@[expose] def fourSW (w : FourV) : List (Fin 4) :=
  if w = ![0, 0, 0, 1] then [0, 2, 1, 2] else if w = ![0, 0, 1, 0] then [0, 3, 1, 2] else
  if w = ![0, 0, 1, 1] then [3, 0, 3, 0, 2] else if w = ![0, 1, 0, 0] then [1, 3] else
  if w = ![0, 1, 0, 1] then [0, 3, 2] else if w = ![0, 1, 1, 0] then [1, 0, 2] else
  if w = ![0, 1, 1, 1] then [3, 0, 3, 2] else if w = ![1, 0, 0, 1] then [3, 0, 2] else
  if w = ![1, 0, 1, 0] then [1, 2] else if w = ![1, 0, 1, 1] then [2] else
  if w = ![1, 1, 0, 0] then [3] else if w = ![1, 1, 0, 1] then [3, 2] else
  if w = ![1, 1, 1, 0] then [2, 0, 2] else if w = ![1, 1, 1, 1] then [0, 2] else []

theorem fourSW_spec : ∀ w : FourV, w ≠ 0 → fourWordM (fourSW w) *ᵥ fourBasisVec 0 = w := by decide

@[expose] def fourKW (y1 y3 : FourV) : List (Fin 4) :=
  if y1 = ![0, 1, 0, 0] then
    (if y3 = ![1, 0, 0, 1] then [0] else if y3 = ![0, 1, 0, 1] then [3, 0, 3] else
      if y3 = ![1, 1, 0, 1] then [3, 0, 3, 0] else [])
  else
    (if y3 = ![1, 0, 0, 1] then [1, 0] else if y3 = ![0, 1, 0, 1] then [3, 0, 3, 1] else
      if y3 = ![1, 1, 0, 1] then [1, 3, 0, 3] else [1])

set_option synthInstance.maxSize 4096 in
theorem fourKW_spec : ∀ y1 : FourV, (y1 = fourBasisVec 1 ∨ y1 = fourBasisVec 1 + fourBasisVec 0) → ∀ y3 : FourV,
    fourB (fourBasisVec 0) y3 = 0 → y3 ≠ 0 → y3 ≠ fourBasisVec 0 → y3 ≠ fourBasisVec 1 → y3 ≠ fourBasisVec 1 + fourBasisVec 0 →
    fourWordM (fourKW y1 y3) *ᵥ fourBasisVec 0 = fourBasisVec 0 ∧ fourWordM (fourKW y1 y3) *ᵥ fourBasisVec 1 = y1 ∧
      fourWordM (fourKW y1 y3) *ᵥ fourBasisVec 3 = y3 := by decide

theorem g12f_mem_fourM0_aux {Γ : Subgroup (GLV FourV)} (hΓ : Γ ≤ spSub fourB)
    (ht0 : radE fourB (fourBasisVec 0) 0 1 ∉ Γ) (hm1 : radE fourB (fourBasisVec 0) (fourBasisVec 1) 1 ∈ Γ)
    (g1 : radE fourB (fourBasisVec 0) (fourBasisVec 3) 0 ∈ Γ) (hM : fourM0 ≤ Γ) {g : GLV FourV} (hg : g ∈ Γ) :
    g ∈ fourM0 := by
  have hB := isSymplectic_fourB
  have hw0 : g (fourBasisVec 0) ≠ 0 := (LinearEquiv.map_ne_zero_iff g).2 (by decide)
  obtain ⟨s, hsM, hs⟩ : ∃ s ∈ fourM0, s (fourBasisVec 0) = g (fourBasisVec 0) :=
    ⟨fourWord (fourSW (g (fourBasisVec 0))), fourWord_mem fourGen_mem _, by
      rw [fourWord_apply]; exact fourSW_spec _ hw0⟩
  obtain ⟨h, hΓh, hh0, rfl⟩ : ∃ h ∈ Γ, h (fourBasisVec 0) = fourBasisVec 0 ∧ s * h = g := by
    refine ⟨s⁻¹ * g, Γ.mul_mem (Γ.inv_mem (hM hsM)) hg, ?_, by group⟩
    show s.symm (g (fourBasisVec 0)) = fourBasisVec 0
    rw [← hs, LinearEquiv.symm_apply_apply]
  refine fourM0.mul_mem hsM ?_
  have hhS : ∀ x y, fourB (h x) (h y) = fourB x y := hΓ hΓh
  have u13 : radE fourB (fourBasisVec 0) (fourBasisVec 1 + fourBasisVec 3) 0 ∈ Γ := by
    have := Γ.mul_mem hm1 g1
    rwa [radE_mul hB (by decide) (by decide),
      show (1 + 0 + fourB (fourBasisVec 1) (fourBasisVec 3) : ZMod 2) = 0 by decide] at this
  have hun : ∀ x, fourB (fourBasisVec 0) x = 0 → radE fourB (fourBasisVec 0) x 0 ∈ Γ → radE fourB (fourBasisVec 0) x 1 ∉ Γ :=
    fun x hx h0 h1 => absurd (radE_unique hB hx ht0 h1 h0) (by decide)
  have hm1' : radE fourB (fourBasisVec 0) (h (fourBasisVec 1)) 1 ∈ Γ := by
    have := radE_conj_mem hB hΓ hΓh (by decide : fourB (fourBasisVec 0) (fourBasisVec 1) = 0) hm1
    rwa [hh0] at this
  have hb1 : fourB (fourBasisVec 0) (h (fourBasisVec 1)) = 0 := by rw [← hh0, hhS]; decide
  have hn1 : h (fourBasisVec 1) ≠ 0 := (LinearEquiv.map_ne_zero_iff h).2 (by decide)
  have hn1' : h (fourBasisVec 1) ≠ fourBasisVec 0 := fun e => absurd (h.injective (e.trans hh0.symm)) (by decide)
  have hy1 : h (fourBasisVec 1) = fourBasisVec 1 ∨ h (fourBasisVec 1) = fourBasisVec 1 + fourBasisVec 0 := by
    rcases fourCov0 _ hb1 hn1 hn1' with e | e | e | e | e | e
    · exact Or.inl e
    · rw [e] at hm1'; exact absurd hm1' (hun _ (by decide) g1)
    · rw [e] at hm1'; exact absurd hm1' (hun _ (by decide) u13)
    · exact Or.inr e
    · rw [e, g12f_radE_add_self hB (by decide)] at hm1'; exact absurd hm1' (hun _ (by decide) g1)
    · rw [e, g12f_radE_add_self hB (by decide)] at hm1'
      exact absurd hm1' (hun _ (by decide) u13)
  have hb3 : fourB (fourBasisVec 0) (h (fourBasisVec 3)) = 0 := by rw [← hh0, hhS]; decide
  have hn3 : h (fourBasisVec 3) ≠ 0 := (LinearEquiv.map_ne_zero_iff h).2 (by decide)
  have hn30 : h (fourBasisVec 3) ≠ fourBasisVec 0 := fun e => absurd (h.injective (e.trans hh0.symm)) (by decide)
  have h10 : h (fourBasisVec 1 + fourBasisVec 0) = h (fourBasisVec 1) + fourBasisVec 0 := by rw [map_add, hh0]
  have hne1 : h (fourBasisVec 3) ≠ h (fourBasisVec 1) := fun e => absurd (h.injective e) (by decide)
  have hne2 : h (fourBasisVec 3) ≠ h (fourBasisVec 1 + fourBasisVec 0) := fun e => absurd (h.injective e) (by decide)
  have hn31 : h (fourBasisVec 3) ≠ fourBasisVec 1 ∧ h (fourBasisVec 3) ≠ fourBasisVec 1 + fourBasisVec 0 := by
    rcases hy1 with e | e
    · refine ⟨fun e' => hne1 (e'.trans e.symm), fun e' => hne2 ?_⟩
      rw [h10, e]; exact e'
    · refine ⟨fun e' => hne2 ?_, fun e' => hne1 (e'.trans e.symm)⟩
      rw [h10, e, add_assoc, g12_vadd_self, add_zero]; exact e'
  obtain ⟨k0, k1, k3⟩ := fourKW_spec _ hy1 _ hb3 hn3 hn30 hn31.1 hn31.2
  obtain ⟨k, hkM, hk0, hk1, hk3⟩ : ∃ k ∈ fourM0, k (fourBasisVec 0) = fourBasisVec 0 ∧ k (fourBasisVec 1) = h (fourBasisVec 1) ∧
      k (fourBasisVec 3) = h (fourBasisVec 3) :=
    ⟨fourWord (fourKW (h (fourBasisVec 1)) (h (fourBasisVec 3))), fourWord_mem fourGen_mem _,
      by rw [fourWord_apply]; exact k0, by rw [fourWord_apply]; exact k1,
      by rw [fourWord_apply]; exact k3⟩
  have hr : k⁻¹ * h ∈ Γ := Γ.mul_mem (Γ.inv_mem (hM hkM)) hΓh
  have hf : ∀ i : Fin 4, h (fourBasisVec i) = k (fourBasisVec i) → (k⁻¹ * h) (fourBasisVec i) = fourBasisVec i := fun i e => by
    show k.symm (h (fourBasisVec i)) = fourBasisVec i
    rw [e, LinearEquiv.symm_apply_apply]
  have hfix : ∀ u ∈ perp fourB (fourBasisVec 0), (k⁻¹ * h) u = u + fourB u 0 • fourBasisVec 0 := by
    intro u hu
    rw [map_zero, zero_smul, add_zero]
    have hu2 : u 2 = 0 := by rw [← fourB_fe0 u]; exact mem_perp_iff.1 hu
    have hdec : u = u 0 • fourBasisVec 0 + u 1 • fourBasisVec 1 + u 3 • fourBasisVec 3 := by
      funext i
      fin_cases i <;> simp [fourBasisVec, hu2]
    rw [hdec, map_add, map_add, map_smul, map_smul, map_smul, hf 0 (hh0.trans hk0.symm),
      hf 1 hk1.symm, hf 3 hk3.symm]
  obtain ⟨c, hc⟩ := eq_radE_of_fix hB (by simp) (hΓ hr) hfix
  rcases g12_eq_zero_or_one c with rfl | rfl
  · have h1 : k⁻¹ * h = 1 := by rw [hc, radE_zero_zero hB]
    have e : h = k := by
      calc h = k * (k⁻¹ * h) := by group
        _ = k := by rw [h1, mul_one]
    rw [e]
    exact hkM
  · exact absurd (hc ▸ hr) ht0

theorem g12f_eq_fourM0 {Γ : Subgroup (GLV FourV)} (hΓ : Γ ≤ spSub fourB)
    (hs0 : IsStarVec fourB Γ (fourBasisVec 0)) (hs2 : IsStarVec fourB Γ (fourBasisVec 2))
    (ht0 : radE fourB (fourBasisVec 0) 0 1 ∉ Γ)
    (hy0 : ¬ FourElliptic fourB Γ (fourBasisVec 0)) (hy2 : ¬ FourElliptic fourB Γ (fourBasisVec 2))
    (hm1 : radE fourB (fourBasisVec 0) (fourBasisVec 1) 1 ∈ Γ) (hm2 : radE fourB (fourBasisVec 2) (fourBasisVec 3) 1 ∈ Γ) :
    Γ = fourM0 := by
  have hB := isSymplectic_fourB
  have g1 : radE fourB (fourBasisVec 0) (fourBasisVec 3) 0 ∈ Γ := by
    obtain ⟨c, hc⟩ := ((isStarVec_iff_rad hB hΓ).1 hs0).2 (fourBasisVec 3) (by decide)
    rcases g12_eq_zero_or_one c with rfl | rfl
    · exact hc
    · exact absurd (g12f_elliptic_of_pair hB (by decide) (by decide) (by decide) hm1 hc
        fourCov0) hy0
  have g3 : radE fourB (fourBasisVec 2) (fourBasisVec 1) 0 ∈ Γ := by
    obtain ⟨c, hc⟩ := ((isStarVec_iff_rad hB hΓ).1 hs2).2 (fourBasisVec 1) (by decide)
    rcases g12_eq_zero_or_one c with rfl | rfl
    · exact hc
    · exact absurd (g12f_elliptic_of_pair hB (by decide) (by decide) (by decide) hm2 hc
        fourCov2) hy2
  have hgen : ∀ k, fourGen k ∈ Γ := by
    intro k
    fin_cases k
    · exact hm1
    · exact g1
    · exact hm2
    · exact g3
  have hM : fourM0 ≤ Γ := (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact hgen k)
  exact le_antisymm (fun g hg => g12f_mem_fourM0_aux hΓ ht0 hm1 g1 hM hg) hM

theorem g12f_false_of_marked {Γ : Subgroup (GLV FourV)} (hΓ : Γ ≤ spSub fourB)
    (hs1 : IsStarVec fourB Γ (fourBasisVec 1)) (hy1 : ¬ FourElliptic fourB Γ (fourBasisVec 1))
    (hm1 : radE fourB (fourBasisVec 0) (fourBasisVec 1) 1 ∈ Γ) (hm3 : radE fourB (fourBasisVec 2) (fourBasisVec 1) 1 ∈ Γ) : False := by
  have hB := isSymplectic_fourB
  have a1 := g12f_radE_symm hB hΓ (w := fourBasisVec 0) (a := fourBasisVec 1) (by decide) hs1 (by decide)
    (by decide) hm1
  have a2 := g12f_radE_symm hB hΓ (w := fourBasisVec 2) (a := fourBasisVec 1) (by decide) hs1 (by decide)
    (by decide) hm3
  exact hy1 (g12f_elliptic_of_pair hB (by decide) (by decide) (by decide) a1 a2 fourCov1)

end NoInst

end CFSG.Quasithin.G11
