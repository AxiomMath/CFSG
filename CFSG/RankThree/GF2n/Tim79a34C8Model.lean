module

public import CFSG.RankThree.GF2n.Tim79a34SpRad

public section

namespace CFSG.RankThree.GF2n.Tim79a

open scoped Matrix commutatorElement
open CFSG CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic

theorem c8_zero_or_one {F : Type} [Field F] [CharP F 2] (hF : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr ((hy c hc).trans (hy 1 one_ne_zero).symm)

theorem c8_exists_far {n : ℕ} {F : Type} [Field F] [CharP F 2] (hn : 3 ≤ n)
    {a x : Fin n ⊕ Fin n → F} (ha : a ≠ 0) (hax : spForm a x = 0) (hxa : ∀ c : F, x ≠ c • a) :
    ∃ w, spForm a w = 0 ∧ spForm x w = 0 ∧ ∀ c d : F, w ≠ c • a + d • x := by
  obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
  obtain ⟨y, hay, hxy⟩ := exists_dual ha hax hxa
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : Fin n ⊕ Fin n → F, b₁ = b + spForm x b • y := ⟨_, rfl⟩
  have hab₁ : spForm a b₁ = 1 := by
    rw [hb₁, spForm_add_right, spForm_smul_right', hay, mul_zero, add_zero, hb]
  have hxb₁ : spForm x b₁ = 0 := by
    rw [hb₁, spForm_add_right, spForm_smul_right', hxy, mul_one, CharTwo.add_self_eq_zero]
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, x, b₁, y]
    (by rw [Fintype.card_fin]; omega)
  have hwa : spForm a w = 0 := hw 0
  have hwx : spForm x w = 0 := hw 1
  have hwb : spForm b₁ w = 0 := hw 2
  have hwy : spForm y w = 0 := hw 3
  refine ⟨w, hwa, hwx, fun c d hcd => hw0 ?_⟩
  have e1 : spForm b₁ w = -c := by
    rw [hcd, spForm_add_right, spForm_smul_right', spForm_smul_right', spForm_comm a b₁,
      spForm_comm x b₁, hab₁, hxb₁]
    ring
  have e2 : spForm y w = -d := by
    rw [hcd, spForm_add_right, spForm_smul_right', spForm_smul_right', spForm_comm a y,
      spForm_comm x y, hay, hxy]
    ring
  have hc : c = 0 := neg_eq_zero.1 (e1.symm.trans hwb)
  have hd : d = 0 := neg_eq_zero.1 (e2.symm.trans hwy)
  simp [hcd, hc, hd]

theorem c8_exists_common_dual {n : ℕ} {F : Type} [Field F] [CharP F 2] (hF : Nat.card F = 2)
    {a x y : Fin n ⊕ Fin n → F} (ha : a ≠ 0) (hax : spForm a x = 0) (hxa : ∀ c : F, x ≠ c • a)
    (hay : spForm a y = 0) (hya : ∀ c : F, y ≠ c • a) :
    ∃ z, spForm a z = 0 ∧ spForm x z = 1 ∧ spForm y z = 1 := by
  obtain ⟨z₁, haz₁, hxz₁⟩ := exists_dual ha hax hxa
  obtain ⟨z₂, haz₂, hyz₂⟩ := exists_dual ha hay hya
  rcases c8_zero_or_one hF (spForm y z₁) with h1 | h1
  · rcases c8_zero_or_one hF (spForm x z₂) with h2 | h2
    · refine ⟨z₁ + z₂, ?_, ?_, ?_⟩
      · rw [spForm_add_right, haz₁, haz₂, add_zero]
      · rw [spForm_add_right, hxz₁, h2, add_zero]
      · rw [spForm_add_right, h1, hyz₂, zero_add]
    · exact ⟨z₂, haz₂, h2, hyz₂⟩
  · exact ⟨z₁, haz₁, hxz₁, h1⟩

theorem c8_no_const_quad {n : ℕ} {F : Type} [Field F] [CharP F 2] (hn : 3 ≤ n)
    (hF : Nat.card F = 2) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) (s : (Fin n ⊕ Fin n → F) → F)
    (c : F)
    (hs : ∀ x y, spForm a x = 0 → spForm a y = 0 → s (x + y) = s x + s y + spForm x y)
    (hconst : ∀ x, spForm a x = 0 → (∀ l : F, x ≠ l • a) → s x = c) : False := by
  obtain ⟨u, -, hau, hua⟩ := exists_perp_vec_not_smul (by omega : 2 ≤ n) ha
  obtain ⟨v, hav, huv⟩ := exists_dual ha hau hua
  obtain ⟨w, haw, huw, hwcd⟩ := c8_exists_far hn ha hau hua
  have hua0 : spForm u a = 0 := by rw [spForm_comm a u, hau, neg_zero]
  have hva : ∀ l : F, v ≠ l • a := by
    intro l hl
    rw [hl, spForm_smul_right', hua0, mul_zero] at huv
    exact zero_ne_one huv
  have hwa : ∀ l : F, w ≠ l • a := fun l hl => hwcd l 0 (by rw [hl, zero_smul, add_zero])
  have huaw : ∀ l : F, u + w ≠ l • a := by
    intro l hl
    exact hwcd l 1 (by linear_combination (norm := module) hl - vec_add_self u)
  have huav : ∀ l : F, u + v ≠ l • a := by
    intro l hl
    have h1 : spForm u (u + v) = 1 := by
      rw [spForm_add_right, spForm_self, huv, zero_add]
    rw [hl, spForm_smul_right', hua0, mul_zero] at h1
    exact zero_ne_one h1
  have hauw : spForm a (u + w) = 0 := by rw [spForm_add_right, hau, haw, add_zero]
  have hauv : spForm a (u + v) = 0 := by rw [spForm_add_right, hau, hav, add_zero]
  have hA := hconst u hau hua
  have hB := hconst w haw hwa
  have hC := hconst (u + w) hauw huaw
  have hD := hconst v hav hva
  have hE := hconst (u + v) hauv huav
  have hsuw := hs u w hau haw
  have hsuv := hs u v hau hav
  have hc0 : c = 0 := by linear_combination hC - hsuw - huw - hA - hB
  exact one_ne_zero (by linear_combination hE - hsuv - huv - hA - hD - hc0 : (1 : F) = 0)

@[expose] def C8Cong {n : ℕ} {F : Type} [Field F] (a x y : Fin n ⊕ Fin n → F) : Prop :=
  ∃ c : F, x = y + c • a

theorem C8Cong.refl {n : ℕ} {F : Type} [Field F] (a x : Fin n ⊕ Fin n → F) : C8Cong a x x :=
  ⟨0, by simp⟩

theorem C8Cong.symm {n : ℕ} {F : Type} [Field F] [CharP F 2] {a x y : Fin n ⊕ Fin n → F}
    (h : C8Cong a x y) : C8Cong a y x := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [hc, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem C8Cong.trans {n : ℕ} {F : Type} [Field F] {a x y z : Fin n ⊕ Fin n → F}
    (h₁ : C8Cong a x y) (h₂ : C8Cong a y z) : C8Cong a x z := by
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  refine ⟨c + d, ?_⟩
  rw [hc, hd, add_smul]
  abel

theorem C8Cong.add {n : ℕ} {F : Type} [Field F] {a x y x' y' : Fin n ⊕ Fin n → F}
    (h₁ : C8Cong a x y) (h₂ : C8Cong a x' y') : C8Cong a (x + x') (y + y') := by
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  refine ⟨c + d, ?_⟩
  rw [hc, hd, add_smul]
  abel

theorem c8_spForm_comm_char2 {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u v : Fin n ⊕ Fin n → F) : spForm v u = spForm u v := by
  rw [spForm_comm, CharTwo.neg_eq]

section Helpers

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem c8_cong_mulVec {a x y : Fin n ⊕ Fin n → F}
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (hM : M *ᵥ a = a) (h : C8Cong a x y) :
    C8Cong a (M *ᵥ x) (M *ᵥ y) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_smul, hM]

theorem c8_gam_apply (x y u : Fin n ⊕ Fin n → F) :
    (spTrans x 1 * spTrans y 1) *ᵥ u =
      u + spForm y u • y + (spForm x u + spForm y u * spForm x y) • x := by
  rw [← Matrix.mulVec_mulVec]
  simp only [spTrans_mulVec, spForm_add_right, spForm_smul_right', one_mul]

theorem c8_gam_x {x y : Fin n ⊕ Fin n → F} (hxy : spForm x y = 1) :
    (spTrans x 1 * spTrans y 1) *ᵥ x = y := by
  have hyx : spForm y x = 1 := by rw [c8_spForm_comm_char2, hxy]
  rw [c8_gam_apply, hyx, hxy, spForm_self]
  linear_combination (norm := module) vec_add_self x

theorem c8_gam_y {x y : Fin n ⊕ Fin n → F} (hxy : spForm x y = 1) :
    (spTrans x 1 * spTrans y 1) *ᵥ y = x + y := by
  rw [c8_gam_apply, spForm_self, hxy]
  module

theorem c8_gam_a {a x y : Fin n ⊕ Fin n → F} (hax : spForm a x = 0) (hay : spForm a y = 0) :
    (spTrans x 1 * spTrans y 1) *ᵥ a = a := by
  rw [c8_gam_apply, spForm_eq_zero_comm hax, spForm_eq_zero_comm hay]
  simp

theorem c8_cycle {x y : Fin n ⊕ Fin n → F} (hxy : spForm x y = 1) (p : Fin n ⊕ Fin n → F) :
    p + (spTrans x 1 * spTrans y 1) *ᵥ p +
        (spTrans x 1 * spTrans y 1) *ᵥ ((spTrans x 1 * spTrans y 1) *ᵥ p) =
      p + spForm x p • y + spForm y p • x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hyx : spForm y x = 1 := by rw [c8_spForm_comm_char2, hxy]
  have hq : (spTrans x 1 * spTrans y 1) *ᵥ p =
      p + spForm y p • y + (spForm x p + spForm y p) • x := by
    rw [c8_gam_apply, hxy, mul_one]
  set q := (spTrans x 1 * spTrans y 1) *ᵥ p with hqdef
  have e1 : spForm y q = spForm x p := by
    rw [hq]
    simp only [spForm_add_right, spForm_smul_right', spForm_self, hyx, mul_zero, zero_add,
      mul_one, add_zero]
    linear_combination (spForm y p) * h2
  have e2 : spForm x q + spForm y q * spForm x y = spForm y p := by
    rw [e1, hxy, mul_one, hq]
    simp only [spForm_add_right, spForm_smul_right', spForm_self, hxy, mul_zero, zero_add,
      mul_one, add_zero]
    linear_combination (spForm x p) * h2
  rw [c8_gam_apply x y q, e2, e1]
  linear_combination (norm := module) vec_add_self q

theorem c8_cycle_cong (φ : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F)) {a x y : Fin n ⊕ Fin n → F}
    (hφadd : ∀ u u', spForm a u = 0 → spForm a u' = 0 → C8Cong a (φ (u + u')) (φ u + φ u'))
    (hφγ : ∀ x y, spForm a x = 0 → spForm a y = 0 → spForm x y = 1 → ∀ u, spForm a u = 0 →
      C8Cong a (φ ((spTrans x 1 * spTrans y 1) *ᵥ u)) ((spTrans x 1 * spTrans y 1) *ᵥ φ u))
    (hax : spForm a x = 0) (hay : spForm a y = 0) (hxy : spForm x y = 1) :
    C8Cong a (φ x) (spForm x (φ x) • y + spForm y (φ x) • x) := by
  have hγa := c8_gam_a hax hay
  have h1 : C8Cong a (φ y) ((spTrans x 1 * spTrans y 1) *ᵥ φ x) := by
    have h := hφγ x y hax hay hxy x hax
    rwa [c8_gam_x hxy] at h
  have h2 : C8Cong a (φ (x + y)) ((spTrans x 1 * spTrans y 1) *ᵥ φ y) := by
    have h := hφγ x y hax hay hxy y hay
    rwa [c8_gam_y hxy] at h
  have h3 : C8Cong a ((spTrans x 1 * spTrans y 1) *ᵥ φ y)
      ((spTrans x 1 * spTrans y 1) *ᵥ ((spTrans x 1 * spTrans y 1) *ᵥ φ x)) :=
    c8_cong_mulVec _ hγa h1
  have h4 : C8Cong a (φ (x + y)) (φ x + φ y) := hφadd x y hax hay
  have h5 : C8Cong a (φ x + φ y) (φ x + (spTrans x 1 * spTrans y 1) *ᵥ φ x) :=
    C8Cong.add (C8Cong.refl a _) h1
  have h6 : C8Cong a ((spTrans x 1 * spTrans y 1) *ᵥ ((spTrans x 1 * spTrans y 1) *ᵥ φ x))
      (φ x + (spTrans x 1 * spTrans y 1) *ᵥ φ x) :=
    C8Cong.trans (C8Cong.symm (C8Cong.trans h2 h3)) (C8Cong.trans h4 h5)
  obtain ⟨c, hc⟩ := h6
  refine ⟨c, ?_⟩
  have hcyc := c8_cycle hxy (φ x)
  linear_combination (norm := module)
    hcyc - hc - vec_add_self ((spTrans x 1 * spTrans y 1) *ᵥ φ x + c • a)

theorem c8_perp_scalar (φ : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F))
    {a x : Fin n ⊕ Fin n → F} (hn : 3 ≤ n) (ha : a ≠ 0) (hax : spForm a x = 0)
    (hxa : ∀ c : F, x ≠ c • a)
    (hφadd : ∀ u u', spForm a u = 0 → spForm a u' = 0 → C8Cong a (φ (u + u')) (φ u + φ u'))
    (hφγ : ∀ x y, spForm a x = 0 → spForm a y = 0 → spForm x y = 1 → ∀ u, spForm a u = 0 →
      C8Cong a (φ ((spTrans x 1 * spTrans y 1) *ᵥ u)) ((spTrans x 1 * spTrans y 1) *ᵥ φ u)) :
    ∃ β : F, C8Cong a (φ x) (β • x) := by
  obtain ⟨y, hay, hxy⟩ := exists_dual ha hax hxa
  obtain ⟨w, haw, hxw, hw⟩ := c8_exists_far hn ha hax hxa
  have hxy' : spForm x (y + w) = 1 := by rw [spForm_add_right, hxy, hxw, add_zero]
  have hay' : spForm a (y + w) = 0 := by rw [spForm_add_right, hay, haw, add_zero]
  obtain ⟨c, hc⟩ := c8_cycle_cong φ hφadd hφγ hax hay hxy
  obtain ⟨c', hc'⟩ := c8_cycle_cong φ hφadd hφγ hax hay' hxy'
  have hα : spForm x (φ x) = 0 := by
    by_contra hα
    have hvec : spForm x (φ x) • w =
        (spForm y (φ x) - spForm (y + w) (φ x)) • x + (c - c') • a := by
      linear_combination (norm := module) hc - hc'
    have hw_eq : w = (spForm x (φ x))⁻¹ •
        ((spForm y (φ x) - spForm (y + w) (φ x)) • x + (c - c') • a) := by
      rw [← hvec]
      exact (inv_smul_smul₀ hα w).symm
    apply hw ((spForm x (φ x))⁻¹ * (c - c'))
      ((spForm x (φ x))⁻¹ * (spForm y (φ x) - spForm (y + w) (φ x)))
    refine hw_eq.trans ?_
    module
  refine ⟨spForm y (φ x), c, ?_⟩
  rw [hα, zero_smul, zero_add] at hc
  exact hc

end Helpers

theorem c8_schur {n : ℕ} {F : Type} [Field F] [CharP F 2] (hn : 3 ≤ n)
    (hF : Nat.card F = 2)
    {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) (φ : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F))
    (hφE : ∀ u, spForm a u = 0 → spForm a (φ u) = 0)
    (hφadd : ∀ u u', spForm a u = 0 → spForm a u' = 0 → C8Cong a (φ (u + u')) (φ u + φ u'))
    (hφa : C8Cong a (φ a) 0)
    (hφγ : ∀ x y, spForm a x = 0 → spForm a y = 0 → spForm x y = 1 → ∀ u, spForm a u = 0 →
      C8Cong a (φ ((spTrans x 1 * spTrans y 1) *ᵥ u)) ((spTrans x 1 * spTrans y 1) *ᵥ φ u)) :
    (∀ u, spForm a u = 0 → C8Cong a (φ u) 0) ∨ (∀ u, spForm a u = 0 → C8Cong a (φ u) u) := by
  have hz : ∀ c : F, c = 0 ∨ c = 1 := c8_zero_or_one hF
  have hperp0 : spForm a (0 : Fin n ⊕ Fin n → F) = 0 := spForm_zero_right a
  have hφ0 : C8Cong a (φ 0) 0 := by
    have h := hφadd 0 0 hperp0 hperp0
    rw [add_zero] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    linear_combination (norm := module) hc + vec_add_self (φ 0)
  have hφc : ∀ c : F, C8Cong a (φ (c • a)) 0 := by
    intro c
    rcases hz c with rfl | rfl
    · rw [zero_smul]
      exact hφ0
    · rw [one_smul]
      exact hφa
  have hperp_smul : ∀ c : F, spForm a (c • a) = 0 := fun c => by
    rw [spForm_smul_right', spForm_self, mul_zero]
  have hdich : ∀ x : Fin n ⊕ Fin n → F, spForm a x = 0 → (∀ c : F, x ≠ c • a) →
      C8Cong a (φ x) 0 ∨ C8Cong a (φ x) x := by
    intro x hx hxF
    obtain ⟨β, hβ⟩ := c8_perp_scalar φ hn ha hx hxF hφadd hφγ
    rcases hz β with rfl | rfl
    · rw [zero_smul] at hβ
      exact Or.inl hβ
    · rw [one_smul] at hβ
      exact Or.inr hβ
  by_cases hcase : ∀ u, spForm a u = 0 → C8Cong a (φ u) 0
  · exact Or.inl hcase
  · right
    push Not at hcase
    obtain ⟨x₀, hx₀a, hx₀⟩ := hcase
    have hx₀F : ∀ c : F, x₀ ≠ c • a := fun c h => hx₀ (by rw [h]; exact hφc c)
    have hx₀φ : C8Cong a (φ x₀) x₀ := (hdich x₀ hx₀a hx₀F).resolve_left hx₀
    intro u hua
    by_cases hu : ∃ c : F, u = c • a
    · obtain ⟨c, rfl⟩ := hu
      exact C8Cong.trans (hφc c) (C8Cong.symm (Exists.intro c (by rw [zero_add])))
    · push Not at hu
      rcases hdich u hua hu with h0 | h1
      · exfalso
        have hz0 : spForm a (x₀ + u) = 0 := by
          rw [spForm_add_right, hx₀a, hua, add_zero]
        have hφz : C8Cong a (φ (x₀ + u)) x₀ := by
          have h := C8Cong.add hx₀φ h0
          rw [add_zero] at h
          exact C8Cong.trans (hφadd x₀ u hx₀a hua) h
        by_cases hzF : ∃ c : F, x₀ + u = c • a
        · obtain ⟨c, hc⟩ := hzF
          have hu' : u = x₀ + c • a := by
            linear_combination (norm := module) hc - vec_add_self x₀
          have hφu : C8Cong a (φ u) (φ x₀ + φ (c • a)) := by
            have h := hφadd x₀ (c • a) hx₀a (hperp_smul c)
            rw [← hu'] at h
            exact h
          have h' : C8Cong a (φ x₀ + φ (c • a)) x₀ := by
            have h'' := C8Cong.add hx₀φ (hφc c)
            rw [add_zero] at h''
            exact h''
          have hx00 : C8Cong a x₀ 0 := C8Cong.trans (C8Cong.symm (C8Cong.trans hφu h')) h0
          obtain ⟨d, hd⟩ := hx00
          exact hx₀F d (by rw [hd, zero_add])
        · push Not at hzF
          rcases hdich (x₀ + u) hz0 hzF with hz1 | hz2
          · have hx00 : C8Cong a x₀ 0 := C8Cong.trans (C8Cong.symm hφz) hz1
            obtain ⟨d, hd⟩ := hx00
            exact hx₀F d (by rw [hd, zero_add])
          · have hx2 : C8Cong a x₀ (x₀ + u) := C8Cong.trans (C8Cong.symm hφz) hz2
            obtain ⟨d, hd⟩ := hx2
            apply hu (-d)
            linear_combination (norm := module) -hd
      · exact h1

private theorem c8_mat_inv_eq {n : ℕ} {F : Type} [Field F] {g : StatedSp n F}
    {T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hg : SpExtras.mat n F g = T)
    (hT : T * T = 1) : SpExtras.mat n F g⁻¹ = T := by
  have h1 : T * SpExtras.mat n F g⁻¹ = 1 := by
    rw [← hg, ← map_mul, mul_inv_cancel, map_one]
  calc SpExtras.mat n F g⁻¹ = (T * T) * SpExtras.mat n F g⁻¹ := by rw [hT, one_mul]
    _ = T * (T * SpExtras.mat n F g⁻¹) := by rw [mul_assoc]
    _ = T := by rw [h1, mul_one]

private theorem c8_conj_transvection {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {x y : Fin n ⊕ Fin n → F} (hxy : spForm x y = 1) :
    spTrans (x + y) 1 * (spTrans x 1 * spTrans (x + y) 1) = spTrans y 1 := by
  have hyx : spForm y x = -1 := by rw [spForm_comm, hxy]
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [spTrans_mulVec, one_mul, spForm_add_left, spForm_add_right, spForm_smul_left',
    spForm_smul_right', spForm_self, hxy, hyx]
  linear_combination (norm := module) (spForm x v + spForm y v) • two_smul_vec_eq_zero x

theorem c8_commutator_lift {n : ℕ} {F : Type} [Field F] [CharP F 2] {a x y : Fin n ⊕ Fin n → F}
    (hax : spForm a x = 0) (hay : spForm a y = 0) (hxy : spForm x y = 1) :
    ∃ g₁ g₂ : StatedSp n F, SpExtras.mat n F g₁ = spTrans x 1 ∧
      SpExtras.mat n F g₂ = spTrans (x + y) 1 ∧
      SpExtras.mat n F g₁ *ᵥ a = a ∧ SpExtras.mat n F g₂ *ᵥ a = a ∧
      SpExtras.mat n F ⁅g₁, g₂⁆ = spTrans x 1 * spTrans y 1 := by
  obtain ⟨g₁, hg₁⟩ := exists_mat_eq_spTrans x 1
  obtain ⟨g₂, hg₂⟩ := exists_mat_eq_spTrans (x + y) 1
  have hT₁ : spTrans x 1 * spTrans x 1 = 1 := by
    rw [spTrans_mul_spTrans, one_add_one_eq_two, CharTwo.two_eq_zero, spTrans_zero]
  have hT₂ : spTrans (x + y) 1 * spTrans (x + y) 1 = 1 := by
    rw [spTrans_mul_spTrans, one_add_one_eq_two, CharTwo.two_eq_zero, spTrans_zero]
  refine ⟨g₁, g₂, hg₁, hg₂, ?_, ?_, ?_⟩
  · rw [hg₁, spTrans_mulVec, spForm_eq_zero_comm hax, mul_zero, zero_smul, add_zero]
  · rw [hg₂, spTrans_mulVec, spForm_add_left, spForm_eq_zero_comm hax,
      spForm_eq_zero_comm hay, add_zero, mul_zero, zero_smul, add_zero]
  · rw [commutatorElement_def, map_mul, map_mul, map_mul, c8_mat_inv_eq hg₁ hT₁,
      c8_mat_inv_eq hg₂ hT₂, hg₁, hg₂,
      show spTrans x 1 * spTrans (x + y) 1 * spTrans x 1 * spTrans (x + y) 1 =
        spTrans x 1 * (spTrans (x + y) 1 * (spTrans x 1 * spTrans (x + y) 1)) by
        simp only [mul_assoc], c8_conj_transvection hxy]

theorem c8_mem_trans_of_apply {n : ℕ} {F : Type} [Field F] [CharP F 2] {a b : Fin n ⊕ Fin n → F}
    (ha : a ≠ 0) (hb : spForm a b = 1) {g : StatedSp n F} (hg : g ∈ spRad a)
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T)
    (h : ∃ c : F, SpExtras.mat n F g *ᵥ b = b + c • a) : g ∈ T := by
  obtain ⟨w, l, -, hx⟩ := exists_param_of_mem_spRad ha hg
  obtain ⟨c, hc⟩ := h
  have e : b + w + (spForm w b + l) • a = b + c • a := by
    rw [← hc, hx b, hb, one_smul, mul_one]
    module
  have hw : w = (c - spForm w b - l) • a := by
    linear_combination (norm := module) e
  exact (hT.1 g).2 ⟨l, mat_eq_spTrans_of_param hx hw⟩

theorem c8_noInvComp {n : ℕ} {F : Type}
    [Field F] [CharP F 2] (hn : 3 ≤ n) (hF : Nat.card F = 2) {a : Fin n ⊕ Fin n → F}
    (ha : a ≠ 0) {T S : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hS : S ≤ spRad a)
    (hsup : S ⊔ T = spRad a) (hinf : S ⊓ T = ⊥)
    (hinv : ∀ x y : Fin n ⊕ Fin n → F, spForm a x = 0 → spForm a y = 0 → spForm x y = 1 →
      ∀ g : StatedSp n F, SpExtras.mat n F g = spTrans x 1 * spTrans y 1 →
        ∀ s ∈ S, g * s * g⁻¹ ∈ S) : False := by
  have hex : ∀ w : Fin n ⊕ Fin n → F, ∃ c : F, spForm a w = 0 →
      ∃ s ∈ S, ∀ v, SpExtras.mat n F s *ᵥ v =
        v + spForm a v • w + spForm w v • a + (c * spForm a v) • a := by
    intro w
    by_cases hw : spForm a w = 0
    · obtain ⟨s, hs, c, hc⟩ := exists_mem_param ha hT hS hsup hw
      exact ⟨c, fun _ => ⟨s, hs, hc⟩⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose wt hwt using hex
  have huniq : ∀ {w : Fin n ⊕ Fin n → F} {c : F} {s : StatedSp n F}, spForm a w = 0 →
      s ∈ S → (∀ v, SpExtras.mat n F s *ᵥ v =
        v + spForm a v • w + spForm w v • a + (c * spForm a v) • a) → c = wt w := by
    intro w c s hw hsS hs
    obtain ⟨s', hs'S, hs'⟩ := hwt w hw
    exact param_eq_of_mem_inf ha hT hinf hw hs hs' hsS hs'S
  have hadd : ∀ x y : Fin n ⊕ Fin n → F, spForm a x = 0 → spForm a y = 0 →
      wt (x + y) = wt x + wt y + spForm x y := by
    intro x y hx hy
    obtain ⟨sx, hsxS, hsx⟩ := hwt x hx
    obtain ⟨sy, hsyS, hsy⟩ := hwt y hy
    have hxy0 : spForm a (x + y) = 0 := by rw [spForm_add_right, hx, hy, add_zero]
    exact (huniq hxy0 (S.mul_mem hsxS hsyS) (mat_mul_mulVec_of_param hx hy hsx hsy)).symm
  have hfixa : ∀ x y : Fin n ⊕ Fin n → F, spForm a x = 0 → spForm a y = 0 →
      ∀ g : StatedSp n F, SpExtras.mat n F g = spTrans x 1 * spTrans y 1 →
        SpExtras.mat n F g *ᵥ a = a := by
    intro x y hx hy g hg
    have hxa : spForm x a = 0 := spForm_eq_zero_comm hx
    have hya : spForm y a = 0 := spForm_eq_zero_comm hy
    have h2 : spTrans y 1 *ᵥ a = a := by
      rw [spTrans_mulVec, hya, one_mul, zero_smul, add_zero]
    have h1 : SpExtras.mat n F g *ᵥ a = spTrans x 1 *ᵥ (spTrans y 1 *ᵥ a) := by
      rw [hg, Matrix.mulVec_mulVec]
    rw [h1, h2, spTrans_mulVec, hxa, one_mul, zero_smul, add_zero]
  have hfix : ∀ x y : Fin n ⊕ Fin n → F, spForm a x = 0 → spForm a y = 0 →
      spForm x y = 1 → ∀ g : StatedSp n F, SpExtras.mat n F g = spTrans x 1 * spTrans y 1 →
        ∀ w : Fin n ⊕ Fin n → F, spForm a w = 0 → wt (SpExtras.mat n F g *ᵥ w) = wt w := by
    intro x y hx hy hxy g hg w hw
    have hga := hfixa x y hx hy g hg
    have hgw : spForm a (SpExtras.mat n F g *ᵥ w) = 0 := spForm_mat_mulVec_eq_zero hga hw
    obtain ⟨s, hsS, hs⟩ := hwt w hw
    have hgs : g * s * g⁻¹ ∈ S := hinv x y hx hy hxy g hg s hsS
    exact (huniq hgw hgs (mat_conj_mulVec_of_param hs hga)).symm
  have hswap : ∀ x y : Fin n ⊕ Fin n → F, spForm a x = 0 → spForm a y = 0 →
      spForm x y = 1 → wt y = wt x := by
    intro x y hx hy hxy
    obtain ⟨g₁, hg₁⟩ := exists_mat_eq_spTrans x (1 : F)
    obtain ⟨g₂, hg₂⟩ := exists_mat_eq_spTrans y (1 : F)
    have hg : SpExtras.mat n F (g₁ * g₂) = spTrans x 1 * spTrans y 1 := by
      rw [map_mul, hg₁, hg₂]
    have hyx : spForm y x = 1 := by rw [spForm_comm, hxy, CharTwo.neg_eq]
    have h3 : spTrans y 1 *ᵥ x = x + y := by
      rw [spTrans_mulVec, hyx, one_mul, one_smul]
    have h4 : spTrans x 1 *ᵥ (x + y) = y := by
      rw [spTrans_mulVec, spForm_add_right, spForm_self, hxy, zero_add, one_mul, one_smul]
      linear_combination (norm := module) (1 : F) • two_smul_vec_eq_zero x
    have hxy' : SpExtras.mat n F (g₁ * g₂) *ᵥ x = y := by
      rw [hg, ← Matrix.mulVec_mulVec, h3, h4]
    have h5 := hfix x y hx hy hxy (g₁ * g₂) hg x hx
    rw [hxy'] at h5
    exact h5
  have hconst : ∀ x y : Fin n ⊕ Fin n → F, spForm a x = 0 → (∀ c : F, x ≠ c • a) →
      spForm a y = 0 → (∀ c : F, y ≠ c • a) → wt x = wt y := by
    intro x y hx hxa hy hya
    obtain ⟨z, hz, hxz, hyz⟩ := c8_exists_common_dual hF ha hx hxa hy hya
    exact (hswap x z hx hz hxz).symm.trans (hswap y z hy hz hyz)
  obtain ⟨x₀, -, hx₀a, hx₀c⟩ := exists_perp_vec_not_smul (show 2 ≤ n by omega) ha
  exact c8_no_const_quad hn hF ha wt (wt x₀) hadd (fun x hx hxa => hconst x x₀ hx hxa hx₀a hx₀c)

end CFSG.RankThree.GF2n.Tim79a

end
