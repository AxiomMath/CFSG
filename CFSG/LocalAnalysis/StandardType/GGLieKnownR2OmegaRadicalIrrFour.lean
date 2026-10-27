module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalIrr

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.PCoreSection

private theorem irr4_polar_minusVec {F : Type} [Field F] {b c : F} (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (m : Fin 3) (r : Bool) :
    polar (Spin.quadMinus 4 F b c) (Spin.Twisted.minusVec 4 (K := F) m r) x =
      bif r then x (.inr (.inl m)) else x (.inl m) := by
  cases r
  · rw [Spin.Twisted.minusVec_false, Spin.Twisted.fVec, polar_comm, polar_quadMinus_single_inr_inl]
    rfl
  · rw [Spin.Twisted.minusVec_true, Spin.Twisted.eVec, polar_comm, polar_quadMinus_single_inl]
    rfl

private theorem irr4_mem_W_iff {F : Type} [Field F] {b c : F} (i j : Fin 3) (s t : Bool)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    x ∈ siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)) ↔
      x (.inl i) = 0 ∧ x (.inr (.inl i)) = 0 ∧ x (.inl j) = 0 ∧ x (.inr (.inl j)) = 0 := by
  rw [siegelW, mem_orth_iff]
  constructor
  · intro h
    have hj : x (.inl j) = 0 ∧ x (.inr (.inl j)) = 0 := by
      have h1 := h (Spin.Twisted.minusVec 4 (K := F) j t) (Submodule.subset_span (by simp))
      have h2 := h (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Submodule.subset_span (by simp))
      rw [irr4_polar_minusVec] at h1 h2
      cases t
      · rw [Bool.not_false] at h2
        exact ⟨by simpa using h1, by simpa using h2⟩
      · rw [Bool.not_true] at h2
        exact ⟨by simpa using h2, by simpa using h1⟩
    have hi : x (.inl i) = 0 ∧ x (.inr (.inl i)) = 0 := by
      have h1 := h (Spin.Twisted.minusVec 4 (K := F) i s) (Submodule.subset_span (by simp))
      have h2 := h (Spin.Twisted.minusVec 4 (K := F) i (!s)) (Submodule.subset_span (by simp))
      rw [irr4_polar_minusVec] at h1 h2
      cases s
      · rw [Bool.not_false] at h2
        exact ⟨by simpa using h1, by simpa using h2⟩
      · rw [Bool.not_true] at h2
        exact ⟨by simpa using h2, by simpa using h1⟩
    exact ⟨hi.1, hi.2, hj.1, hj.2⟩
  · rintro ⟨hi1, hi2, hj1, hj2⟩ y hy
    refine Submodule.span_induction (p := fun y _ => polar (Spin.quadMinus 4 F b c) y x = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro z (rfl | rfl | rfl | rfl)
      · rw [irr4_polar_minusVec]; cases t <;> simp [hj1, hj2]
      · rw [irr4_polar_minusVec]; cases s <;> simp [hi1, hi2]
      · rw [irr4_polar_minusVec]; cases t <;> simp [hj1, hj2]
      · rw [irr4_polar_minusVec]; cases s <;> simp [hi1, hi2]
    · simp
    · intro a b _ _ ha hb; rw [polar_add_left, ha, hb, add_zero]
    · intro cc a _ ha; rw [polar_smul_left, ha, smul_zero]

private theorem irr4_b_ne_zero {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  refine discr_ne_zero_of_finite (K := F) hirr ?_
  have h4 : (4 : F) = 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul]
  rw [hb, h4]
  ring

private theorem irr4_eq_wVec {F : Type} [Field F] {b c : F} {i j k : Fin 3}
    (hcover : ∀ m : Fin 3, m = i ∨ m = j ∨ m = k) (s t : Bool)
    {x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hx : x ∈ siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s))) :
    x = Spin.Twisted.wVec 4 k (x (.inl k)) (fun q => x (.inr (.inr q))) (x (.inr (.inl k))) := by
  obtain ⟨hi1, hi2, hj1, hj2⟩ := (irr4_mem_W_iff i j s t x).mp hx
  funext z
  rcases z with m | m | q
  · rw [Spin.Twisted.wVec_apply_inl]
    by_cases hm : m = k
    · rw [if_pos hm, hm]
    · rw [if_neg hm]
      rcases hcover m with h | h | h
      · rw [h]; exact hi1
      · rw [h]; exact hj1
      · exact absurd h hm
  · rw [Spin.Twisted.wVec_apply_inr_inl]
    by_cases hm : m = k
    · rw [if_pos hm, hm]
    · rw [if_neg hm]
      rcases hcover m with h | h | h
      · rw [h]; exact hi2
      · rw [h]; exact hj2
      · exact absurd h hm
  · rw [Spin.Twisted.wVec_apply_inr_inr]

private theorem irr4_polarPlane_sep {F : Type} [Field F] [CharP F 2] {b c : F} (hb : b ≠ 0)
    {p : Fin 2 → F}
    (h : ∀ a : Fin 2 → F, polarPlane b c p a = 0) : p = 0 := by
  funext t
  fin_cases t
  · have h1 := h ![0, 1]
    have h2 : b * p 0 = 0 := by simpa [polarPlane, CharTwo.two_eq_zero] using h1
    exact (mul_eq_zero.mp h2).resolve_left hb
  · have h1 := h ![1, 0]
    have h2 : b * p 1 = 0 := by simpa [polarPlane, CharTwo.two_eq_zero] using h1
    exact (mul_eq_zero.mp h2).resolve_left hb

private theorem irr4_wVec_add {F : Type} [Field F] (k : Fin 3) (l₁ : F) (p₁ : Fin 2 → F) (m₁ : F)
    (l₂ : F)
    (p₂ : Fin 2 → F) (m₂ : F) :
    Spin.Twisted.wVec 4 k l₁ p₁ m₁ + Spin.Twisted.wVec 4 k l₂ p₂ m₂ =
      Spin.Twisted.wVec 4 k (l₁ + l₂) (p₁ + p₂) (m₁ + m₂) := by
  simp only [Spin.Twisted.wVec, Spin.Twisted.planeVec_add, add_smul]
  abel

private theorem irr4_wVec_smul {F : Type} [Field F] (k : Fin 3) (r l : F) (p : Fin 2 → F) (m : F) :
    r • Spin.Twisted.wVec 4 k l p m = Spin.Twisted.wVec 4 k (r * l) (r • p) (r * m) :=
  Spin.Twisted.wVec_smul 4 k r l p m

private theorem irr4_wVec_sub {F : Type} [Field F] (k : Fin 3) (l₁ : F) (p₁ : Fin 2 → F) (m₁ : F)
    (l₂ : F)
    (p₂ : Fin 2 → F) (m₂ : F) :
    Spin.Twisted.wVec 4 k l₁ p₁ m₁ - Spin.Twisted.wVec 4 k l₂ p₂ m₂ =
      Spin.Twisted.wVec 4 k (l₁ - l₂) (p₁ - p₂) (m₁ - m₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul F (Spin.Twisted.wVec 4 k l₂ p₂ m₂), irr4_wVec_smul,
    irr4_wVec_add, Spin.Twisted.wVec_eq_iff]
  exact ⟨by ring, by ext t; simp; ring, by ring⟩

private theorem irr4_eichler_e_wVec {F : Type} [Field F] {b c : F} (k : Fin 3) (a : Fin 2 → F)
    (l : F) (p : Fin 2 → F) (m : F) :
    eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k) (Spin.Twisted.planeVec 4 a)
      (Spin.Twisted.wVec 4 k l p m) =
      Spin.Twisted.wVec 4 k (l - polarPlane b c p a - planeNorm b c a * m) (p + m • a) m := by
  rw [eichler_apply (Spin.Twisted.quadMinus_eVec 4 b c k)
      (Spin.Twisted.polar_eVec_planeVec 4 b c k a),
    Spin.Twisted.polar_wVec_eVec, Spin.Twisted.polar_wVec_planeVec,
      Spin.Twisted.quadMinus_planeVec',
    ← Spin.Twisted.wVec_planeVec 4 k a, Spin.Twisted.wVec_smul,
    ← Spin.Twisted.wVec_eVec 4 k, Spin.Twisted.wVec_smul,
    irr4_wVec_add, irr4_wVec_sub]
  simp [sub_add_eq_sub_sub]

private theorem irr4_eichler_f_wVec {F : Type} [Field F] {b c : F} (k : Fin 3) (a : Fin 2 → F)
    (l : F) (p : Fin 2 → F) (m : F) :
    eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.fVec 4 k) (Spin.Twisted.planeVec 4 a)
      (Spin.Twisted.wVec 4 k l p m) =
      Spin.Twisted.wVec 4 k l (p + l • a) (m - polarPlane b c p a - planeNorm b c a * l) := by
  rw [eichler_apply (Spin.Twisted.quadMinus_fVec 4 b c k)
      (Spin.Twisted.polar_fVec_planeVec 4 b c k a),
    Spin.Twisted.polar_wVec_fVec, Spin.Twisted.polar_wVec_planeVec,
      Spin.Twisted.quadMinus_planeVec',
    ← Spin.Twisted.wVec_planeVec 4 k a, Spin.Twisted.wVec_smul,
    ← Spin.Twisted.wVec_fVec 4 k, Spin.Twisted.wVec_smul,
    irr4_wVec_add, irr4_wVec_sub]
  simp [sub_add_eq_sub_sub]


private theorem irr4_fixed_e {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {i j k : Fin 3}
    (hcover : ∀ m : Fin 3, m = i ∨ m = j ∨ m = k)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (s t : Bool)
    {x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hxW : x ∈ siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)))
    (hfix : ∀ a : Fin 2 → F,
      eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k) (Spin.Twisted.planeVec 4 a) x = x) :
    x ∈ Submodule.span F {Spin.Twisted.eVec 4 k} := by
  have hb : b ≠ 0 := irr4_b_ne_zero (b := b) (c := c) hirr
  set l : F := x (.inl k)
  set p : Fin 2 → F := fun q => x (.inr (.inr q))
  set m : F := x (.inr (.inl k))
  have hxeq : x = Spin.Twisted.wVec 4 k l p m := irr4_eq_wVec hcover s t hxW
  rw [hxeq] at hfix ⊢
  have hm : m = 0 := by
    have h1 := hfix ![1, 0]
    rw [irr4_eichler_e_wVec] at h1
    have h2 := congrArg (fun v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F => v (.inr (.inr (0 : Fin 2)))) h1
    rw [Spin.Twisted.wVec_apply_inr_inr, Spin.Twisted.wVec_apply_inr_inr, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h2
    linear_combination h2
  have hp : p = 0 := by
    apply irr4_polarPlane_sep hb
    intro a
    have h1 := hfix a
    rw [irr4_eichler_e_wVec, hm] at h1
    rw [Spin.Twisted.wVec_eq_iff] at h1
    have h2 : l - polarPlane b c p a = l := by
      simpa using h1.1
    exact sub_eq_self.mp h2
  rw [hm, hp, Spin.Twisted.wVec]
  simp only [Spin.Twisted.planeVec_zero, zero_smul, add_zero]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem irr4_eichler_fixes_S {F : Type} [Field F] {b c : F} {i j : Fin 3} (s t : Bool)
    {u w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (huW : u ∈ siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)))
    (hwW : w ∈ siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)))
    (hu : (Spin.quadMinus 4 F b c) u = 0) (huw : polar (Spin.quadMinus 4 F b c) u w = 0) :
    ∀ v ∈ Submodule.span F {(Spin.Twisted.minusVec 4 (K := F) j t),
      (Spin.Twisted.minusVec 4 (K := F) i s), (Spin.Twisted.minusVec 4 (K := F) j (!t)),
      (Spin.Twisted.minusVec 4 (K := F) i (!s))},
      eichler (Spin.quadMinus 4 F b c) u w v = v := by
  intro v hv
  rw [eichler_apply hu huw]
  have h1 : polar (Spin.quadMinus 4 F b c) v u = 0 := (mem_orth_iff.mp huW) v hv
  have h2 : polar (Spin.quadMinus 4 F b c) v w = 0 := (mem_orth_iff.mp hwW) v hv
  rw [h1, h2]
  module


private theorem irr4_aux {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {i j k : Fin 3}
    (hki : k ≠ i) (hkj : k ≠ j)
    (hcover : ∀ m : Fin 3, m = i ∨ m = j ∨ m = k)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (s t : Bool) :
    ∀ X : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F),
      X ≤ siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)) →
      (∀ g ∈ elementaryGroup (Spin.quadMinus 4 F b c),
        (∀ v ∈ Submodule.span F {(Spin.Twisted.minusVec 4 (K := F) j t),
          (Spin.Twisted.minusVec 4 (K := F) i s),
          (Spin.Twisted.minusVec 4 (K := F) j (!t)),
          (Spin.Twisted.minusVec 4 (K := F) i (!s))}, g v = v) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)) := by
  intro X hXW hXinv
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  right
  have heW : Spin.Twisted.eVec 4 k ∈ siegelW (Spin.quadMinus 4 F b c)
      (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
      (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)) := by
    rw [irr4_mem_W_iff]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Spin.Twisted.eVec, Pi.single_apply, Ne.symm hki, Ne.symm hkj]
  have hfW : Spin.Twisted.fVec 4 k ∈ siegelW (Spin.quadMinus 4 F b c)
      (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
      (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)) := by
    rw [irr4_mem_W_iff]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Spin.Twisted.fVec, Pi.single_apply, Ne.symm hki, Ne.symm hkj]
  have hplW : ∀ a : Fin 2 → F, Spin.Twisted.planeVec 4 a ∈ siegelW (Spin.quadMinus 4 F b c)
      (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
      (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)) := by
    intro a
    rw [irr4_mem_W_iff]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Spin.Twisted.planeVec]
  let φ : Multiplicative (Fin 2 → F) →* Gom (Spin.quadMinus 4 F b c) :=
    { toFun := fun a => ⟨eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k)
          (Spin.Twisted.planeVec 4 a.toAdd),
        eichler_mem_elementaryGroup (Spin.quadMinus 4 F b c) _ _⟩
      map_one' := by
        apply Subtype.ext
        show eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k)
          (Spin.Twisted.planeVec 4 (0 : Fin 2 → F)) = 1
        rw [Spin.Twisted.planeVec_zero, eichler_zero_right]
      map_mul' := by
        intro u v
        apply Subtype.ext
        show eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k)
            (Spin.Twisted.planeVec 4 (u * v).toAdd) =
          eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k)
            (Spin.Twisted.planeVec 4 u.toAdd) *
          eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k)
            (Spin.Twisted.planeVec 4 v.toAdd)
        rw [toAdd_mul, Spin.Twisted.planeVec_add,
          eichler_mul (Spin.Twisted.polar_eVec_planeVec 4 b c k u.toAdd)
            (Spin.Twisted.polar_eVec_planeVec 4 b c k v.toAdd)] }
  let T : Subgroup (Gom (Spin.quadMinus 4 F b c)) := φ.range
  have hT : IsPGroup 2 T := by
    have htop : IsPGroup 2 (⊤ : Subgroup (Multiplicative (Fin 2 → F))) := by
      intro y
      refine ⟨1, ?_⟩
      have hyy : y * y = 1 := by
        apply Subtype.ext
        show (y : Multiplicative (Fin 2 → F)) * (y : Multiplicative (Fin 2 → F)) = 1
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_one]
        exact CharTwo.add_self_eq_zero (y : Multiplicative (Fin 2 → F)).toAdd
      simpa [pow_two] using hyy
    have h := IsPGroup.map (p := 2) (H := ⊤) htop φ
    rwa [← MonoidHom.range_eq_map] at h
  obtain ⟨x, hxX, hx0, hxfix⟩ := exists_fixed_mem_of_isPGroup
    (isLinearAction_Gom (Spin.quadMinus 4 F b c)) (T := T) hT (L := ⊥) (P := X) bot_le
    (fun tt ht y hy => by
      obtain ⟨a, rfl⟩ := ht
      simpa [Gom.app, φ] using hXinv (eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k)
          (Spin.Twisted.planeVec 4 a.toAdd))
        (eichler_mem_elementaryGroup (Spin.quadMinus 4 F b c) _ _)
        (irr4_eichler_fixes_S s t heW (hplW a.toAdd)
          (Spin.Twisted.quadMinus_eVec 4 b c k)
          (Spin.Twisted.polar_eVec_planeVec 4 b c k a.toAdd)) y hy)
    (fun tt ht y hy => by
      rw [Submodule.mem_bot] at hy ⊢
      rw [hy, (isLinearAction_Gom (Spin.quadMinus 4 F b c)).map_zero tt])
    (Ne.symm hbot)
  have hfix' : ∀ a : Fin 2 → F,
      eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k) (Spin.Twisted.planeVec 4 a)
        x = x := by
    intro a
    have h := hxfix (φ (Multiplicative.ofAdd a)) ⟨Multiplicative.ofAdd a, rfl⟩
    rw [Submodule.mem_bot] at h
    have h2 : (φ (Multiplicative.ofAdd a)).app x = x := sub_eq_zero.mp h
    simpa [Gom.app, φ] using h2
  have hxspan := irr4_fixed_e hcover hirr s t (hXW hxX) hfix'
  obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hxspan
  have hcc0 : cc ≠ 0 := by
    intro h0
    apply hx0
    rw [← hcc, h0, zero_smul]
    exact Submodule.zero_mem _
  have heX : Spin.Twisted.eVec 4 k ∈ X := by
    have h := X.smul_mem cc⁻¹ hxX
    rwa [← hcc, smul_smul, inv_mul_cancel₀ hcc0, one_smul] at h
  have hfX : Spin.Twisted.fVec 4 k ∈ X := by
    have h1 : eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.fVec 4 k)
        (Spin.Twisted.planeVec 4 Spin.Twisted.planeOne) (Spin.Twisted.eVec 4 k) ∈ X :=
      hXinv _ (eichler_mem_elementaryGroup (Spin.quadMinus 4 F b c) _ _)
        (irr4_eichler_fixes_S s t hfW (hplW Spin.Twisted.planeOne)
          (Spin.Twisted.quadMinus_fVec 4 b c k)
          (Spin.Twisted.polar_fVec_planeVec 4 b c k Spin.Twisted.planeOne)) _ heX
    have h1' : Spin.Twisted.wVec 4 k 1 Spin.Twisted.planeOne 1 ∈ X := by
      convert h1 using 1
      rw [← Spin.Twisted.wVec_eVec 4 k, irr4_eichler_f_wVec, Spin.Twisted.wVec_eq_iff]
      refine ⟨rfl, ?_, ?_⟩
      · simp
      · simp [Spin.Twisted.polarPlane_zero_left, Spin.Twisted.planeNorm_planeOne, CharTwo.neg_eq]
    have h2 : eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k)
        (Spin.Twisted.planeVec 4 Spin.Twisted.planeOne)
        (Spin.Twisted.wVec 4 k 1 Spin.Twisted.planeOne 1) ∈ X :=
      hXinv _ (eichler_mem_elementaryGroup (Spin.quadMinus 4 F b c) _ _)
        (irr4_eichler_fixes_S s t heW (hplW Spin.Twisted.planeOne)
          (Spin.Twisted.quadMinus_eVec 4 b c k)
          (Spin.Twisted.polar_eVec_planeVec 4 b c k Spin.Twisted.planeOne)) _ h1'
    have h2' : Spin.Twisted.wVec 4 k 0 0 1 ∈ X := by
      convert h2 using 1
      rw [irr4_eichler_e_wVec, Spin.Twisted.wVec_eq_iff]
      refine ⟨?_, ?_, rfl⟩
      · simp [Spin.Twisted.polarPlane, Spin.Twisted.planeNorm, Spin.Twisted.planeOne,
          CharTwo.two_eq_zero]
      · ext t; fin_cases t <;>
          simp [Spin.Twisted.planeOne, CharTwo.add_self_eq_zero]
    simpa [Spin.Twisted.wVec_fVec] using h2'
  have hplX : ∀ a : Fin 2 → F, Spin.Twisted.planeVec 4 a ∈ X := by
    intro a
    have h1 : eichler (Spin.quadMinus 4 F b c) (Spin.Twisted.eVec 4 k)
        (Spin.Twisted.planeVec 4 a) (Spin.Twisted.fVec 4 k) ∈ X :=
      hXinv _ (eichler_mem_elementaryGroup (Spin.quadMinus 4 F b c) _ _)
        (irr4_eichler_fixes_S s t heW (hplW a)
          (Spin.Twisted.quadMinus_eVec 4 b c k)
          (Spin.Twisted.polar_eVec_planeVec 4 b c k a)) _ hfX
    have h1' : Spin.Twisted.wVec 4 k (planeNorm b c a) a 1 ∈ X := by
      convert h1 using 1
      rw [← Spin.Twisted.wVec_fVec 4 k, irr4_eichler_e_wVec, Spin.Twisted.wVec_eq_iff]
      refine ⟨?_, ?_, rfl⟩
      · simp [Spin.Twisted.polarPlane_zero_left, CharTwo.neg_eq]
      · simp
    have h3 : Spin.Twisted.planeVec 4 a =
        Spin.Twisted.wVec 4 k (planeNorm b c a) a 1 - planeNorm b c a • Spin.Twisted.eVec 4 k -
        Spin.Twisted.fVec 4 k := by
      rw [Spin.Twisted.wVec]
      simp only [one_smul]
      module
    rw [h3]
    exact X.sub_mem (X.sub_mem h1' (X.smul_mem _ heX)) hfX
  apply le_antisymm hXW
  intro w hw
  rw [irr4_eq_wVec hcover s t hw, Spin.Twisted.wVec]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (X.smul_mem _ heX) (hplX _)) (X.smul_mem _ hfX)


private theorem irr4_main {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {i j : Fin 3} (hij : i ≠ j) (s t : Bool) :
    ∀ X : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F),
      X ≤ siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)) →
      (∀ g ∈ elementaryGroup (Spin.quadMinus 4 F b c),
        (∀ v ∈ Submodule.span F {(Spin.Twisted.minusVec 4 (K := F) j t),
          (Spin.Twisted.minusVec 4 (K := F) i s),
          (Spin.Twisted.minusVec 4 (K := F) j (!t)),
          (Spin.Twisted.minusVec 4 (K := F) i (!s))}, g v = v) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW (Spin.quadMinus 4 F b c)
        (Spin.Twisted.minusVec 4 (K := F) j t) (Spin.Twisted.minusVec 4 (K := F) i s)
        (Spin.Twisted.minusVec 4 (K := F) j (!t)) (Spin.Twisted.minusVec 4 (K := F) i (!s)) := by
  let k : Fin 3 := ⟨3 - i.val - j.val, by omega⟩
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hki : k ≠ i := by
    intro h
    have : i.val = j.val := by
      have hk : k.val = 3 - i.val - j.val := rfl
      have h_eq : k.val = i.val := congrArg Fin.val h
      omega
    exact hij' this
  have hkj : k ≠ j := by
    intro h
    have : i.val = j.val := by
      have hk : k.val = 3 - i.val - j.val := rfl
      have h_eq : k.val = j.val := congrArg Fin.val h
      omega
    exact hij' this
  have hcover : ∀ m : Fin 3, m = i ∨ m = j ∨ m = k := by
    intro m
    by_cases h1 : m = i
    · exact Or.inl h1
    by_cases h2 : m = j
    · exact Or.inr (Or.inl h2)
    right; right
    apply Fin.ext
    have h1' : m.val ≠ i.val := fun h => h1 (Fin.ext h)
    have h2' : m.val ≠ j.val := fun h => h2 (Fin.ext h)
    have hm := m.isLt
    have hi := i.isLt
    have hj := j.isLt
    have hk : k.val = 3 - i.val - j.val := rfl
    omega
  exact irr4_aux hki hkj hcover hirr s t

theorem siegelW_irreducible_quadMinus_four {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin 3} (hij : i ≠ j) (s t : Bool) :
    ∀ X : Submodule F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F),
      X ≤ siegelW (Spin.quadMinus 4 F b c) ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec j t)
        ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec i s)
        ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec j (!t))
        ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec i (!s)) →
      (∀ g ∈ elementaryGroup (Spin.quadMinus 4 F b c),
        (∀ v ∈ Submodule.span F {((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec j t),
          ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec i s),
          ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec j (!t)),
          ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec i (!s))}, g v = v) →
        ∀ x ∈ X, g x ∈ X) →
      X = ⊥ ∨ X = siegelW (Spin.quadMinus 4 F b c)
        ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec j t)
        ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec i s)
        ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec j (!t))
        ((Spin.Twisted.minusFrame 4 b c).toHypFrame.vec i (!s)) := by
  have hvec : (Spin.Twisted.minusFrame 4 b c).toHypFrame.vec = Spin.Twisted.minusVec 4 (K := F) :=
    Spin.Twisted.minusFrame_vec 4 b c
  rw [hvec]
  exact irr4_main hirr hij s t

end CFSG.StandardType.LieKnownR2.POmega.Radical
