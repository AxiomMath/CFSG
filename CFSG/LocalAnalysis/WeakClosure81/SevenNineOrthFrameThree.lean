module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthSiegel
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthCW

public section

namespace CFSG.LocalAnalysis.WeakClosure81

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure OrthFrameThree (f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3))
    extends OrthFrame 3 6 f where
  t : Fin 6 → ZMod 3
  t' : Fin 6 → ZMod 3
  c : Fin 6 → ZMod 3
  γ : ZMod 3
  t_orth_s : f t s = 0
  t_orth_s' : f t s' = 0
  t_orth_a : f t a = 0
  isotropic_t : f t t = 0
  t'_orth_s : f t' s = 0
  t'_orth_s' : f t' s' = 0
  t'_orth_a : f t' a = 0
  isotropic_t' : f t' t' = 0
  pair_t : f t t' = 1
  c_orth_s : f c s = 0
  c_orth_s' : f c s' = 0
  c_orth_a : f c a = 0
  c_orth_t : f c t = 0
  c_orth_t' : f c t' = 0
  norm_c : f c c = γ
  γ_ne_zero : γ ≠ 0
  span : ∀ w, f w s = 0 → f w s' = 0 →
    w = f w a • a + f w t' • t + f w t • t' + (γ * f w c) • c

private def v1 {α : Type} (x0 : α) : Fin 1 → α
  | ⟨0, _⟩ => x0

private def v3 {α : Type} (x0 x1 x2 : α) : Fin 3 → α
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2

private def v5 {α : Type} (x0 x1 x2 x3 x4 : α) : Fin 5 → α
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3
  | ⟨4, _⟩ => x4

private def v6 {α : Type} (x0 x1 x2 x3 x4 x5 : α) : Fin 6 → α
  | ⟨0, _⟩ => x0
  | ⟨1, _⟩ => x1
  | ⟨2, _⟩ => x2
  | ⟨3, _⟩ => x3
  | ⟨4, _⟩ => x4
  | ⟨5, _⟩ => x5

private lemma zmod3_sq_eq_one {γ : ZMod 3} (h : γ ≠ 0) : γ * γ = 1 := by
  revert γ
  decide

private lemma zmod3_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private structure Seed (f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)) where
  s : Fin 6 → ZMod 3
  s' : Fin 6 → ZMod 3
  a : Fin 6 → ZMod 3
  t : Fin 6 → ZMod 3
  t' : Fin 6 → ZMod 3
  c₀ : Fin 6 → ZMod 3
  isotropic_s : f s s = 0
  isotropic_s' : f s' s' = 0
  pair : f s s' = 1
  norm_a : f a a = -2
  a_orth_s : f a s = 0
  a_orth_s' : f a s' = 0
  t_orth_s : f t s = 0
  t_orth_s' : f t s' = 0
  t_orth_a : f t a = 0
  isotropic_t : f t t = 0
  isotropic_t' : f t' t' = 0
  pair_t : f t t' = 1
  t'_orth_s : f t' s = 0
  t'_orth_s' : f t' s' = 0
  t'_orth_a : f t' a = 0
  c₀_orth_s : f c₀ s = 0
  c₀_orth_s' : f c₀ s' = 0
  c₀_orth_a : f c₀ a = 0
  c₀_orth_t : f c₀ t = 0
  c₀_orth_t' : f c₀ t' = 0
  c₀_ne : c₀ ≠ 0

private lemma exists_hyperbolic_pair_a (f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3))
    (hf : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    {a : Fin 6 → ZMod 3} (ha : f a a = -2) :
    ∃ s s' : Fin 6 → ZMod 3, f s s = 0 ∧ f s s' = 1 ∧ f s' s' = 0 ∧
      f a s = 0 ∧ f a s' = 0 := by
  have ha1 : f a a = 1 := by rw [ha]; decide
  obtain ⟨s, hs0, hss, hsa⟩ := exists_ne_zero_isotropic_orth f (vs := v1 a) (by decide)
  have hsa0 : f s a = 0 := hsa 0
  have has0 : f a s = 0 := (hf a s).trans hsa0
  obtain ⟨s', hss', hs's', hs'a⟩ :=
    exists_hyperbolic_partner f hf hnd zmod3_two_ne_zero hs0 hss (vs := v1 a)
      (fun i => hsa i)
      (fun x => x - f x a • a)
      (fun x i => by
        fin_cases i
        simp only [v1, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
          smul_eq_mul, ha1]
        ring)
      (fun x => by
        simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
          smul_eq_mul, has0]
        ring)
  exact ⟨s, s', hss, hss', hs's', has0, (hf a s').trans (hs'a 0)⟩

private lemma exists_hyperbolic_pair_t (f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3))
    (hf : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    {a s s' : Fin 6 → ZMod 3} (ha : f a a = -2) (hss : f s s = 0) (hss' : f s s' = 1)
    (hs's' : f s' s' = 0) (has : f a s = 0) (has' : f a s' = 0) :
    ∃ t t' : Fin 6 → ZMod 3, f t t = 0 ∧ f t t' = 1 ∧ f t' t' = 0 ∧ f t s = 0 ∧
      f t s' = 0 ∧ f t a = 0 ∧ f t' s = 0 ∧ f t' s' = 0 ∧ f t' a = 0 := by
  have ha1 : f a a = 1 := by rw [ha]; decide
  obtain ⟨t, ht0, htt, htv⟩ :=
    exists_ne_zero_isotropic_orth f (vs := v3 s s' a) (by decide)
  have hts : f t s = 0 := htv 0
  have hts' : f t s' = 0 := htv 1
  have hta : f t a = 0 := htv 2
  obtain ⟨t', htt', ht't', ht'v⟩ :=
    exists_hyperbolic_partner f hf hnd zmod3_two_ne_zero ht0 htt (vs := v3 s s' a)
      (fun i => htv i)
      (fun x => x - f x s' • s - f x s • s' - f x a • a)
      (fun x i => by
        fin_cases i
        · simp only [v3, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
            smul_eq_mul, hf s' s, hss', hss, has]
          ring
        · simp only [v3, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
            smul_eq_mul, hss', hs's', has']
          ring
        · simp only [v3, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
            smul_eq_mul, hf s a, hf s' a, has, has', ha1]
          ring)
      (fun x => by
        simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
          smul_eq_mul, hf s t, hf s' t, hf a t, hts, hts', hta]
        ring)
  exact ⟨t, t', htt, htt', ht't', hts, hts', hta, ht'v 0, ht'v 1, ht'v 2⟩

private lemma exists_seed (f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3))
    (hf : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    {a : Fin 6 → ZMod 3} (ha : f a a = -2) : ∃ D : Seed f, D.a = a := by
  obtain ⟨s, s', hss, hss', hs's', has, has'⟩ := exists_hyperbolic_pair_a f hf hnd ha
  obtain ⟨t, t', htt, htt', ht't', hts, hts', hta, ht's, ht's', ht'a⟩ :=
    exists_hyperbolic_pair_t f hf hnd ha hss hss' hs's' has has'
  obtain ⟨c₀, hc₀0, hc₀v⟩ := exists_ne_zero_orth f (vs := v5 s s' a t t') (by decide)
  refine ⟨?_, ?_⟩
  exact
    { s := s, s' := s', a := a, t := t, t' := t', c₀ := c₀,
      isotropic_s := hss, isotropic_s' := hs's', pair := hss', norm_a := ha,
      a_orth_s := has, a_orth_s' := has', t_orth_s := hts, t_orth_s' := hts',
      t_orth_a := hta, isotropic_t := htt, isotropic_t' := ht't', pair_t := htt',
      t'_orth_s := ht's, t'_orth_s' := ht's', t'_orth_a := ht'a, c₀_orth_s := hc₀v 0,
      c₀_orth_s' := hc₀v 1, c₀_orth_a := hc₀v 2, c₀_orth_t := hc₀v 3,
      c₀_orth_t' := hc₀v 4, c₀_ne := hc₀0 }
  rfl

private def seedProj {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (D : Seed f)
    (y : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  y - f y D.s' • D.s - f y D.s • D.s' - f y D.a • D.a - f y D.t' • D.t - f y D.t • D.t'

private lemma seedProj_orth {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (D : Seed f)
    (hf : ∀ x y, f x y = f y x) {y : Fin 6 → ZMod 3} :
    f (seedProj D y) D.s = 0 ∧ f (seedProj D y) D.s' = 0 ∧ f (seedProj D y) D.a = 0 ∧
      f (seedProj D y) D.t = 0 ∧ f (seedProj D y) D.t' = 0 ∧
      f D.c₀ (seedProj D y) = f D.c₀ y := by
  have ha1 : f D.a D.a = 1 := by rw [D.norm_a]; decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [seedProj, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      smul_eq_mul]
    rw [hf D.s' D.s, D.pair, D.isotropic_s, D.a_orth_s, D.t_orth_s, D.t'_orth_s]
    ring
  · simp only [seedProj, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      smul_eq_mul]
    rw [D.pair, D.isotropic_s', D.a_orth_s', D.t_orth_s', D.t'_orth_s']
    ring
  · simp only [seedProj, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      smul_eq_mul]
    rw [hf D.s D.a, hf D.s' D.a, D.a_orth_s, D.a_orth_s', D.t_orth_a, D.t'_orth_a, ha1]
    ring
  · simp only [seedProj, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      smul_eq_mul]
    rw [hf D.s D.t, hf D.s' D.t, hf D.a D.t, hf D.t' D.t, D.t_orth_s, D.t_orth_s',
      D.t_orth_a, D.isotropic_t, D.pair_t]
    ring
  · simp only [seedProj, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      smul_eq_mul]
    rw [hf D.s D.t', hf D.s' D.t', hf D.a D.t', D.t'_orth_s, D.t'_orth_s', D.t'_orth_a,
      D.pair_t, D.isotropic_t']
    ring
  · simp only [seedProj, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right,
      smul_eq_mul]
    rw [D.c₀_orth_s, D.c₀_orth_s', D.c₀_orth_a, D.c₀_orth_t, D.c₀_orth_t']
    ring

private lemma seed_exists_anisotropic {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    (D : Seed f) (hf : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0) :
    ∃ c : Fin 6 → ZMod 3, f c D.s = 0 ∧ f c D.s' = 0 ∧ f c D.a = 0 ∧ f c D.t = 0 ∧
      f c D.t' = 0 ∧ f c c ≠ 0 := by
  by_cases hcc : f D.c₀ D.c₀ = 0
  · obtain ⟨y, hy⟩ : ∃ y, f D.c₀ y ≠ 0 := by
      by_contra h
      exact D.c₀_ne (hnd D.c₀ (by simpa only [not_exists, not_not] using h))
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := seedProj_orth D hf (y := y)
    by_cases hyy : f (seedProj D y) (seedProj D y) = 0
    · have hval : f (D.c₀ + seedProj D y) (D.c₀ + seedProj D y) = 2 * f D.c₀ y := by
        rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
          LinearMap.BilinForm.add_right, hf (seedProj D y) D.c₀, hcc, hyy, h6]
        ring
      refine ⟨D.c₀ + seedProj D y, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [LinearMap.BilinForm.add_left, D.c₀_orth_s, h1, add_zero]
      · rw [LinearMap.BilinForm.add_left, D.c₀_orth_s', h2, add_zero]
      · rw [LinearMap.BilinForm.add_left, D.c₀_orth_a, h3, add_zero]
      · rw [LinearMap.BilinForm.add_left, D.c₀_orth_t, h4, add_zero]
      · rw [LinearMap.BilinForm.add_left, D.c₀_orth_t', h5, add_zero]
      · rw [hval]
        exact mul_ne_zero zmod3_two_ne_zero hy
    · exact ⟨seedProj D y, h1, h2, h3, h4, h5, hyy⟩
  · exact ⟨D.c₀, D.c₀_orth_s, D.c₀_orth_s', D.c₀_orth_a, D.c₀_orth_t, D.c₀_orth_t', hcc⟩

private lemma seed_dual_pairing {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    (D : Seed f) (hf : ∀ x y, f x y = f y x) {c : Fin 6 → ZMod 3} {γ : ZMod 3}
    (hcs : f c D.s = 0) (hcs' : f c D.s' = 0) (hca : f c D.a = 0) (hct : f c D.t = 0)
    (hct' : f c D.t' = 0) (hcc : f c c = γ) (hγ : γ ≠ 0) :
    ∀ i j, f (v6 D.s' D.s D.a D.t' D.t (γ • c) j) (v6 D.s D.s' D.a D.t D.t' c i) =
      if i = j then 1 else 0 := by
  have ha1 : f D.a D.a = 1 := by rw [D.norm_a]; decide
  have hγsq : γ * γ = 1 := zmod3_sq_eq_one hγ
  have h1 : f D.s' D.s = 1 := (hf D.s' D.s).trans D.pair
  have h2 : f D.s' D.a = 0 := (hf D.s' D.a).trans D.a_orth_s'
  have h3 : f D.s D.a = 0 := (hf D.s D.a).trans D.a_orth_s
  have h4 : f D.s' D.t = 0 := (hf D.s' D.t).trans D.t_orth_s'
  have h5 : f D.s D.t = 0 := (hf D.s D.t).trans D.t_orth_s
  have h6 : f D.a D.t = 0 := (hf D.a D.t).trans D.t_orth_a
  have h7 : f D.t' D.t = 1 := (hf D.t' D.t).trans D.pair_t
  have h8 : f D.s D.t' = 0 := (hf D.s D.t').trans D.t'_orth_s
  have h9 : f D.a D.t' = 0 := (hf D.a D.t').trans D.t'_orth_a
  have h10 : f D.s' c = 0 := (hf D.s' c).trans hcs'
  have h11 : f D.s c = 0 := (hf D.s c).trans hcs
  have h12 : f D.a c = 0 := (hf D.a c).trans hca
  have h13 : f D.t' c = 0 := (hf D.t' c).trans hct'
  have h14 : f D.t c = 0 := (hf D.t c).trans hct
  have h15 : f D.s' D.t' = 0 := (hf D.s' D.t').trans D.t'_orth_s'
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [v6, LinearMap.BilinForm.smul_left, smul_eq_mul, D.isotropic_s, D.pair,
      D.isotropic_s', ha1, D.a_orth_s, D.a_orth_s', D.t_orth_s, D.t_orth_s', D.t_orth_a,
      D.isotropic_t, D.t'_orth_s, D.t'_orth_s', D.t'_orth_a, D.isotropic_t', D.pair_t,
      hcs, hcs', hca, hct, hct', hcc, hγsq, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13, h14, h15, mul_zero, if_true, if_false]
  all_goals decide

private lemma seed_orth_dual {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    (D : Seed f) (hf : ∀ x y, f x y = f y x) {c : Fin 6 → ZMod 3} {γ : ZMod 3}
    (hcs : f c D.s = 0) (hcs' : f c D.s' = 0) (hca : f c D.a = 0) (hct : f c D.t = 0)
    (hct' : f c D.t' = 0) (hcc : f c c = γ) (hγ : γ ≠ 0)
    {w : Fin 6 → ZMod 3} (hws : f w D.s = 0) (hws' : f w D.s' = 0) :
    ∀ i, f (w - (f w D.a • D.a + f w D.t' • D.t + f w D.t • D.t' + (γ * f w c) • c))
      (v6 D.s D.s' D.a D.t D.t' c i) = 0 := by
  have ha1 : f D.a D.a = 1 := by rw [D.norm_a]; decide
  have hγsq : γ * γ = 1 := zmod3_sq_eq_one hγ
  have h6 : f D.a D.t = 0 := (hf D.a D.t).trans D.t_orth_a
  have h7 : f D.t' D.t = 1 := (hf D.t' D.t).trans D.pair_t
  have h9 : f D.a D.t' = 0 := (hf D.a D.t').trans D.t'_orth_a
  have h12 : f D.a c = 0 := (hf D.a c).trans hca
  have h13 : f D.t' c = 0 := (hf D.t' c).trans hct'
  have h14 : f D.t c = 0 := (hf D.t c).trans hct
  intro i
  fin_cases i <;>
    simp only [v6, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, smul_eq_mul, hws, hws', ha1, D.a_orth_s,
      D.a_orth_s', D.t_orth_s, D.t_orth_s', D.t_orth_a, D.t'_orth_s, D.t'_orth_s',
      D.t'_orth_a, D.isotropic_t, D.isotropic_t', D.pair_t, h6, h7, h9, h12, h13, h14,
      hcs, hcs', hca, hct, hct', hcc, hγsq, mul_zero]
  all_goals
    try rw [mul_assoc, mul_comm (f w c) γ, ← mul_assoc, hγsq, one_mul]
    ring

private lemma seed_span {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (D : Seed f)
    (hf : ∀ x y, f x y = f y x) {c : Fin 6 → ZMod 3} {γ : ZMod 3}
    (hcs : f c D.s = 0) (hcs' : f c D.s' = 0) (hca : f c D.a = 0) (hct : f c D.t = 0)
    (hct' : f c D.t' = 0) (hcc : f c c = γ) (hγ : γ ≠ 0) :
    ∀ w, f w D.s = 0 → f w D.s' = 0 →
      w = f w D.a • D.a + f w D.t' • D.t + f w D.t • D.t' + (γ * f w c) • c := by
  intro w hws hws'
  have hd := seed_dual_pairing D hf hcs hcs' hca hct hct' hcc hγ
  have hx := seed_orth_dual D hf hcs hcs' hca hct hct' hcc hγ hws hws'
  have h0 : w - (f w D.a • D.a + f w D.t' • D.t + f w D.t • D.t' +
      (γ * f w c) • c) = 0 :=
    eq_zero_of_forall_orth_of_dual f
      (e := v6 D.s D.s' D.a D.t D.t' c) (d := v6 D.s' D.s D.a D.t' D.t (γ • c)) hd hx
  exact sub_eq_zero.mp h0

theorem exists_orthFrameThree (f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3))
    (hf : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    {a : Fin 6 → ZMod 3} (ha : f a a = -2) : ∃ F : OrthFrameThree f, F.a = a := by
  obtain ⟨D, rfl⟩ := exists_seed f hf hnd ha
  obtain ⟨c, hcs, hcs', hca, hct, hct', hcc⟩ := seed_exists_anisotropic D hf hnd
  refine ⟨?_, ?_⟩
  exact
    { s := D.s, s' := D.s', a := D.a, symm := hf, two_ne := zmod3_two_ne_zero,
      isotropic_s := D.isotropic_s, isotropic_s' := D.isotropic_s', pair := D.pair,
      norm_a := D.norm_a, a_orth_s := D.a_orth_s, a_orth_s' := D.a_orth_s',
      t := D.t, t' := D.t', c := c, γ := f c c,
      t_orth_s := D.t_orth_s, t_orth_s' := D.t_orth_s', t_orth_a := D.t_orth_a,
      isotropic_t := D.isotropic_t, t'_orth_s := D.t'_orth_s,
      t'_orth_s' := D.t'_orth_s', t'_orth_a := D.t'_orth_a,
      isotropic_t' := D.isotropic_t', pair_t := D.pair_t,
      c_orth_s := hcs, c_orth_s' := hcs', c_orth_a := hca, c_orth_t := hct,
      c_orth_t' := hct', norm_c := rfl, γ_ne_zero := hcc,
      span := seed_span D hf hcs hcs' hca hct hct' rfl hcc }
  rfl

end CFSG.LocalAnalysis.WeakClosure81
