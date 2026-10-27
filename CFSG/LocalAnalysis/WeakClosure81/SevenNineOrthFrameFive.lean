module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthSiegel
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthCW

public section

namespace CFSG.LocalAnalysis.WeakClosure81

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem zmod5_cases (q : ZMod 5) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by
  revert q; decide

private theorem zmod5_five_eq_zero : (5 : ZMod 5) = 0 := by decide

private theorem zmod5_neg_five_eq_zero : (-5 : ZMod 5) = 0 := by decide

private theorem zmod5_sixteen_eq_one : (16 : ZMod 5) = 1 := by decide

private theorem zmod5_neg_four_eq_one : (-(2 * 2) : ZMod 5) = 1 := by decide

private theorem zmod5_one_ne_zero : (1 : ZMod 5) ≠ 0 := by decide

private theorem zmod5_two_ne_zero : (2 : ZMod 5) ≠ 0 := by decide

private theorem zmod5_neg_two_ne_zero : (-2 : ZMod 5) ≠ 0 := by decide

private theorem exists_singular_orth_a [Fact (Nat.Prime 5)]
    (f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5)) (a : Fin 4 → ZMod 5) :
    ∃ s : Fin 4 → ZMod 5, s ≠ 0 ∧ f s s = 0 ∧ f s a = 0 := by
  obtain ⟨s, hs0, hss, hsa⟩ :=
    exists_ne_zero_isotropic_orth f (p := 5) (m := 4) ![a] (by norm_num)
  exact ⟨s, hs0, hss, by simpa using hsa 0⟩

private theorem exists_hyperbolic_partner_orth_a [Fact (Nat.Prime 5)]
    (f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5))
    (hf : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    {a s : Fin 4 → ZMod 5} (ha : f a a = -2) (hs0 : s ≠ 0) (hss : f s s = 0)
    (hsa : f s a = 0) :
    ∃ s' : Fin 4 → ZMod 5, f s s' = 1 ∧ f s' s' = 0 ∧ f s' a = 0 := by
  have has : f a s = 0 := by rw [hf a s]; exact hsa
  obtain ⟨s', hpair, hiso, horth⟩ :=
    exists_hyperbolic_partner f hf hnd zmod5_two_ne_zero hs0 hss
      (vs := fun _ : Fin 1 => a) (fun _ => hsa)
      (fun x => x - (2 * f x a) • a)
      (fun x _ => by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
          smul_eq_mul, ha]
        ring_nf
        rw [zmod5_five_eq_zero]
        simp)
      (fun x => by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
          smul_eq_mul, has]
        ring)
  exact ⟨s', hpair, hiso, by simpa using horth 0⟩

private theorem eq_zero_of_singular_orth
    (f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5))
    (hf : ∀ x y, f x y = f y x)
    (hW : ∀ a b : Fin 4 → ZMod 5, f a a = 0 → f a b = 0 → f b b = 0 →
      ∃ c d : ZMod 5, (c ≠ 0 ∨ d ≠ 0) ∧ c • a + d • b = 0)
    {s s' u : Fin 4 → ZMod 5} (hss : f s s = 0) (hus : f u s = 0)
    (hu : f u u = 0) (hpair : f s s' = 1) (hs'u : f s' u = 0) :
    u = 0 := by
  have hsu : f s u = 0 := by rw [hf s u]; exact hus
  obtain ⟨c, d, hcd, hsum⟩ := hW s u hss hsu hu
  have hss' : f s' s = 1 := by rw [hf s' s]; exact hpair
  have hc : c = 0 := by
    have h := congrArg (fun v => f s' v) hsum
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hss', hs'u, map_zero] at h
    simpa using h
  have hd : d ≠ 0 := by
    rcases hcd with hc0 | hd0
    · exact absurd hc hc0
    · exact hd0
  have hdu : d • u = 0 := by simpa [hc] using hsum
  have huinv := congrArg (fun v => d⁻¹ • v) hdu
  simpa [smul_smul, inv_mul_cancel₀ hd] using huinv

private theorem smul_two_norm_one_orth_four
    (f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5))
    {a s s' b0 : Fin 4 → ZMod 5} (hb0s : f b0 s = 0) (hb0s' : f b0 s' = 0)
    (hb0a : f b0 a = 0) (hq : f b0 b0 = 4) :
    f ((2 : ZMod 5) • b0) s = 0 ∧ f ((2 : ZMod 5) • b0) s' = 0 ∧
      f ((2 : ZMod 5) • b0) a = 0 ∧
        f ((2 : ZMod 5) • b0) ((2 : ZMod 5) • b0) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hb0s, mul_zero]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hb0s', mul_zero]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hb0a, mul_zero]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hq]
    ring_nf
    rw [zmod5_sixteen_eq_one]

private theorem exists_norm_one_orth_four [Fact (Nat.Prime 5)]
    (f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5))
    (hf : ∀ x y, f x y = f y x)
    (hW : ∀ a b : Fin 4 → ZMod 5, f a a = 0 → f a b = 0 → f b b = 0 →
      ∃ c d : ZMod 5, (c ≠ 0 ∨ d ≠ 0) ∧ c • a + d • b = 0)
    {a s s' : Fin 4 → ZMod 5} (ha : f a a = -2) (hss : f s s = 0)
    (hs's' : f s' s' = 0) (hpair : f s s' = 1) (hsa : f s a = 0) (hs'a : f s' a = 0) :
    ∃ b : Fin 4 → ZMod 5, f b s = 0 ∧ f b s' = 0 ∧ f b a = 0 ∧ f b b = 1 := by
  obtain ⟨b0, hb0, hb⟩ := exists_ne_zero_orth f (p := 5) (m := 4) ![s, s', a] (by decide)
  have hb0s : f b0 s = 0 := by simpa using hb 0
  have hb0s' : f b0 s' = 0 := by simpa using hb 1
  have hb0a : f b0 a = 0 := by simpa using hb 2
  have hs'b0 : f s' b0 = 0 := by rw [hf s' b0]; exact hb0s'
  have has : f a s = 0 := by rw [hf a s]; exact hsa
  have hab0 : f a b0 = 0 := by rw [hf a b0]; exact hb0a
  have hq := zmod5_cases (f b0 b0)
  rcases hq with hq | hq | hq | hq | hq
  · exact absurd (eq_zero_of_singular_orth f hf hW hss hb0s hq hpair hs'b0) hb0
  · exact ⟨b0, hb0s, hb0s', hb0a, hq⟩
  · have hu : f (a + b0) (a + b0) = 0 := by
      simp only [map_add, LinearMap.add_apply, ha, hab0, hb0a, hq]
      ring
    have hus : f (a + b0) s = 0 := by
      simp [map_add, LinearMap.add_apply, has, hb0s]
    have hs'u : f s' (a + b0) = 0 := by
      simp [map_add, LinearMap.add_apply, hs'a, hs'b0]
    have hfa : f (a + b0) a = -2 := by
      simp [map_add, LinearMap.add_apply, ha, hb0a]
    have hne : a + b0 ≠ 0 := by
      intro h0
      have : (-2 : ZMod 5) = 0 := by rw [← hfa, h0]; simp
      exact zmod5_neg_two_ne_zero this
    exact absurd (eq_zero_of_singular_orth f hf hW hss hus hu hpair hs'u) hne
  · have hu : f ((2 : ZMod 5) • a + b0) ((2 : ZMod 5) • a + b0) = 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ha, hab0, hb0a, hq]
      ring_nf
      rw [zmod5_neg_five_eq_zero]
    have hus : f ((2 : ZMod 5) • a + b0) s = 0 := by
      simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        has, hb0s]
    have hs'u : f s' ((2 : ZMod 5) • a + b0) = 0 := by
      simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hs'a, hs'b0]
    have hfa : f ((2 : ZMod 5) • a + b0) a = 1 := by
      simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ha, hb0a, zmod5_neg_four_eq_one]
    have hne : (2 : ZMod 5) • a + b0 ≠ 0 := by
      intro h0
      have : (1 : ZMod 5) = 0 := by rw [← hfa, h0]; simp
      exact zmod5_one_ne_zero this
    exact absurd (eq_zero_of_singular_orth f hf hW hss hus hu hpair hs'u) hne
  · obtain ⟨h1, h2, h3, h4⟩ := smul_two_norm_one_orth_four f hb0s hb0s' hb0a hq
    exact ⟨(2 : ZMod 5) • b0, h1, h2, h3, h4⟩

private theorem span_of_dual [Fact (Nat.Prime 5)]
    (f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5))
    (hf : ∀ x y, f x y = f y x)
    {s s' a b : Fin 4 → ZMod 5}
    (hss : f s s = 0) (hpair : f s s' = 1) (hs's' : f s' s' = 0)
    (ha : f a a = -2) (hsa : f s a = 0) (hs'a : f s' a = 0)
    (hbs : f b s = 0) (hbs' : f b s' = 0) (hba : f b a = 0) (hbb : f b b = 1) :
    ∀ w, f w s = 0 → f w s' = 0 → w = (2 * f w a) • a + f w b • b := by
  intro w hws hws'
  have has : f a s = 0 := by rw [hf a s]; exact hsa
  have has' : f a s' = 0 := by rw [hf a s']; exact hs'a
  have hsb : f s b = 0 := by rw [hf s b]; exact hbs
  have hs'b : f s' b = 0 := by rw [hf s' b]; exact hbs'
  have hs's : f s' s = 1 := by rw [hf s' s]; exact hpair
  have hab : f a b = 0 := by rw [hf a b]; exact hba
  have hd : ∀ i j : Fin 4,
      f (![s', s, (2 : ZMod 5) • a, b] j) (![s, s', a, b] i) =
        if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hss, hpair, hs's, hs's', hsa, hs'a, ha, has, has', hsb, hs'b, hbs, hbs', hba, hbb,
        hab, smul_eq_mul, zmod5_neg_four_eq_one]
  have hx : w - (2 * f w a) • a - f w b • b = 0 := by
    refine eq_zero_of_forall_orth_of_dual f (e := ![s, s', a, b])
      (d := ![s', s, (2 : ZMod 5) • a, b]) hd ?_
    intro i
    fin_cases i
    · simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hws, has, hbs]
    · simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hws', has', hbs']
    · change f (w - (2 * f w a) • a - f w b • b) a = 0
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        ha, hba, mul_zero, sub_zero]
      ring_nf
      rw [zmod5_five_eq_zero]
      simp
    · simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hab, hbb]
  calc
    w = (w - (2 * f w a) • a - f w b • b) + (2 * f w a) • a + f w b • b := by abel
    _ = (2 * f w a) • a + f w b • b := by rw [hx]; abel

structure OrthFrameFive (f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5))
    extends OrthFrame 5 4 f where
  b : Fin 4 → ZMod 5
  b_orth_s : f b s = 0
  b_orth_s' : f b s' = 0
  b_orth_a : f b a = 0
  norm_b : f b b = 1
  span : ∀ w, f w s = 0 → f w s' = 0 → w = (2 * f w a) • a + f w b • b

theorem exists_orthFrameFive (f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5))
    (hf : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hW : ∀ a b : Fin 4 → ZMod 5, f a a = 0 → f a b = 0 → f b b = 0 →
      ∃ c d : ZMod 5, (c ≠ 0 ∨ d ≠ 0) ∧ c • a + d • b = 0)
    {a : Fin 4 → ZMod 5} (ha : f a a = -2) : ∃ F : OrthFrameFive f, F.a = a := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨s, hs0, hss, hsa⟩ := exists_singular_orth_a f a
  obtain ⟨s', hpair, hs's', hs'a⟩ :=
    exists_hyperbolic_partner_orth_a f hf hnd ha hs0 hss hsa
  have has : f a s = 0 := by rw [hf a s]; exact hsa
  have has' : f a s' = 0 := by rw [hf a s']; exact hs'a
  obtain ⟨b, hbs, hbs', hba, hbb⟩ :=
    exists_norm_one_orth_four f hf hW ha hss hs's' hpair hsa hs'a
  refine ⟨?_, ?_⟩
  · exact
      { s := s
        s' := s'
        a := a
        symm := hf
        two_ne := zmod5_two_ne_zero
        isotropic_s := hss
        isotropic_s' := hs's'
        pair := hpair
        norm_a := ha
        a_orth_s := has
        a_orth_s' := has'
        b := b
        b_orth_s := hbs
        b_orth_s' := hbs'
        b_orth_a := hba
        norm_b := hbb
        span := span_of_dual f hf hss hpair hs's' ha hsa hs'a hbs hbs' hba hbb }
  · rfl

end CFSG.LocalAnalysis.WeakClosure81
