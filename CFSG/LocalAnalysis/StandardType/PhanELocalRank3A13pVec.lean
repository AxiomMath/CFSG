module

public import CFSG.LocalAnalysis.StandardType.PhanELocalHerm4

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private noncomputable def plv_hhTuple (a b : Fin 4 → K) : K × K × K × K :=
  (hh f a a, hh f a b, hh f b a, hh f b b)

private noncomputable def plv_gramTuple (c a b : Fin 4 → K) : K × K × K × K :=
  (gram f c a, hh f c c * hh f a b - hh f c b * hh f a c,
    hh f c c * hh f b a - hh f c a * hh f b c, gram f c b)

private lemma plv_pev_hhTuple (a b : Fin 4 → K) (s : K) :
    pev (2 ^ f) (plv_hhTuple f a b) s = hh f (s • a + b) (s • a + b) := by
  rw [hh_comb]
  simp only [pev, plv_hhTuple]

private lemma plv_pev_gramTuple (c a b : Fin 4 → K) (s : K) :
    pev (2 ^ f) (plv_gramTuple f c a b) s = gram f c (s • a + b) := by
  rw [gram_comb]
  simp only [pev, plv_gramTuple]

private lemma plv_pev_zero (c : K × K × K × K) : pev (2 ^ f) c 0 = c.2.2.2 := by
  have hq0 : (2 : ℕ) ^ f ≠ 0 := pow_ne_zero f (by norm_num)
  simp [pev, hq0]

private lemma plv_pev_s (s : K) : pev (2 ^ f) ((0, 0, 1, 0) : K × K × K × K) s = s := by
  simp [pev]

private lemma plv_hhTuple_ne_zero_of_fst {a b : Fin 4 → K} (h : hh f a a ≠ 0) :
    plv_hhTuple f a b ≠ 0 := by
  intro h0
  exact h (by
    have := congrArg (fun t : K × K × K × K => t.1) h0
    simpa [plv_hhTuple] using this)

private lemma plv_gramTuple_ne_zero_of_fst {c a b : Fin 4 → K} (h : gram f c a ≠ 0) :
    plv_gramTuple f c a b ≠ 0 := by
  intro h0
  exact h (by
    have := congrArg (fun t : K × K × K × K => t.1) h0
    simpa [plv_gramTuple] using this)

private lemma plv_gramTuple_ne_zero_of_last {c a b : Fin 4 → K} (h : gram f c b ≠ 0) :
    plv_gramTuple f c a b ≠ 0 := by
  intro h0
  exact h (by
    have := congrArg (fun t : K × K × K × K => t.2.2.2) h0
    simpa [plv_gramTuple] using this)

private lemma plv_gramTuple_ne_zero_of_aniso (hK : Nat.card K = (2 ^ f) ^ 2)
    {u a b : Fin 4 → K} (hu : Aniso f u) (hab : gram f a b ≠ 0) :
    plv_gramTuple f u a b ≠ 0 := by
  intro h0
  have h1 : gram f u a = 0 := by
    have := congrArg (fun t : K × K × K × K => t.1) h0
    simpa [plv_gramTuple] using this
  have h3 : hh f u u * hh f a b - hh f u b * hh f a u = 0 := by
    have := congrArg (fun t : K × K × K × K => t.2.1) h0
    simpa [plv_gramTuple] using this
  have h2 : gram f u b = 0 := by
    have := congrArg (fun t : K × K × K × K => t.2.2.2) h0
    simpa [plv_gramTuple] using this
  exact hab (gram_eq_zero_of_coeffs f hK hu h1 h2 h3)

private lemma plv_gram_self_comb (a b : Fin 4 → K) (s : K) :
    gram f b (s • a + b) = gram f b a * s ^ (2 ^ f + 1) := by
  rw [gram_comb f b a b s, gram_self f b]
  ring

theorem exists_nbr_vec (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {u : Fin 4 → K}
    (hu : Aniso f u) :
    ∃ w : Fin 4 → K, w 0 = 0 ∧ Aniso f w ∧ gram f u w ≠ 0 := by
  let a : Fin 4 → K := Pi.single (1 : Fin 4) (1 : K)
  let b : Fin 4 → K := Pi.single (2 : Fin 4) (1 : K)
  have ha : Aniso f a := aniso_single_one f
  have hab : gram f a b ≠ 0 := gram_single_one_two f
  have hc₁ : plv_hhTuple f a b ≠ 0 := plv_hhTuple_ne_zero_of_fst f ha
  have hc₂ : plv_gramTuple f u a b ≠ 0 := plv_gramTuple_ne_zero_of_aniso f hK hu hab
  obtain ⟨s, h₁, h₂, -⟩ := exists_avoid f hK hq hc₁ hc₂ hc₂
  refine ⟨s • a + b, ?_, ?_, ?_⟩
  · simp [a, b, Pi.single_apply]
  · show hh f (s • a + b) (s • a + b) ≠ 0
    rw [← plv_pev_hhTuple f a b s]
    exact h₁
  · show gram f u (s • a + b) ≠ 0
    rw [← plv_pev_gramTuple f u a b s]
    exact h₂

theorem nbr3_vec (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {u c d : Fin 4 → K}
    (hc0 : c 0 = 0) (hd0 : d 0 = 0) (hu : Aniso f u) (hc : Aniso f c) (hcd : gram f c d ≠ 0) :
    ∃ t : Fin 4 → K, t 0 = 0 ∧ Aniso f t ∧ gram f u t ≠ 0 ∧ gram f c t ≠ 0 ∧ gram f d t ≠ 0 := by
  have hc₁ : plv_hhTuple f c d ≠ 0 := plv_hhTuple_ne_zero_of_fst f hc
  have hc₂ : plv_gramTuple f u c d ≠ 0 := plv_gramTuple_ne_zero_of_aniso f hK hu hcd
  have hc₃ : ((0, 0, 1, 0) : K × K × K × K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by
      have := congrArg (fun t : K × K × K × K => t.2.2.1) h0
      simpa using this
    exact one_ne_zero h1
  obtain ⟨s, h₁, h₂, h₃⟩ := exists_avoid f hK hq hc₁ hc₂ hc₃
  have hs : s ≠ 0 := fun hs0 => h₃ (by rw [hs0, plv_pev_s f 0])
  refine ⟨s • c + d, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hc0, hd0]
  · show hh f (s • c + d) (s • c + d) ≠ 0
    rw [← plv_pev_hhTuple f c d s]
    exact h₁
  · show gram f u (s • c + d) ≠ 0
    rw [← plv_pev_gramTuple f u c d s]
    exact h₂
  · rw [add_comm (s • c) d, gram_add_smul_right f c d s]
    exact hcd
  · rw [plv_gram_self_comb f c d s, gram_symm f d c]
    exact mul_ne_zero hcd (pow_ne_zero _ hs)

theorem nbr2_vec (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {u v : Fin 4 → K}
    (hu0 : u 0 = 0) (hu : Aniso f u) (hv : Aniso f v) :
    ∃ t : Fin 4 → K, t 0 = 0 ∧ Aniso f t ∧ gram f u t ≠ 0 ∧ gram f v t ≠ 0 := by
  obtain ⟨w, hw0, _, huw⟩ := exists_nbr_vec f hK hq hu
  obtain ⟨t, ht0, ht, hvt, hut, -⟩ :=
    nbr3_vec (u := v) (c := u) (d := w) f hK hq hu0 hw0 hv hu huw
  exact ⟨t, ht0, ht, hut, hvt⟩

theorem nbr4_vec (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {a b c d : Fin 4 → K}
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha : Aniso f a) (hab : gram f a b ≠ 0)
    (hbc : gram f b c ≠ 0) (hda : gram f d a ≠ 0) (hbd : gram f b d = 0) :
    ∃ t : Fin 4 → K, t 0 = 0 ∧ Aniso f t ∧ gram f a t ≠ 0 ∧ gram f b t ≠ 0 ∧ gram f c t ≠ 0 ∧
      gram f d t ≠ 0 := by
  have hc₁ : plv_hhTuple f a b ≠ 0 := plv_hhTuple_ne_zero_of_fst f ha
  have hc₂ : plv_gramTuple f c a b ≠ 0 :=
    plv_gramTuple_ne_zero_of_last f (by rw [gram_symm f]; exact hbc)
  have hc₃ : plv_gramTuple f d a b ≠ 0 := plv_gramTuple_ne_zero_of_fst f hda
  obtain ⟨s, h₁, h₂, h₃⟩ := exists_avoid f hK hq hc₁ hc₂ hc₃
  have hs : s ≠ 0 := by
    intro hs0
    apply h₃
    rw [hs0, plv_pev_zero f (plv_gramTuple f d a b)]
    simp only [plv_gramTuple]
    rw [gram_symm f d b]
    exact hbd
  refine ⟨s • a + b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ha0, hb0]
  · show hh f (s • a + b) (s • a + b) ≠ 0
    rw [← plv_pev_hhTuple f a b s]
    exact h₁
  · rw [add_comm (s • a) b, gram_add_smul_right f a b s]
    exact hab
  · rw [plv_gram_self_comb f a b s, gram_symm f b a]
    exact mul_ne_zero hab (pow_ne_zero _ hs)
  · show gram f c (s • a + b) ≠ 0
    rw [← plv_pev_gramTuple f c a b s]
    exact h₂
  · show gram f d (s • a + b) ≠ 0
    rw [← plv_pev_gramTuple f d a b s]
    exact h₃

theorem cone_vec (hK : Nat.card K = (2 ^ f) ^ 2) {x y z : Fin 4 → K} (hx : Aniso f x)
    (hy : Aniso f y) (hz : Aniso f z) (hxy : gram f x y ≠ 0)
    (hzxy : z ∈ Submodule.span K {x, y}) :
    Aniso f (polar f x y) ∧ gram f x (polar f x y) ≠ 0 ∧ gram f y (polar f x y) ≠ 0 ∧
      gram f z (polar f x y) ≠ 0 ∧ polar f x y ∉ Submodule.span K {x, y} := by
  have hxp0 : hh f x (polar f x y) = 0 := hh_polar_left f x y
  have hyp0 : hh f y (polar f x y) = 0 := hh_polar_right f x y
  have hpx0 : hh f (polar f x y) x = 0 := by
    rw [hh_symm f hK x (polar f x y), hxp0, map_zero]
  have hpy0 : hh f (polar f x y) y = 0 := by
    rw [hh_symm f hK y (polar f x y), hyp0, map_zero]
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hzxy
  have hzp0 : hh f z (polar f x y) = 0 := by
    rw [← hab, hh_add_left, hh_smul_left, hh_smul_left, hxp0, hyp0, mul_zero, mul_zero, add_zero]
  have hpz0 : hh f (polar f x y) z = 0 := by
    rw [hh_symm f hK z (polar f x y), hzp0, map_zero]
  have hpp : hh f (polar f x y) (polar f x y) = gram f x y := hh_polar_self f hK x y
  have hpp_ne : hh f (polar f x y) (polar f x y) ≠ 0 := by
    rw [hpp]
    exact hxy
  refine ⟨hpp_ne, ?_, ?_, ?_, ?_⟩
  · simp only [gram, hxp0, hpx0, mul_zero, sub_zero]
    exact mul_ne_zero hx hpp_ne
  · simp only [gram, hyp0, hpy0, mul_zero, sub_zero]
    exact mul_ne_zero hy hpp_ne
  · simp only [gram, hzp0, hpz0, mul_zero, sub_zero]
    exact mul_ne_zero hz hpp_ne
  · intro hmem
    obtain ⟨a', b', hab'⟩ := Submodule.mem_span_pair.mp hmem
    have h1 : hh f (polar f x y) (a' • x + b' • y) = 0 := by
      rw [hh_add_right, hh_smul_right, hh_smul_right, hpx0, hpy0, mul_zero, mul_zero, add_zero]
    exact hpp_ne (hab' ▸ h1)

theorem link_vec (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {p w₀ r : Fin 4 → K}
    (h : gram f p w₀ ≠ 0) : ∃ s : K, gram f p (s • w₀ + r) ≠ 0 := by
  have hc : plv_gramTuple f p w₀ r ≠ 0 := plv_gramTuple_ne_zero_of_fst f h
  obtain ⟨s, h₁, -, -⟩ := exists_avoid f hK hq hc hc hc
  exact ⟨s, by rw [← plv_pev_gramTuple f p w₀ r s]; exact h₁⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
