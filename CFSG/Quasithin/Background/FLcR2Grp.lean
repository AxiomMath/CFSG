module

public import CFSG.Quasithin.Background.FLcP0Main
public import CFSG.Quasithin.Background.FLcR2Mat

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

variable {G : Type} [Group G]

abbrev Kc (L S UL : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (UL : Set G) ⊓ (L ⊔ S)

@[expose] def Dec (L S UL : Subgroup G) (x : G) (l : ↥L) : Prop :=
  ∃ c ∈ Kc L S UL, x = (l : G) * c

theorem pow_three_of_odd {x : G} (hodd : Odd (orderOf x)) {k : ℕ} (hk : (x ^ 6) ^ 2 ^ k = 1) :
    x ^ 3 = 1 := by
  have hdvd : orderOf x ∣ 3 * 2 ^ (k + 1) := by
    apply orderOf_dvd_of_pow_eq_one
    have e : 3 * 2 ^ (k + 1) = 6 * 2 ^ k := by ring
    rw [e, pow_mul]
    exact hk
  have hcop : Nat.Coprime (orderOf x) (2 ^ (k + 1)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    obtain ⟨j, hj⟩ := hodd
    omega
  have h3 : orderOf x ∣ 3 := hcop.dvd_of_dvd_mul_right hdvd
  exact orderOf_dvd_iff_pow_eq_one.1 h3

theorem pow_two_pow_cases {M : Type*} [Monoid M] {s : M} (hs : s * s * s = 1) (k : ℕ) :
    s ^ 2 ^ k = s ∨ s ^ 2 ^ k = s * s := by
  induction k with
  | zero => exact Or.inl (by simp)
  | succ k ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h | h
    · rw [h]
      exact Or.inr (pow_two s)
    · rw [h]
      left
      calc (s * s) ^ 2 = s * (s * s * s) := by rw [pow_two]; simp only [mul_assoc]
        _ = s := by rw [hs, mul_one]

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem kc_pgroup [Finite G] : IsPGroup 2 ↥(Kc L S UL) :=
  (kc_facts D.S_norm D.S2 D.L_le D.S_le D.K2).1

theorem kc_norm [Finite G] : ∀ x ∈ L ⊔ S, ∀ k ∈ Kc L S UL, x * k * x⁻¹ ∈ Kc L S UL :=
  (kc_facts D.S_norm D.S2 D.L_le D.S_le D.K2).2

theorem dec_mul [Finite G] {x₁ x₂ : G} {l₁ l₂ : ↥L} (h₁ : Dec L S UL x₁ l₁)
    (h₂ : Dec L S UL x₂ l₂) : Dec L S UL (x₁ * x₂) (l₁ * l₂) := by
  obtain ⟨c₁, hc₁, rfl⟩ := h₁
  obtain ⟨c₂, hc₂, rfl⟩ := h₂
  refine ⟨(l₂ : G)⁻¹ * c₁ * (l₂ : G) * c₂, ?_, ?_⟩
  · refine (Kc L S UL).mul_mem ?_ hc₂
    have := D.kc_norm ((l₂ : G)⁻¹) ((L ⊔ S).inv_mem (Subgroup.mem_sup_left l₂.2)) c₁ hc₁
    simpa [mul_assoc] using this
  · show (l₁ : G) * c₁ * ((l₂ : G) * c₂) =
      (l₁ : G) * (l₂ : G) * ((l₂ : G)⁻¹ * c₁ * (l₂ : G) * c₂)
    group

theorem dec_inv [Finite G] {x : G} {l : ↥L} (h : Dec L S UL x l) : Dec L S UL x⁻¹ l⁻¹ := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨(l : G) * c⁻¹ * (l : G)⁻¹, ?_, ?_⟩
  · exact D.kc_norm (l : G) (Subgroup.mem_sup_left l.2) c⁻¹ ((Kc L S UL).inv_mem hc)
  · show ((l : G) * c)⁻¹ = (l : G)⁻¹ * ((l : G) * c⁻¹ * (l : G)⁻¹)
    group

theorem dec_pow [Finite G] {x : G} {l : ↥L} (h : Dec L S UL x l) (k : ℕ) :
    Dec L S UL (x ^ k) (l ^ k) := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', h'⟩ := exists_pow_mul_of_normal D.kc_norm (Subgroup.mem_sup_left l.2) hc k
  exact ⟨c', hc', h'⟩

omit D in
theorem dec_self (l : ↥L) : Dec L S UL (l : G) l := ⟨1, (Kc L S UL).one_mem, by simp⟩

theorem alpha_eq_one_of_mem_centralizer {a : ↥L}
    (ha : (a : G) ∈ Subgroup.centralizer (UL : Set G)) : D.α a = 1 := by
  have h1 : ∀ v : Vt n, mat (D.α a) *ᵥ v = v := by
    intro v
    set u : ↥UL := D.β.symm (Multiplicative.ofAdd v) with hu
    have hβu : Multiplicative.toAdd (D.β u) = v := by
      rw [hu, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have hc : (u : G) = (a : G) * (u : G) * (a : G)⁻¹ :=
      eq_mul_inv_iff_mul_eq.2 (Subgroup.mem_centralizer_iff.1 ha (u : G) u.2)
    have h2 := D.rel a u u hc
    rw [hβu] at h2
    exact h2.symm
  apply Subtype.ext
  ext r c
  have h := congrFun (h1 (Pi.single c 1)) r
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h

theorem mem_parab_of_alpha {i : ℕ} (l : ↥L) (hl : D.α l ∈ Qn n i) :
    (l : G) ∈ parab (L ⊔ S) n W i :=
  mem_parab.2 ⟨Subgroup.mem_sup_left l.2, fun j hj1 hjn hji =>
    (D.mem_normalizer_W hj1 hjn l).2 (mem_Qn.1 hl j hj1 hjn hji)⟩

theorem alpha_mem_Qn {i : ℕ} {x : G} (hx : x ∈ parab (L ⊔ S) n W i) {l : ↥L}
    (hd : Dec L S UL x l) : D.α l ∈ Qn n i := by
  obtain ⟨c, hc, hxlc⟩ := hd
  exact mem_Qn.2 fun j hj1 hjn hji =>
    D.stab_of_decomp hxlc hc.1 hj1 hjn ((mem_parab.1 hx).2 j hj1 hjn hji)

theorem two_elt_of_Ut [Finite G] {x : G} {l : ↥L} (hd : Dec L S UL x l) (hU : D.α l ∈ Ut n) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨c, hc, hxlc⟩ := hd
  obtain ⟨a, ha⟩ := isPGroup_Ut (by have := D.three_le; omega) ⟨D.α l, hU⟩
  have ha' : (D.α l) ^ (2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hker : ((l ^ 2 ^ a : ↥L) : G) ∈ Subgroup.centralizer (UL : Set G) := by
    apply D.ker
    rw [map_pow]
    exact ha'
  have hlpow : ((l ^ 2 ^ a : ↥L) : G) = (l : G) ^ 2 ^ a := rfl
  obtain ⟨b, hb⟩ := D.K2 ⟨(l : G) ^ 2 ^ a, by rw [← hlpow]; exact (l ^ 2 ^ a).2,
    by rw [← hlpow]; exact hker⟩
  have hb' : ((l : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  obtain ⟨c', hc', hxm⟩ :=
    exists_pow_mul_of_normal D.kc_norm (Subgroup.mem_sup_left l.2) hc (2 ^ (a + b))
  have hlm : (l : G) ^ 2 ^ (a + b) = 1 := by
    rw [pow_add, pow_mul, hb']
  rw [hlm, one_mul] at hxm
  obtain ⟨d, hd⟩ := D.kc_pgroup ⟨c', hc'⟩
  have hd' : c' ^ 2 ^ d = 1 := by
    have := congrArg Subtype.val hd
    simpa using this
  refine ⟨a + b + d, ?_⟩
  rw [← hxlc] at hxm
  rw [pow_add, pow_mul, hxm, hd']

theorem two_elt_of_blk [Finite G] {i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n}
    (hP : P.val + 1 = i) (hQ : Q.val = i) {x : G} (hx : x ∈ parab (L ⊔ S) n W i) {l : ↥L}
    (hd : Dec L S UL x l) (hb : blk P Q (D.α l) = 1) : ∃ k : ℕ, x ^ 2 ^ k = 1 :=
  D.two_elt_of_Ut hd (mem_Ut_of_blk_one hi hin hP hQ (D.alpha_mem_Qn hx hd) hb)

theorem inv_property [Finite G] {i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n}
    (hP : P.val + 1 = i) (hQ : Q.val = i) {y : G} {ly : ↥L} (hy : y ∈ parab (L ⊔ S) n W i)
    (hdy : Dec L S UL y ly) {η : SLt n} (hη : D.α ly = η) (hηη : η * η = 1)
    (hηb : blk P Q η = tau2) {x : G} (hx : x ∈ parab (L ⊔ S) n W i) (hodd : Odd (orderOf x)) :
    ∃ k : ℕ, (y * x * y⁻¹ * x) ^ 2 ^ k = 1 := by
  have hne : P ≠ Q := fun h => by rw [h] at hP; omega
  obtain ⟨lx, cx, hcx, hxl⟩ := D.decomp (mem_parab.1 hx).1
  have hdx : Dec L S UL x lx := ⟨cx, hcx, hxl⟩
  have hX : D.α lx ∈ Qn n i := D.alpha_mem_Qn hx hdx
  have hY : D.α ly ∈ Qn n i := D.alpha_mem_Qn hy hdy
  have hη' : η ∈ Qn n i := hη ▸ hY
  have hblk : ∀ {a b : SLt n}, a ∈ Qn n i → b ∈ Qn n i →
      blk P Q (a * b) = blk P Q a * blk P Q b := fun ha hb => blk_mul_Qn hi hin hP hQ ha hb
  have hx6 : x ^ 6 ∈ parab (L ⊔ S) n W i := (parab (L ⊔ S) n W i).pow_mem hx 6
  have hd6 : Dec L S UL (x ^ 6) (lx ^ 6) := D.dec_pow hdx 6
  have hb6 : blk P Q (D.α (lx ^ 6)) = 1 := by
    rw [map_pow, blk_pow_Qn hi hin hP hQ hX]
    refine gl2_pow_six _ (blk P Q (D.α lx)⁻¹) ?_
    rw [← hblk hX ((Qn n i).inv_mem hX), mul_inv_cancel]
    exact blk_one hne
  obtain ⟨k, hk⟩ := D.two_elt_of_blk hi hin hP hQ hx6 hd6 hb6
  have hx3 : x ^ 3 = 1 := pow_three_of_odd hodd hk
  have hα3 : D.α (lx ^ 3) = 1 := by
    obtain ⟨c3, hc3, h3⟩ := D.dec_pow hdx 3
    rw [hx3] at h3
    apply D.alpha_eq_one_of_mem_centralizer
    have h4 : ((lx ^ 3 : ↥L) : G) = c3⁻¹ := eq_inv_of_mul_eq_one_left h3.symm
    rw [h4]
    exact (Subgroup.centralizer (UL : Set G)).inv_mem hc3.1
  have hB3 : (blk P Q (D.α lx)) ^ 3 = 1 := by
    rw [← blk_pow_Qn hi hin hP hQ hX, ← map_pow, hα3]
    exact blk_one hne
  have hdo : Dec L S UL (y * x * y⁻¹ * x) (ly * lx * ly⁻¹ * lx) :=
    D.dec_mul (D.dec_mul (D.dec_mul hdy hdx) (D.dec_inv hdy)) hdx
  have hηi : D.α ly⁻¹ = η := by
    rw [map_inv, hη]
    exact inv_eq_of_mul_eq_one_right hηη
  have hηiQ : D.α ly⁻¹ ∈ Qn n i := hηi ▸ hη'
  have hdoα : blk P Q (D.α (ly * lx * ly⁻¹ * lx)) = 1 := by
    rw [map_mul, map_mul, map_mul, hηi, hη]
    rw [hblk ((Qn n i).mul_mem ((Qn n i).mul_mem hη' hX) hη') hX,
      hblk ((Qn n i).mul_mem hη' hX) hη', hblk hη' hX, hηb]
    exact gl2_key _ hB3
  have hyP : y⁻¹ ∈ parab (L ⊔ S) n W i := (parab (L ⊔ S) n W i).inv_mem hy
  have hdoP : y * x * y⁻¹ * x ∈ parab (L ⊔ S) n W i :=
    (parab (L ⊔ S) n W i).mul_mem ((parab (L ⊔ S) n W i).mul_mem
      ((parab (L ⊔ S) n W i).mul_mem hy hx) hyP) hx
  exact D.two_elt_of_blk hi hin hP hQ hdoP hdo hdoα

end P0Setup

end CFSG.Quasithin.FLc
