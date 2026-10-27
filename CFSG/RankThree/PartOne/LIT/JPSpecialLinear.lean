module

public import CFSG.RankThree.PartOne.LIT.CohomologyBasic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne.LIT.JP

open Matrix Module SpecialLinearGroup
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] def prodHom (n : ℕ) (K : Type*) [Field K] : (Fin n → Kˣ) →* Kˣ where
  toFun d := ∏ i, d i
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

@[expose] def torusSub (n : ℕ) (K : Type*) [Field K] : Subgroup (Fin n → Kˣ) := (prodHom n K).ker

@[expose] def diagSL {n : ℕ} {K : Type*} [Field K] (d : Fin n → Kˣ) (hd : ∏ i, d i = 1) :
    SpecialLinearGroup (Fin n) K :=
  ⟨Matrix.diagonal (fun i => ((d i : Kˣ) : K)), by
    rw [det_diagonal, ← Units.coe_prod, hd, Units.val_one]⟩

theorem diagSL_mul {n : ℕ} {K : Type*} [Field K] (d e : Fin n → Kˣ) (hd : ∏ i, d i = 1)
    (he : ∏ i, e i = 1) (hde : ∏ i, (d * e) i = 1) :
    diagSL (d * e) hde = (diagSL d hd : SpecialLinearGroup (Fin n) K) * diagSL e he := by
  apply Subtype.ext
  show Matrix.diagonal (fun i => (((d * e) i : Kˣ) : K)) =
    Matrix.diagonal (fun i => ((d i : Kˣ) : K)) * Matrix.diagonal (fun i => ((e i : Kˣ) : K))
  rw [diagonal_mul_diagonal]
  rfl

@[expose] def torusHom (n : ℕ) (K : Type*) [Field K] :
    torusSub n K →* SpecialLinearGroup (Fin n) K where
  toFun d := diagSL d.1 (MonoidHom.mem_ker.mp d.2)
  map_one' := by
    apply Subtype.ext
    simp [diagSL]
  map_mul' a b := diagSL_mul a.1 b.1 _ _ _

theorem torusHom_coe (n : ℕ) (K : Type*) [Field K] (d : torusSub n K) :
    ((torusHom n K d : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => ((d.1 i : Kˣ) : K)) := rfl

theorem card_torusSub_ne_zero {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ((Nat.card (torusSub n (ZMod p)) : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hdvd : Nat.card (torusSub n (ZMod p)) ∣ (p - 1) ^ n := by
    have h1 := Subgroup.card_subgroup_dvd_card (torusSub n (ZMod p))
    have h2 : Nat.card (Fin n → (ZMod p)ˣ) = (p - 1) ^ n := by
      rw [Nat.card_pi]
      simp [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
    rwa [h2] at h1
  have := (Fact.out : p.Prime).dvd_of_dvd_pow (h.trans hdvd)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have := Nat.le_of_dvd (by omega) this
  omega

theorem diag2n_eq_torusHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : ZMod p) (ha : a ≠ 0) :
    ∃ d : torusSub n (ZMod p), torusHom n (ZMod p) d = diag2n hij a ha := by
  let u : (ZMod p)ˣ := Units.mk0 a ha
  let d : Fin n → (ZMod p)ˣ := fun k => if k = i then u else if k = j then u⁻¹ else 1
  have hd : ∏ k, d k = 1 := by
    apply Units.ext
    have := (diag2n hij a ha).2
    rw [diag2n_coe, det_diagonal] at this
    rw [Units.coe_prod]
    simpa [d, u, apply_ite (fun x : (ZMod p)ˣ => (x : ZMod p))] using this
  refine ⟨⟨d, MonoidHom.mem_ker.mpr hd⟩, ?_⟩
  apply Subtype.ext
  rw [torusHom_coe, diag2n_coe]
  congr 1
  funext k
  simp only [d, u]
  split_ifs <;> simp

theorem natCast_ne_zero_of_not_dvd {m : ℕ} (h : ¬ p ∣ m) : ((m : ℕ) : ZMod p) ≠ 0 :=
  fun h0 => h ((ZMod.natCast_eq_zero_iff m p).mp h0)

theorem exists_good_unit (hp : 5 ≤ p) : ∃ a : ZMod p, a ≠ 0 ∧ a ^ 2 ≠ 1 ∧ a ^ 3 ≠ 1 := by
  have hpp : p.Prime := Fact.out
  by_cases h7 : p = 7
  · have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_not_dvd (by rw [h7]; decide)
    have h8 : ((8 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_not_dvd (by rw [h7]; decide)
    have h26 : ((26 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_not_dvd (by rw [h7]; decide)
    refine ⟨3, by simpa using h3, ?_, ?_⟩
    · intro h
      apply h8
      push_cast
      linear_combination h
    · intro h
      apply h26
      push_cast
      linear_combination h
  · have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_not_dvd (fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega)
    have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_not_dvd (fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega)
    have h7' : ((7 : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_not_dvd (fun h => by
      exact h7 ((Nat.prime_dvd_prime_iff_eq hpp (by decide)).mp h))
    refine ⟨2, by simpa using h2, ?_, ?_⟩
    · intro h
      apply h3
      push_cast
      linear_combination h
    · intro h
      apply h7'
      push_cast
      linear_combination h

theorem transvection_mulVec_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (s : ZMod p)
    (w : Fin n → ZMod p) (k : Fin n) :
    ((transvection hij s : SpecialLinearGroup (Fin n) (ZMod p)).1 *ᵥ w) k =
      w k + (if k = i then s * w j else 0) := by
  rw [transvection_coe, add_mulVec, one_mulVec, single_mulVec_eq]
  simp [Pi.single_apply]

theorem diag2n_mul_transvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : ZMod p) (ha : a ≠ 0)
    (s : ZMod p) :
    diag2n hij a ha * transvection hij s = transvection hij (a ^ 2 * s) * diag2n hij a ha := by
  apply Subtype.ext
  show Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) *
      Matrix.transvection i j s =
    Matrix.transvection i j (a ^ 2 * s) *
      Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1)
  ext x y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h : i = x ∧ j = y
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, hij.symm]
    field_simp
  · by_cases hxy : x = y
    · subst hxy
      simp [h]
    · simp [h, hxy]

theorem transvection_fixes (hp : 5 ≤ p) {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (B : Submodule (ZMod p) V) (θ : B ≃ₗ[ZMod p] (Fin n → ZMod p))
    (ρ : SpecialLinearGroup (Fin n) (ZMod p) →* (V ≃ₗ[ZMod p] V))
    (hB : ∀ (y : SpecialLinearGroup (Fin n) (ZMod p)) (b : B),
      ρ y (b : V) = ((θ.symm (y.1 *ᵥ θ b) : B) : V))
    (hq : ∀ y v, ρ y v - v ∈ B) {v₁ : V}
    (hT : ∀ d : torusSub n (ZMod p), ρ (torusHom n (ZMod p) d) v₁ = v₁)
    {i j : Fin n} (hij : i ≠ j) (s : ZMod p) :
    ρ (transvection hij s) v₁ = v₁ := by
  obtain ⟨a, ha0, ha2, ha3⟩ := exists_good_unit hp
  obtain ⟨d, hd⟩ := diag2n_eq_torusHom hij a ha0
  set t : SpecialLinearGroup (Fin n) (ZMod p) := diag2n hij a ha0 with ht
  have htv : ρ t v₁ = v₁ := by rw [← hd]; exact hT d
  let δ : ZMod p → B := fun s => ⟨ρ (transvection hij s) v₁ - v₁, hq _ _⟩
  let c : Fin n → ZMod p → ZMod p := fun k s => θ (δ s) k
  have hadd : ∀ k s r, c k (s + r) = c k s + c k r + (if k = i then s * c j r else 0) := by
    intro k s r
    have h1 : ρ (transvection hij (s + r)) v₁ - v₁ =
        (ρ (transvection hij s) v₁ - v₁) +
          ρ (transvection hij s) (ρ (transvection hij r) v₁ - v₁) := by
      rw [transvection_add, map_mul]
      simp [LinearEquiv.mul_apply, map_sub]
    have h2 : δ (s + r) = δ s + θ.symm ((transvection hij s).1 *ᵥ θ (δ r)) := by
      apply Subtype.ext
      show ρ (transvection hij (s + r)) v₁ - v₁ = _
      rw [h1]
      have := hB (transvection hij s) (δ r)
      simp only [Submodule.coe_add]
      rw [← this]
    have h3 := congrArg (fun b => θ b k) h2
    simp only [map_add, LinearEquiv.apply_symm_apply, Pi.add_apply] at h3
    rw [show c k (s + r) = θ (δ (s + r)) k from rfl, h3, transvection_mulVec_apply]
    show _ = c k s + c k r + _
    simp only [c]
    ring
  have htor : ∀ k s, c k (a ^ 2 * s) =
      (if k = i then a else if k = j then a⁻¹ else 1) * c k s := by
    intro k s
    have h1 : ρ t (ρ (transvection hij s) v₁) = ρ (transvection hij (a ^ 2 * s)) v₁ := by
      have := congrArg (fun g => ρ g v₁) (diag2n_mul_transvection hij a ha0 s)
      simp only [map_mul, LinearEquiv.mul_apply] at this
      rw [← ht, htv] at this
      exact this
    have h2 : δ (a ^ 2 * s) = θ.symm (t.1 *ᵥ θ (δ s)) := by
      apply Subtype.ext
      show ρ (transvection hij (a ^ 2 * s)) v₁ - v₁ = _
      rw [← h1, ← hB t (δ s)]
      show ρ t (ρ (transvection hij s) v₁) - v₁ = ρ t (ρ (transvection hij s) v₁ - v₁)
      rw [map_sub, htv]
    have h3 := congrArg (fun b => θ b k) h2
    simp only [LinearEquiv.apply_symm_apply] at h3
    show θ (δ (a ^ 2 * s)) k = _
    rw [h3, ht, diag2n_coe, mulVec_diagonal]
  have hlin : ∀ k, k ≠ i → ∀ s, c k s = s * c k 1 := by
    intro k hk s
    exact additive_eq_mul (c k) (fun s r => by simpa [hk] using hadd k s r) s
  have hzero : ∀ k, k ≠ i → ∀ s, c k s = 0 := by
    intro k hk s
    rw [hlin k hk s]
    have h := htor k 1
    rw [hlin k hk (a ^ 2 * 1), hlin k hk 1] at h
    simp only [hk, ite_false] at h
    have key : (a ^ 2 - (if k = j then a⁻¹ else 1)) * c k 1 = 0 := by
      by_cases hkj : k = j
      · simp only [hkj, ite_true] at h ⊢
        linear_combination h
      · simp only [hkj, ite_false] at h ⊢
        linear_combination h
    have hne : a ^ 2 - (if k = j then a⁻¹ else 1) ≠ 0 := by
      by_cases hkj : k = j
      · simp only [hkj, ite_true]
        intro h0
        apply ha3
        field_simp at h0
        linear_combination h0
      · simp only [hkj, ite_false]
        exact sub_ne_zero.mpr ha2
    have := (mul_eq_zero.mp key).resolve_left hne
    rw [this, mul_zero]
  have hi : ∀ s, c i s = 0 := by
    have hc1 : ∀ s r, c i (s + r) = c i s + c i r := by
      intro s r
      have := hadd i s r
      simp only [ite_true, hzero j hij.symm r, mul_zero, add_zero] at this
      exact this
    intro s
    rw [additive_eq_mul (c i) hc1 s]
    have h := htor i 1
    rw [additive_eq_mul (c i) hc1 (a ^ 2 * 1), additive_eq_mul (c i) hc1 1] at h
    simp only [ite_true] at h
    have key : (a ^ 2 - a) * c i 1 = 0 := by linear_combination h
    have hne : a ^ 2 - a ≠ 0 := by
      intro h0
      have : a * (a - 1) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp this with h1 | h1
      · exact ha0 h1
      · apply ha2
        have : a = 1 := by linear_combination h1
        rw [this]; norm_num
    have := (mul_eq_zero.mp key).resolve_left hne
    rw [this, mul_zero]
  have hδ : δ s = 0 := by
    apply θ.injective
    funext k
    by_cases hk : k = i
    · subst hk; simpa using hi s
    · simpa using hzero k hk s
  have := congrArg Subtype.val hδ
  simpa [δ, sub_eq_zero] using this

theorem jp_special_linear (hp : 5 ≤ p) {n : ℕ} (hn : 2 ≤ n) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (B : Submodule (ZMod p) V) (θ : B ≃ₗ[ZMod p] (Fin n → ZMod p))
    (ρ : SpecialLinearGroup (Fin n) (ZMod p) →* (V ≃ₗ[ZMod p] V))
    (hB : ∀ (y : SpecialLinearGroup (Fin n) (ZMod p)) (b : B),
      ρ y (b : V) = ((θ.symm (y.1 *ᵥ θ b) : B) : V))
    (hq : ∀ y v, ρ y v - v ∈ B) (v₀ : V) :
    ∃ v : V, v - v₀ ∈ B ∧ ∀ y, ρ y v = v := by
  obtain ⟨v₁, hv₁B, hv₁⟩ := exists_fixed_vector_of_index (ρ.comp (torusHom n (ZMod p))) B
    (fun g v => hq _ v) ⊥ (by rw [Subgroup.index_bot]; exact card_torusSub_ne_zero n)
    (v₁ := v₀) (fun h hh => by rw [Subgroup.mem_bot.mp hh, map_one]; rfl)
  refine ⟨v₁, hv₁B, fun y => ?_⟩
  have : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  refine SpecialLinearGroup.diagonal_transvection_induction' (fun M => ρ M v₁ = v₁) y ?_ ?_ ?_
  · intro i j hij c hc
    obtain ⟨d, hd⟩ := diag2n_eq_torusHom hij c hc
    show ρ (diag2n hij c hc) v₁ = v₁
    rw [← hd]
    exact hv₁ d
  · intro i j hij a
    exact transvection_fixes hp B θ ρ hB hq hv₁ hij a
  · intro A B' hA hB'
    show ρ (A * B') v₁ = v₁
    rw [map_mul, LinearEquiv.mul_apply]
    have hB'' : ρ B' v₁ = v₁ := hB'
    have hA' : ρ A v₁ = v₁ := hA
    rw [hB'', hA']

end CFSG.RankThree.PartOne.LIT.JP
