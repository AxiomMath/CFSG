module

public import CFSG.Walter.Ree.Thompson2.Alg.Defs
public import CFSG.Walter.Ree.Thompson2.Alg.Formula

public section

namespace CFSG.Walter.Ree.T2.Alg

variable {k : Type} [Field k]
variable {a : ℕ} {σ : k ≃+* k} {d : k} {S : k → k × k × k}

theorem FE1C.fst (h : FE1C a S) {x : k} (hx : x + 1 ≠ 0) :
    (S x).1 = (S (ι₁ x)).1 * ((x + 1) ^ a)⁻¹ := congrArg Prod.fst (h x hx)

theorem FE1C.snd (h : FE1C a S) {x : k} (hx : x + 1 ≠ 0) :
    (S x).2.1 = (S (ι₁ x)).2.1 * ((x + 1) ^ 2)⁻¹ - (x + 1)⁻¹ :=
  congrArg (fun p => p.2.1) (h x hx)

theorem FE1C.thd (h : FE1C a S) {x : k} (hx : x + 1 ≠ 0) :
    (S x).2.2 = (S (ι₁ x)).2.2 * ((x + 1) ^ (a + 2))⁻¹ :=
  congrArg (fun p => p.2.2) (h x hx)

theorem FE2C.fst (h : FE2C σ d S) {x : k} (hx : x - 1 ≠ 0) :
    (S x).1 = -(S (ι₂ x)).1 - 1 := congrArg Prod.fst (h x hx)

theorem FE2C.snd (h : FE2C σ d S) {x : k} (hx : x - 1 ≠ 0) :
    (S x).2.1 = (S (ι₂ x)).2.1 + (S (ι₂ x)).1 - σ (S (ι₂ x)).1 :=
  congrArg (fun p => p.2.1) (h x hx)

theorem FE2C.thd (h : FE2C σ d S) {x : k} (hx : x - 1 ≠ 0) :
    (S x).2.2 = 1 - d - (S (ι₂ x)).2.2 - (S (ι₂ x)).2.1 - σ (S (ι₂ x)).1 - (S (ι₂ x)).1 +
      (S (ι₂ x)).1 ^ 2 :=
  congrArg (fun p => p.2.2) (h x hx)

variable [CharP k 3]

theorem s1_mul_of_ne (ha : Even a) (h1 : FE1C a S) (h2 : FE2C σ d S) {x : k} (hx : x ≠ 0)
    (hx1 : x - 1 ≠ 0) (hx2 : x + 1 ≠ 0) :
    (S x).1 * (x ^ a - (x ^ 2 - 1) ^ a) = (x - 1) ^ a - x ^ a := by
  have e := klein (f := fun x => (S x).1) (m := fun x => ((x + 1) ^ a)⁻¹) (n := fun _ => 0)
    (ε := -1) (c := fun _ => -1) (fun x hx => by rw [h1.fst hx]; ring)
    (fun x hx => by rw [h2.fst hx]; ring) hx hx1 hx2
  rw [ι₂_add_one hx1, div_pow, ha.neg_pow] at e
  field_simp at e
  have hsq : (x ^ 2 - 1) ^ a = (x - 1) ^ a * (x + 1) ^ a := by rw [← mul_pow]; ring
  rw [hsq]
  linear_combination e

theorem s1_eq (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) (x : k) :
    (S x).1 = ((x - 1) ^ a - x ^ a) / (x ^ a - (x ^ 2 - 1) ^ a) := by
  have ha0 := a_ne_zero haσ
  by_cases hx : x = 0
  · subst hx; rw [h3.2.1]; exact (s1F_zero ha ha0).symm
  by_cases hx1 : x - 1 = 0
  · rw [sub_eq_zero.1 hx1, h3.2.2]; exact (s1F_one ha0).symm
  by_cases hx2 : x + 1 = 0
  · rw [eq_neg_of_add_eq_zero_left hx2, h3.1]; exact (s1F_neg_one ha).symm
  rw [eq_div_iff (D1_ne_zero ha haσ x)]
  exact s1_mul_of_ne ha h1 h2 hx hx1 hx2

theorem s1_mul_eq (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) (x : k) :
    (S x).1 * (x ^ a - (x ^ 2 - 1) ^ a) = (x - 1) ^ a - x ^ a := by
  rw [s1_eq ha haσ h1 h2 h3 x, div_mul_cancel₀ _ (D1_ne_zero ha haσ x)]

theorem fst_eq_s1F (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) (x : k) : (S x).1 = s1F a x :=
  s1_eq ha haσ h1 h2 h3 x

theorem s2_mul_of_ne (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) {x : k} (hx : x ≠ 0) (hx1 : x - 1 ≠ 0)
    (hx2 : x + 1 ≠ 0) :
    (S x).2.1 * -((x ^ 2 - x - 1) * (x ^ 2 + x - 1)) =
      (x - 1) * (x ^ 2 + x - 1) + x ^ 2 * c2F σ a (ι₂ x) - (x - 1) ^ 2 * c2F σ a (-x⁻¹) := by
  have e := klein (f := fun x => (S x).2.1) (m := fun x => ((x + 1) ^ 2)⁻¹)
    (n := fun x => -(x + 1)⁻¹) (ε := 1) (c := fun t => (S t).1 - σ (S t).1)
    (fun x hx => by rw [h1.snd hx]; ring) (fun x hx => by rw [h2.snd hx]; ring) hx hx1 hx2
  have hc : ∀ t, (S t).1 - σ (S t).1 = c2F σ a t := fun t => by
    rw [fst_eq_s1F ha haσ h1 h2 h3 t, c2F]
  simp only [hc] at e
  rw [ι₂_add_one hx1] at e
  generalize c2F σ a (ι₂ x) = C1 at e ⊢
  generalize c2F σ a (-x⁻¹) = C2 at e ⊢
  field_simp at e
  linear_combination e

theorem s2_eq (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) (x : k) : (S x).2.1 = s2F σ a x := by
  have ha0 := a_ne_zero haσ
  by_cases hx : x = 0
  · subst hx; rw [h3.2.1]; exact (s2F_zero ha ha0).symm
  by_cases hx1 : x - 1 = 0
  · rw [sub_eq_zero.1 hx1, h3.2.2]; exact (s2F_one ha ha0).symm
  by_cases hx2 : x + 1 = 0
  · rw [eq_neg_of_add_eq_zero_left hx2, h3.1]; exact (s2F_neg_one ha ha0).symm
  rw [s2F, eq_div_iff (quad_ne_zero (sq_ne_neg_one ha haσ) x)]
  exact s2_mul_of_ne ha haσ h1 h2 h3 hx hx1 hx2

theorem s3_mul_of_ne (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) {x : k} (hx : x ≠ 0) (hx1 : x - 1 ≠ 0)
    (hx2 : x + 1 ≠ 0) :
    (S x).2.2 * (x ^ (2 + a) - (x ^ 2 - 1) ^ (2 + a)) =
      x ^ (2 + a) * c3F σ a d (ι₂ x) - (x - 1) ^ (2 + a) * c3F σ a d (-x⁻¹) := by
  have e := klein (f := fun x => (S x).2.2) (m := fun x => ((x + 1) ^ (a + 2))⁻¹)
    (n := fun _ => 0) (ε := -1)
    (c := fun t => 1 - d - (S t).2.1 - σ (S t).1 - (S t).1 + (S t).1 ^ 2)
    (fun x hx => by rw [h1.thd hx]; ring) (fun x hx => by rw [h2.thd hx]; ring) hx hx1 hx2
  have hc : ∀ t, 1 - d - (S t).2.1 - σ (S t).1 - (S t).1 + (S t).1 ^ 2 = c3F σ a d t :=
    fun t => by rw [fst_eq_s1F ha haσ h1 h2 h3 t, s2_eq ha haσ h1 h2 h3 t, c3F]
  simp only [hc] at e
  rw [ι₂_add_one hx1, div_pow, (ha.add even_two).neg_pow] at e
  generalize c3F σ a d (ι₂ x) = C1 at e ⊢
  generalize c3F σ a d (-x⁻¹) = C2 at e ⊢
  field_simp at e
  rw [add_comm 2 a]
  have hsq : (x ^ 2 - 1) ^ (a + 2) = (x - 1) ^ (a + 2) * (x + 1) ^ (a + 2) := by
    rw [← mul_pow]; ring
  rw [hsq]
  linear_combination e

theorem s3_eq (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) {x : k}
    (hD : x ^ (2 + a) - (x ^ 2 - 1) ^ (2 + a) ≠ 0) : (S x).2.2 = (sFormula σ a d x).2.2 := by
  have he : Even (2 + a) := even_two.add ha
  have he0 : 2 + a ≠ 0 := by omega
  by_cases h3x : x ^ 3 = x
  · rw [sFormula, ite_eq_left h3x]
    rcases pow_three_eq_self_iff.1 h3x with rfl | rfl | rfl
    · rw [h3.2.1, phi3, s1F_zero he he0]; ring
    · rw [h3.2.2, phi3, s1F_one he0]; ring
    · rw [h3.1, phi3, s1F_neg_one he]; ring
  · rw [sFormula, ite_eq_right h3x, s3F, eq_div_iff hD]
    have hx : x ≠ 0 := by rintro rfl; simp at h3x
    have hx1 : x - 1 ≠ 0 := by intro h; rw [sub_eq_zero.1 h] at h3x; simp at h3x
    have hx2 : x + 1 ≠ 0 := by
      intro h; rw [eq_neg_of_add_eq_zero_left h] at h3x; norm_num at h3x
    exact s3_mul_of_ne ha haσ h1 h2 h3 hx hx1 hx2

theorem S_eq_sFormula (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hD3 : ∀ x : k, x ^ (2 + a) - (x ^ 2 - 1) ^ (2 + a) ≠ 0) (h1 : FE1C a S)
    (h2 : FE2C σ d S) (h3 : GF3C d S) : S = sFormula σ a d :=
  funext fun x => Prod.ext (s1_eq ha haσ h1 h2 h3 x)
    (Prod.ext (s2_eq ha haσ h1 h2 h3 x) (s3_eq ha haσ h1 h2 h3 (hD3 x)))

theorem S_eq_of (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hD3 : ∀ x : k, x ^ (2 + a) - (x ^ 2 - 1) ^ (2 + a) ≠ 0) {S S' : k → k × k × k}
    (h : FE1C a S ∧ FE2C σ d S ∧ GF3C d S) (h' : FE1C a S' ∧ FE2C σ d S' ∧ GF3C d S') :
    S = S' :=
  (S_eq_sFormula ha haσ hD3 h.1 h.2.1 h.2.2).trans
    (S_eq_sFormula ha haσ hD3 h'.1 h'.2.1 h'.2.2).symm

theorem S_eq_sFormula_of_sigmaTwo (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hσ2 : ∀ x : k, σ x * x ^ 2 = 1 → x = 1) (h1 : FE1C a S) (h2 : FE2C σ d S)
    (h3 : GF3C d S) : S = sFormula σ a d :=
  S_eq_sFormula ha haσ (D3_ne_zero ha haσ hσ2) h1 h2 h3

theorem S_eq_sFormula_of_ree (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hσ : ∀ x : k, σ (σ x) = x ^ 3) (h1 : FE1C a S) (h2 : FE2C σ d S) (h3 : GF3C d S) :
    S = sFormula σ a d :=
  S_eq_sFormula_of_sigmaTwo ha haσ (sigmaTwo_of_ree hσ) h1 h2 h3

theorem S_eq_of_ree (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hσ : ∀ x : k, σ (σ x) = x ^ 3) {S S' : k → k × k × k}
    (h : FE1C a S ∧ FE2C σ d S ∧ GF3C d S) (h' : FE1C a S' ∧ FE2C σ d S' ∧ GF3C d S') :
    S = S' :=
  S_eq_of ha haσ (D3_ne_zero ha haσ (sigmaTwo_of_ree hσ)) h h'

end CFSG.Walter.Ree.T2.Alg
