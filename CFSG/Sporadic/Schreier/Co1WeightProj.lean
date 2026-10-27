module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Sporadic.Co1Schreier.WeightProj

open Matrix

variable {K : Type*} [Field K] {w : K} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)

@[expose] def chi (w : K) (f b : Fin 6 → ZMod 3) : K := w ^ (f ⬝ᵥ b).val

include hw3 in
theorem w_pow_val_add (m n : ZMod 3) : w ^ (m + n).val = w ^ m.val * w ^ n.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (m.val + n.val) 3, pow_add, pow_mul, hw3, one_pow, one_mul]

include hw3 in
theorem chi_add (f b b' : Fin 6 → ZMod 3) : chi w f (b + b') = chi w f b * chi w f b' := by
  unfold chi
  rw [dotProduct_add, w_pow_val_add hw3]

include hw3 in
theorem chi_add_left (f f' b : Fin 6 → ZMod 3) : chi w (f + f') b = chi w f b * chi w f' b := by
  unfold chi
  rw [add_dotProduct, w_pow_val_add hw3]

theorem chi_zero (f : Fin 6 → ZMod 3) : chi w f 0 = 1 := by
  unfold chi
  rw [dotProduct_zero, ZMod.val_zero, pow_zero]

theorem chi_zero_left (b : Fin 6 → ZMod 3) : chi w 0 b = 1 := by
  unfold chi
  rw [zero_dotProduct, ZMod.val_zero, pow_zero]

include hw3 in
theorem chi_neg (f b : Fin 6 → ZMod 3) : chi w f (-b) * chi w f b = 1 := by
  rw [← chi_add hw3, neg_add_cancel, chi_zero]

theorem card_three_pow_six [CharP K 2] : ((Fintype.card (Fin 6 → ZMod 3) : ℕ) : K) = 1 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, show (3 ^ 6 : ℕ) = 2 * 364 + 1 by norm_num,
    Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, zero_add, Nat.cast_one]

include hw3 hw1 in
theorem sum_chi [CharP K 2] (h : Fin 6 → ZMod 3) : ∑ b, chi w h b = if h = 0 then 1 else 0 := by
  split_ifs with h0
  · subst h0
    simp only [chi_zero_left, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact card_three_pow_six
  · obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      exact h0 (funext hne)
    set b₀ : Fin 6 → ZMod 3 := Pi.single i (h i)
    have hb₀ : h ⬝ᵥ b₀ = 1 := by
      rw [dotProduct_single]
      revert hi
      generalize h i = x
      revert x
      decide
    have hshift : ∑ b, chi w h b = chi w h b₀ * ∑ b, chi w h b := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.addLeft b₀) _ _ fun b => by
        rw [Equiv.coe_addLeft, chi_add hw3]).symm
    have hw : chi w h b₀ = w := by
      unfold chi
      rw [hb₀, ZMod.val_one, pow_one]
    rw [hw] at hshift
    have : (1 - w) * ∑ b, chi w h b = 0 := by rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (sub_eq_zero.mp h1).symm hw1
    · exact h1

variable {n : ℕ} (R : (Fin 6 → ZMod 3) → Matrix (Fin n) (Fin n) K)

@[expose] def wtSpace (f : Fin 6 → ZMod 3) : Submodule K (Fin n → K) where
  carrier := {v | ∀ b, R b *ᵥ v = chi w f b • v}
  add_mem' := by
    intro v v' hv hv' b
    change ∀ b, _ at hv hv'
    rw [mulVec_add, hv b, hv' b, smul_add]
  zero_mem' := fun b => by rw [mulVec_zero, smul_zero]
  smul_mem' := by
    intro c v hv b
    change ∀ b, _ at hv
    rw [mulVec_smul, hv b, smul_comm]

theorem mem_wtSpace {f : Fin 6 → ZMod 3} {v : Fin n → K} :
    v ∈ wtSpace (w := w) R f ↔ ∀ b, R b *ᵥ v = chi w f b • v := Iff.rfl

@[expose] def wtProj (f : Fin 6 → ZMod 3) (v : Fin n → K) : Fin n → K :=
  ∑ b, chi w f (-b) • (R b *ᵥ v)

variable {R} (hR : ∀ b b', R (b + b') = R b * R b') (hR0 : R 0 = 1)

include hw3 hR in
theorem wtProj_mulVec_mem (f : Fin 6 → ZMod 3) (v : Fin n → K) :
    wtProj (w := w) R f v ∈ wtSpace (w := w) R f := by
  intro c
  unfold wtProj
  rw [mulVec_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft c) _ _ fun b => ?_
  rw [Equiv.coe_addLeft, mulVec_smul, mulVec_mulVec, ← hR, smul_smul]
  congr 1
  have h1 := chi_neg hw3 f c
  have h2 : chi w f (-(c + b)) = chi w f (-c) * chi w f (-b) := by
    rw [neg_add, chi_add hw3]
  rw [h2, ← mul_assoc, mul_comm (chi w f c), h1, one_mul]

include hw3 hw1 in
theorem wtProj_of_mem [CharP K 2] {f g : Fin 6 → ZMod 3} {v : Fin n → K}
    (hv : v ∈ wtSpace (w := w) R f) :
    wtProj (w := w) R g v = if g = f then v else 0 := by
  unfold wtProj
  have : ∀ b, chi w g (-b) • (R b *ᵥ v) = chi w (f - g) b • v := by
    intro b
    rw [hv b, smul_smul]
    congr 1
    unfold chi
    rw [← w_pow_val_add hw3, dotProduct_neg, sub_dotProduct,
      show -(g ⬝ᵥ b) + f ⬝ᵥ b = f ⬝ᵥ b - g ⬝ᵥ b by ring]
  simp only [this, ← Finset.sum_smul, sum_chi hw3 hw1, sub_eq_zero]
  split_ifs with h1 h2 h2
  · rw [one_smul]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [zero_smul]

include hw3 hw1 hR0 in
theorem sum_wtProj [CharP K 2] (v : Fin n → K) : ∑ f, wtProj (w := w) R f v = v := by
  unfold wtProj
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have : ∀ b : Fin 6 → ZMod 3, ∑ f, chi w f (-b) = if b = 0 then 1 else 0 := by
    intro b
    have := sum_chi hw3 hw1 (-b)
    simp only [chi, dotProduct_comm _ (-b)] at this ⊢
    simp only [this, neg_eq_zero]
  simp only [this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, hR0, one_mulVec]

@[expose] noncomputable def wtEquiv [CharP K 2] :
    (Fin n → K) ≃ₗ[K] ((f : Fin 6 → ZMod 3) → wtSpace (w := w) R f) where
  toFun v f := ⟨wtProj (w := w) R f v, wtProj_mulVec_mem hw3 hR f v⟩
  invFun u := ∑ f, (u f : Fin n → K)
  map_add' v v' := by
    funext f
    apply Subtype.ext
    simp only [Pi.add_apply, Submodule.coe_add, wtProj, mulVec_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' c v := by
    funext f
    apply Subtype.ext
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, wtProj, mulVec_smul,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_comm _ _ _
  left_inv v := sum_wtProj hw3 hw1 hR0 v
  right_inv u := by
    funext g
    apply Subtype.ext
    change wtProj (w := w) R g (∑ f, (u f : Fin n → K)) = u g
    have hlin : ∀ (s : Finset (Fin 6 → ZMod 3)),
        wtProj (w := w) R g (∑ f ∈ s, (u f : Fin n → K)) = ∑ f ∈ s, wtProj (w := w) R g (u f) := by
      intro s
      unfold wtProj
      simp only [mulVec_sum, Finset.smul_sum]
      exact Finset.sum_comm
    rw [hlin, Finset.sum_eq_single g]
    · simp only [wtProj_of_mem hw3 hw1 (u g).2, ↓reduceIte]
    · intro f _ hf
      simp only [wtProj_of_mem hw3 hw1 (u f).2, Ne.symm hf, ↓reduceIte]
    · intro h
      exact absurd (Finset.mem_univ g) h

include hw3 hw1 hR hR0 in
theorem finrank_eq_sum_wtSpace [CharP K 2] :
    n = ∑ f, Module.finrank K (wtSpace (w := w) R f) := by
  have := (wtEquiv hw3 hw1 hR hR0).finrank_eq
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at this
  exact this

end CFSG.Sporadic.Co1Schreier.WeightProj
