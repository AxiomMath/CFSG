module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

variable {K : Type} [Field K] [Fintype K] [CharP K 2]

theorem frobPow_linearIndependent {f : ℕ} (hf : Fintype.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    LinearIndependent K (fun r : Fin f => (fun c : K => c ^ (2 ^ (r : ℕ)))) := by
  have hφ : Function.Injective (fun r : Fin f => (powMonoidHom (2 ^ (r : ℕ)) : K →* K)) := by
    intro r r' h
    apply Fin.ext
    by_contra hne
    have hpow : (2 : ℕ) ^ (r : ℕ) ≠ 2 ^ (r' : ℕ) := fun h2 =>
      hne (Nat.pow_right_injective le_rfl h2)
    have hfun : ∀ c : K, c ^ (2 ^ (r : ℕ)) = c ^ (2 ^ (r' : ℕ)) := fun c => by
      have hc := DFunLike.congr_fun h c
      simpa only [powMonoidHom_apply] using hc
    have hlt : ∀ s : Fin f, 2 ^ (s : ℕ) < Fintype.card K := fun s => by
      rw [hf]
      exact Nat.pow_lt_pow_right (by norm_num) s.2
    have hp0 : (Polynomial.X ^ (2 ^ (r : ℕ)) - Polynomial.X ^ (2 ^ (r' : ℕ)) : Polynomial K) ≠ 0 := by
      intro h0
      have hc := congrArg (fun q : Polynomial K => q.coeff (2 ^ (r : ℕ))) h0
      simp [Polynomial.coeff_X_pow, hpow, hne] at hc
    have hdeg : (Polynomial.X ^ (2 ^ (r : ℕ)) - Polynomial.X ^ (2 ^ (r' : ℕ)) : Polynomial K).natDegree
        < Fintype.card K := by
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt ?_ ?_)
      · rw [Polynomial.natDegree_X_pow]
        exact hlt r
      · rw [Polynomial.natDegree_X_pow]
        exact hlt r'
    apply hp0
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := id) Function.injective_id ?_ hdeg
    intro c
    simp [hfun c]
  exact (linearIndependent_monoidHom K K).comp _ hφ

theorem twist_eq_zero {N : Type} [AddCommGroup N] [Module K N] {f : ℕ}
    (hf : Fintype.card K = 2 ^ f) (hf2 : 2 ≤ f) (g : Fin f → Module.Dual K N)
    (h : ∀ n, ∑ r : Fin f, (g r n) ^ (2 ^ (r : ℕ)) = 0) : ∀ r, g r = 0 := by
  have hli := frobPow_linearIndependent hf hf2
  rw [Fintype.linearIndependent_iff] at hli
  intro r
  apply LinearMap.ext
  intro n
  have key : ∀ c : K, ∑ s : Fin f, (g s n) ^ (2 ^ (s : ℕ)) * c ^ (2 ^ (s : ℕ)) = 0 := by
    intro c
    have h1 := h (c • n)
    simp only [map_smul, smul_eq_mul, mul_pow] at h1
    exact (Finset.sum_congr rfl fun s _ => mul_comm _ _).trans h1
  have hcoef := hli (fun s => (g s n) ^ (2 ^ (s : ℕ))) (by
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact key c)
  have hr : (g r n) ^ (2 ^ (r : ℕ)) = 0 := hcoef r
  rw [LinearMap.zero_apply]
  exact (pow_eq_zero_iff (by positivity)).mp hr

theorem card_twist_le {N : Type} [AddCommGroup N] [Module K N] [Module.Finite K N] {f : ℕ}
    (hf : Fintype.card K = 2 ^ f) (hf2 : 2 ≤ f) (B : Finset (Fin f)) (Y : AddSubgroup (N → K))
    (hY : ∀ r ∈ B, ∀ g : Module.Dual K N, (fun n => (g n) ^ (2 ^ (r : ℕ))) ∈ Y) :
    Nat.card (Module.Dual K N) ^ B.card ≤ Nat.card Y := by
  haveI : Finite N := Module.finite_of_finite K
  have hmemG : ∀ G : B → Module.Dual K N,
      (fun n => ∑ r : B, (G r n) ^ (2 ^ (r : ℕ))) ∈ Y := by
    intro G
    have hs : (∑ r : B, (fun n => (G r n) ^ (2 ^ (r : ℕ)))) ∈ Y :=
      AddSubgroup.sum_mem Y (fun r _ => hY r.1 r.2 (G r))
    have heq : (∑ r : B, (fun n => (G r n) ^ (2 ^ (r : ℕ))))
        = fun n => ∑ r : B, (G r n) ^ (2 ^ (r : ℕ)) := by
      funext n
      simp [Finset.sum_apply]
    rw [← heq]
    exact hs
  let Φ : (B → Module.Dual K N) → Y := fun G =>
    ⟨fun n => ∑ r : B, (G r n) ^ (2 ^ (r : ℕ)), hmemG G⟩
  have hinj : Function.Injective Φ := by
    intro G₁ G₂ hG
    have hsum : ∀ n, ∑ r : B, (G₁ r n) ^ (2 ^ (r : ℕ)) = ∑ r : B, (G₂ r n) ^ (2 ^ (r : ℕ)) :=
      fun n => congrFun (congrArg Subtype.val hG) n
    let D : Fin f → Module.Dual K N := fun s => if h : s ∈ B then G₁ ⟨s, h⟩ - G₂ ⟨s, h⟩ else 0
    have hD : ∀ n, ∑ s : Fin f, (D s n) ^ (2 ^ (s : ℕ)) = 0 := by
      intro n
      have hzero : ∀ s ∈ (Finset.univ : Finset (Fin f)), s ∉ B → (D s n) ^ (2 ^ (s : ℕ)) = 0 := by
        intro s _ hs
        simp [D, hs]
      have hpt : ∀ r : B, (D r n) ^ (2 ^ (r : ℕ))
          = (G₁ r n) ^ (2 ^ (r : ℕ)) - (G₂ r n) ^ (2 ^ (r : ℕ)) := by
        intro r
        simp only [D, dif_pos r.2, LinearMap.sub_apply]
        exact sub_pow_char_pow _ _ _
      rw [← Finset.sum_subset (Finset.subset_univ B) hzero, ← Finset.sum_coe_sort B]
      simp only [hpt, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (hsum n)
    funext r
    have hr := twist_eq_zero hf hf2 D hD r.1
    simp only [D, dif_pos r.2] at hr
    exact sub_eq_zero.mp hr
  have hcard := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_fun, Nat.card_eq_finsetCard] at hcard
  exact hcard

theorem card_dual {N : Type} [AddCommGroup N] [Module K N] [Module.Finite K N] :
    Nat.card (Module.Dual K N) = Fintype.card K ^ finrank K N := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K N), Subspace.dual_finrank_eq,
    Nat.card_eq_fintype_card]

end CFSG.RankThree.GF2n.Smith81.S81V
