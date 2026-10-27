module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

open Module

theorem no_invariant_plane {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hdim : finrank F V = 3)
    (H : Submodule F V) (hH : finrank F H = 2) (a b s : V ≃ₗ[F] V)
    (ha2 : ∀ x, a (a x) = x) (hb2 : ∀ x, b (b x) = x) (hab : ∀ x, a (b x) = b (a x))
    (ha1 : ∃ w, a w ≠ w) (hsa : ∀ x, s (a x) = b (s x)) (hsb : ∀ x, s (b x) = a (b (s x)))
    (hHa : ∀ x ∈ H, a x ∈ H) (hHb : ∀ x ∈ H, b x ∈ H) (hHs : ∀ x ∈ H, s x ∈ H) : False := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have h6 : (6 : F) ≠ 0 := by
    have : (6 : F) = 2 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h3
  have hlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, finrank_top, hdim] at hH
    omega
  obtain ⟨f, hf0, hHf⟩ := H.exists_le_ker_of_lt_top hlt
  have hsurj : Function.Surjective f := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra hcon
      exact hf0 (LinearMap.ext fun x => not_not.1 fun h => hcon ⟨x, h⟩)
    intro c
    refine ⟨(c / f x) • x, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  have hker : LinearMap.ker f = H := by
    symm
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, hdim] at h1
    exact Submodule.eq_of_le_of_finrank_eq hHf (by omega)
  obtain ⟨v₀, hv₀⟩ := hsurj 1
  have key : ∀ g : V ≃ₗ[F] V, (∀ x ∈ H, g x ∈ H) → ∀ x, f (g x) = f x * f (g v₀) := by
    intro g hg x
    have h1 : x - f x • v₀ ∈ H := by
      rw [← hker, LinearMap.mem_ker, map_sub, map_smul, hv₀, smul_eq_mul, mul_one, sub_self]
    have h2' := hg _ h1
    rw [map_sub, map_smul, ← hker, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul] at h2'
    exact sub_eq_zero.1 h2'
  have hKa := key a hHa
  have hKb := key b hHb
  have hKs := key s hHs
  have hca2 : f (a v₀) * f (a v₀) = 1 := by
    have := hKa (a v₀)
    rw [ha2, hv₀] at this
    exact this.symm
  have hcb2 : f (b v₀) * f (b v₀) = 1 := by
    have := hKb (b v₀)
    rw [hb2, hv₀] at this
    exact this.symm
  have hcs0 : f (s v₀) ≠ 0 := by
    intro h0
    have := hKs (s.symm v₀)
    rw [LinearEquiv.apply_symm_apply, hv₀, h0, mul_zero] at this
    exact one_ne_zero this
  have hR1 : f (a v₀) * f (s v₀) = f (s v₀) * f (b v₀) := by
    have h1 := hKs (a v₀)
    have h2' := hKb (s v₀)
    rw [hsa] at h1
    exact h1.symm.trans h2'
  have hR2 : f (b v₀) * f (s v₀) = f (s v₀) * f (b v₀) * f (a v₀) := by
    have h1 := hKs (b v₀)
    rw [hsb] at h1
    have h2' := hKa (b (s v₀))
    have h3' := hKb (s v₀)
    rw [h3'] at h2'
    exact h1.symm.trans h2'
  have hab' : f (a v₀) = f (b v₀) := by
    apply mul_left_cancel₀ hcs0
    rw [mul_comm, hR1]
  have hcb0 : f (b v₀) ≠ 0 := left_ne_zero_of_mul_eq_one hcb2
  have hca1 : f (a v₀) = 1 := by
    have hne : f (s v₀) * f (b v₀) ≠ 0 := mul_ne_zero hcs0 hcb0
    apply mul_left_cancel₀ hne
    rw [mul_one]
    rw [mul_comm (f (b v₀)) (f (s v₀))] at hR2
    exact hR2.symm
  have hcb1 : f (b v₀) = 1 := hab' ▸ hca1
  have hfa : ∀ x, f (a x) = f x := fun x => by rw [hKa x, hca1, mul_one]
  have hfb : ∀ x, f (b x) = f x := fun x => by rw [hKb x, hcb1, mul_one]
  obtain ⟨v, hfv, hav, hbv⟩ : ∃ v : V, f v = 1 ∧ a v = v ∧ b v = v := by
    refine ⟨(4 : F)⁻¹ • (v₀ + a v₀ + b v₀ + a (b v₀)), ?_, ?_, ?_⟩
    · simp only [map_smul, map_add, hfa, hfb, hv₀, smul_eq_mul]
      rw [inv_mul_eq_iff_eq_mul₀ h4]
      norm_num
    · simp only [map_smul, map_add, ha2]
      congr 1
      abel
    · have e1 : b (a v₀) = a (b v₀) := (hab v₀).symm
      have e2 : b (a (b v₀)) = a v₀ := by rw [← hab, hb2]
      simp only [map_smul, map_add, hb2, e1, e2]
      congr 1
      abel
  have hv0 : v ≠ 0 := fun h => by
    rw [h, map_zero] at hfv
    exact zero_ne_one hfv
  obtain ⟨w, hw⟩ := ha1
  have hw₁0 : w - a w ≠ 0 := fun h => hw (sub_eq_zero.1 h).symm
  have haw₁ : a (w - a w) = -(w - a w) := by
    rw [map_sub, ha2]
    abel
  have hbaw₁ : a (b (w - a w)) = -(b (w - a w)) := by
    rw [hab, haw₁, map_neg]
  obtain ⟨u, ε, hε, hu0, hau, hbu⟩ :
      ∃ (u : V) (ε : F), (ε = 1 ∨ ε = -1) ∧ u ≠ 0 ∧ a u = -u ∧ b u = ε • u := by
    by_cases hp : (w - a w) + b (w - a w) = 0
    · refine ⟨(w - a w) - b (w - a w), -1, Or.inr rfl, ?_, ?_, ?_⟩
      · intro h0
        have h2w : (2 : F) • (w - a w) =
            ((w - a w) + b (w - a w)) + ((w - a w) - b (w - a w)) := by module
        rw [hp, h0, add_zero] at h2w
        exact hw₁0 ((smul_eq_zero.1 h2w).resolve_left h2)
      · rw [map_sub, haw₁, hbaw₁]
        abel
      · rw [map_sub, hb2]
        module
    · refine ⟨(w - a w) + b (w - a w), 1, Or.inl rfl, hp, ?_, ?_⟩
      · rw [map_add, haw₁, hbaw₁]
        abel
      · rw [map_add, hb2]
        module
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hbt1 : b (s u) = -(s u) := by rw [← hsa, hau, map_neg]
  have hat1 : a (s u) = -(ε • s u) := by
    have h := hsb u
    rw [hbu, map_smul, hbt1, map_neg] at h
    rw [h, neg_neg]
  have hbt2 : b (s (s u)) = -(ε • s (s u)) := by
    rw [← hsa, hat1, map_neg, map_smul]
  have hat2 : a (s (s u)) = ε • s (s u) := by
    have h := hsb (s u)
    rw [hbt1, map_neg, hbt2, map_neg, map_smul, neg_inj] at h
    calc a (s (s u)) = (ε * ε) • a (s (s u)) := by rw [hεε, one_smul]
      _ = ε • (ε • a (s (s u))) := by rw [smul_smul]
      _ = ε • s (s u) := by rw [← h]
  have hsu0 : s u ≠ 0 := fun h => hu0 (s.injective (by rw [h, map_zero]))
  have hssu0 : s (s u) ≠ 0 := fun h => hsu0 (s.injective (by rw [h, map_zero]))
  let d : Module.End F V := (a : V →ₗ[F] V) + (2 : F) • (b : V →ₗ[F] V)
  have hd : ∀ x, d x = a x + (2 : F) • b x := fun x => rfl
  have eig : ∀ (μ : F) (x : V), x ≠ 0 → d x = μ • x → d.HasEigenvector μ x :=
    fun μ x hx h => ⟨Module.End.mem_eigenspace_iff.2 h, hx⟩
  have e0 : d.HasEigenvector (3 : F) v := eig _ v hv0 (by rw [hd, hav, hbv]; module)
  have e1 : d.HasEigenvector (-1 + 2 * ε) u := eig _ u hu0 (by rw [hd, hau, hbu]; module)
  have e2 : d.HasEigenvector (-ε - 2) (s u) := eig _ _ hsu0 (by rw [hd, hat1, hbt1]; module)
  have e3 : d.HasEigenvector (-ε) (s (s u)) := eig _ _ hssu0 (by rw [hd, hat2, hbt2]; module)
  have hli : LinearIndependent F ![v, u, s u, s (s u)] := by
    refine d.eigenvectors_linearIndependent' ![(3 : F), -1 + 2 * ε, -ε - 2, -ε] ?_ _ ?_
    · intro i j hij
      rcases hε with rfl | rfl <;>
      · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
        first
          | exact h2 (by linear_combination hij)
          | exact h2 (by linear_combination -hij)
          | exact h4 (by linear_combination hij)
          | exact h4 (by linear_combination -hij)
          | exact h6 (by linear_combination hij)
          | exact h6 (by linear_combination -hij)
    · intro i
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
      · exact e3
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, hdim] at hcard
  omega

end Sec1511

end CFSG.RankThree.PartOne
