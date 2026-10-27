module

public import CFSG.Monster.Code.Defs
public import CFSG.Monster.Code.Bits
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

public section

namespace CFSG.Monster.Code

open F4

@[expose] def Bmask (i : ℕ) : ℕ :=
  [0x11111e, 0x1111e1, 0x111e11, 0x11e111, 0x1e1111, 0xe11111, 0xa6c00c, 0x6ca00a, 0x6ac0c0,
    0xc6a0a0, 0xcccc00, 0xaaaa00].getD i 0

theorem B_eq_bvec : ∀ i : Fin 12, B i = bvec 24 (Bmask i) := by decide

theorem B_mem_C : ∀ i, B i ∈ C := by decide

theorem g_mem_C : ∀ j, g j ∈ C := by decide

theorem Ω_eq_sum_g : Ω = ∑ j, g j := by decide

theorem Ω_mem_C : Ω ∈ C := by decide

@[expose] def ev (r : Fin 4) (j : Fin 6) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (coord r j)

@[expose] def ψ : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  LinearMap.pi ![ev 1 0 + ev 2 0 + ev 3 0, ev 1 1 + ev 2 1 + ev 3 1, ev 1 2 + ev 2 2 + ev 3 2,
    ev 1 3 + ev 2 3 + ev 3 3, ev 1 4 + ev 2 4 + ev 3 4, ev 1 5 + ev 2 5 + ev 3 5,
    ev 1 0 + ev 3 0, ev 2 0 + ev 3 0, ev 1 1 + ev 3 1, ev 2 1 + ev 3 1, ev 1 2 + ev 3 2,
    ev 2 2 + ev 3 2]

theorem ψ_B : ∀ i, ψ (B i) = Pi.single i 1 := by decide

theorem ψ_grey (x : Fin 24 → ZMod 2) (j : Fin 6) :
    ψ x (Fin.castAdd 6 j) = x (coord 1 j) + x (coord 2 j) + x (coord 3 j) := by
  fin_cases j <;> rfl

theorem ψ_six (x : Fin 24 → ZMod 2) : ψ x 6 = x (coord 1 0) + x (coord 3 0) := rfl
theorem ψ_seven (x : Fin 24 → ZMod 2) : ψ x 7 = x (coord 2 0) + x (coord 3 0) := rfl
theorem ψ_eight (x : Fin 24 → ZMod 2) : ψ x 8 = x (coord 1 1) + x (coord 3 1) := rfl
theorem ψ_nine (x : Fin 24 → ZMod 2) : ψ x 9 = x (coord 2 1) + x (coord 3 1) := rfl
theorem ψ_ten (x : Fin 24 → ZMod 2) : ψ x 10 = x (coord 1 2) + x (coord 3 2) := rfl
theorem ψ_eleven (x : Fin 24 → ZMod 2) : ψ x 11 = x (coord 2 2) + x (coord 3 2) := rfl

private theorem hex_formula : ∀ a b c : ZMod 2,
    algebraMap (ZMod 2) F4 a + α * algebraMap (ZMod 2) F4 b + ᾱ * algebraMap (ZMod 2) F4 c =
      ⟨a + c, b + c⟩ := by
  decide

theorem hexProj_apply (x : Fin 24 → ZMod 2) (j : Fin 6) :
    hexProj x j = ⟨x (coord 1 j) + x (coord 3 j), x (coord 2 j) + x (coord 3 j)⟩ :=
  hex_formula _ _ _

private theorem col_zero : ∀ a b c : ZMod 2,
    a + c = 0 → b + c = 0 → a + b + c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

private theorem six_smul (t : ZMod 2) : (6 : ℕ) • t = 0 := by
  rw [nsmul_eq_mul]; revert t; decide

theorem eq_zero_of_mem_C_of_ψ_eq_zero {x : Fin 24 → ZMod 2} (hx : x ∈ C) (hψ : ψ x = 0) :
    x = 0 := by
  obtain ⟨hH, hcol⟩ := hx
  have e : ∀ k, ψ x k = 0 := fun k => congrFun hψ k
  have h0 : hexProj x 0 = 0 := by
    rw [hexProj_apply, ← ψ_six, ← ψ_seven, e, e]; rfl
  have h1 : hexProj x 1 = 0 := by
    rw [hexProj_apply, ← ψ_eight, ← ψ_nine, e, e]; rfl
  have h2 : hexProj x 2 = 0 := by
    rw [hexProj_apply, ← ψ_ten, ← ψ_eleven, e, e]; rfl
  have hz : hexProj x = 0 := by
    rw [mem_H₆_iff, h0, h1, h2] at hH
    simpa using hH
  have hlow : ∀ j, x (coord 1 j) = 0 ∧ x (coord 2 j) = 0 ∧ x (coord 3 j) = 0 := by
    intro j
    have h := congrFun hz j
    rw [hexProj_apply] at h
    exact col_zero _ _ _ (congrArg F4.re h) (congrArg F4.im h) (by rw [← ψ_grey]; exact e _)
  have htop : ∀ j, x (coord 0 j) = topParity x := by
    intro j
    have := hcol j
    rwa [Fin.sum_univ_four, (hlow j).1, (hlow j).2.1, (hlow j).2.2, add_zero, add_zero,
      add_zero] at this
  have ht : topParity x = 0 := by
    have : topParity x = ∑ _j : Fin 6, topParity x :=
      Finset.sum_congr rfl fun j _ => htop j
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, six_smul]
  have hall : ∀ r j, x (coord r j) = 0 := by
    intro r j
    fin_cases r
    · exact (htop j).trans ht
    · exact (hlow j).1
    · exact (hlow j).2.1
    · exact (hlow j).2.2
  funext i
  rw [← coord_row_col i]
  exact hall _ _

theorem ψ_comb (μ : Fin 12 → ZMod 2) : ψ (∑ i, μ i • B i) = μ := by
  simp only [map_sum, map_smul, ψ_B]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem comb_injective : Function.Injective fun μ : Fin 12 → ZMod 2 => ∑ i, μ i • B i :=
  Function.LeftInverse.injective ψ_comb

theorem linearIndependent_B : LinearIndependent (ZMod 2) B := by
  refine LinearIndependent.of_comp ψ ?_
  have : ψ ∘ B = ⇑(Pi.basisFun (ZMod 2) (Fin 12)) := by
    funext i; simp [ψ_B, Pi.basisFun_apply]
  rw [this]
  exact (Pi.basisFun (ZMod 2) (Fin 12)).linearIndependent

theorem eq_comb_of_mem_C {x : Fin 24 → ZMod 2} (hx : x ∈ C) : x = ∑ i, ψ x i • B i := by
  have hy : x - ∑ i, ψ x i • B i ∈ C :=
    C.sub_mem hx (C.sum_mem fun i _ => C.smul_mem _ (B_mem_C i))
  have hψ : ψ (x - ∑ i, ψ x i • B i) = 0 := by rw [map_sub, ψ_comb, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_mem_C_of_ψ_eq_zero hy hψ)

theorem span_B : Submodule.span (ZMod 2) (Set.range B) = C := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 B_mem_C)) fun x hx => ?_
  rw [eq_comb_of_mem_C hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_C_iff_exists_comb (x : Fin 24 → ZMod 2) :
    x ∈ C ↔ ∃ μ : Fin 12 → ZMod 2, ∑ i, μ i • B i = x := by
  rw [← span_B, Submodule.mem_span_range_iff_exists_fun]

noncomputable def basisC : Module.Basis (Fin 12) (ZMod 2) C :=
  (Module.Basis.span linearIndependent_B).map (LinearEquiv.ofEq _ _ span_B)

@[simp] theorem basisC_apply (i : Fin 12) : (basisC i : Fin 24 → ZMod 2) = B i := by
  simp [basisC, Module.Basis.span_apply]

theorem finrank_C : Module.finrank (ZMod 2) C = 12 := by
  rw [Module.finrank_eq_card_basis basisC, Fintype.card_fin]

theorem G_le_C : G ≤ C := Submodule.span_le.2 (Set.range_subset_iff.2 g_mem_C)

private theorem lCol_sum : ∀ z : F4, ∑ r, lCol z r = 0 := by decide

private theorem lCol_row_zero : ∀ z : F4, lCol z 0 = 0 := by decide

private theorem lCol_lower : ∀ z : F4, lCol z 1 + lCol z 2 + lCol z 3 = 0 := by decide

theorem l_mem_C {y : Fin 6 → F4} (hy : y ∈ H₆) : l y ∈ C := by
  refine ⟨by rw [hexProj_l]; exact hy, fun j => ?_⟩
  simp only [l_apply_coord, lCol_sum, topParity, lCol_row_zero, Finset.sum_const_zero]

theorem H_le_C : H ≤ C := by
  rintro _ ⟨y, hy, rfl⟩
  exact l_mem_C hy

theorem l_row_zero (y : Fin 6 → F4) (j : Fin 6) : l y (coord 0 j) = 0 := by
  rw [l_apply_coord, lCol_row_zero]

theorem ψ_l_grey (y : Fin 6 → F4) (j : Fin 6) : ψ (l y) (Fin.castAdd 6 j) = 0 := by
  rw [ψ_grey, l_apply_coord, l_apply_coord, l_apply_coord, lCol_lower]

theorem ψ_g_coloured : ∀ j k : Fin 6, ψ (g j) (Fin.natAdd 6 k) = 0 := by decide

theorem G_sup_H : G ⊔ H = C := by
  refine le_antisymm (sup_le G_le_C H_le_C) ?_
  rw [← span_B, Submodule.span_le, Set.range_subset_iff]
  have hG : ∀ j, g j ∈ G ⊔ H := fun j =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)
  have hH : ∀ y ∈ H₆, l y ∈ G ⊔ H := fun y hy => Submodule.mem_sup_right ⟨y, hy, rfl⟩
  intro i
  fin_cases i
  · exact hG 0
  · exact hG 1
  · exact hG 2
  · exact hG 3
  · exact hG 4
  · exact hG 5
  · exact hH _ v₁_mem
  · exact hH _ (H₆.smul_mem α v₁_mem)
  · exact hH _ v₂_mem
  · exact hH _ (H₆.smul_mem α v₂_mem)
  · exact hH _ v₃_mem
  · exact hH _ (H₆.smul_mem α v₃_mem)

theorem disjoint_G_H : Disjoint G H := by
  rw [Submodule.disjoint_def]
  rintro x hxG ⟨y, -, rfl⟩
  have hG : ∀ k : Fin 6, ψ (l y) (Fin.natAdd 6 k) = 0 := by
    intro k
    have : G ≤ LinearMap.ker (LinearMap.proj (Fin.natAdd 6 k) ∘ₗ ψ) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 fun j => ψ_g_coloured j k)
    exact this hxG
  refine eq_zero_of_mem_C_of_ψ_eq_zero (G_le_C hxG) (funext fun k => ?_)
  fin_cases k
  exacts [ψ_l_grey y 0, ψ_l_grey y 1, ψ_l_grey y 2, ψ_l_grey y 3, ψ_l_grey y 4, ψ_l_grey y 5,
    hG 0, hG 1, hG 2, hG 3, hG 4, hG 5]

end CFSG.Monster.Code
