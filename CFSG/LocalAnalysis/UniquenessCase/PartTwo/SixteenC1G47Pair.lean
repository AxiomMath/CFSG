module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Coord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Siegel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Two

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_pair {K U B N : Subgroup G} (hUK : U ≤ K) (hBK : B ≤ K)
    (hKUB : ∀ k ∈ K, ∃ u ∈ U, ∃ b ∈ B, k = u * b)
    (hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hUsq : ∀ x ∈ U, x * x = 1)
    (hBsq : ∀ x ∈ B, x * x = 1) (hN : N = U ⊓ B) (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hNcent : ∀ n ∈ N, ∀ k ∈ K, k * n = n * k)
    (hBZ : ∀ b ∈ B, (∀ u ∈ U, u * b = b * u) → b ∈ U)
    (hU : Nat.card ↥U = 32) (hB : Nat.card ↥B = 32) (hNc : Nat.card ↥N = 2) {w w' : G}
    (hwU : ∀ u ∈ U, w * u * w⁻¹ = u) (hwB : ∀ b ∈ B, ⁅w, b⁆ ∈ U)
    (hw'B : ∀ b ∈ B, w' * b * w'⁻¹ = b) (hw'U : ∀ u ∈ U, ⁅w', u⁆ ∈ B) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 6 ∧ ∀ x ∈ K, ⁅x, (w * w') ^ k⁆ ∈ N := by
  obtain ⟨κ, hκ⟩ := s16c1_G47_coord hUK hBK hKUB hUab hUsq hBsq hN hKcomm hNcent hBZ hU hB hNc
  obtain ⟨S, hS, hSact⟩ := s16c1_G47_siegel_left hκ hUK hBK hN hKUB hKcomm hBsq hwU hwB
  obtain ⟨T, hT, hTact⟩ := s16c1_G47_siegel_right hκ hUK hBK hN hKUB hKcomm hUsq hw'B hw'U
  obtain ⟨k, hk1, hk6, hkρ⟩ := s16c1_G47_two S T hS hT
  refine ⟨k, hk1, hk6, ?_⟩
  set ρ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) := g47Up S * g47Lo T with hρ
  have key : ∀ m : ℕ, ∀ x ∈ K, (w * w') ^ m * x * ((w * w') ^ m)⁻¹ ∈ K ∧
      κ ((w * w') ^ m * x * ((w * w') ^ m)⁻¹) = (ρ ^ m).mulVec (κ x) := by
    intro m
    induction m with
    | zero =>
      intro x hx
      simp [hx]
    | succ m ih =>
      intro x hx
      obtain ⟨hKm, hκm⟩ := ih x hx
      obtain ⟨hK1, hκ1⟩ := hTact _ hKm
      obtain ⟨hK2, hκ2⟩ := hSact _ hK1
      have hconj : (w * w') ^ (m + 1) * x * ((w * w') ^ (m + 1))⁻¹ =
          w * (w' * ((w * w') ^ m * x * ((w * w') ^ m)⁻¹) * w'⁻¹) * w⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [hconj]
      refine ⟨hK2, ?_⟩
      rw [hκ2, hκ1, hκm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pow_succ', hρ, mul_assoc]
  intro x hx
  obtain ⟨hKk, hκk⟩ := key k x hx
  rw [hkρ, Matrix.one_mulVec] at hκk
  have h1K : (1 : G) ∈ K := K.one_mem
  have hκ1 : κ 1 = 0 := (hκ.eq_zero_iff 1 h1K).2 N.one_mem
  have hκinv : κ x⁻¹ = - κ x := by
    have h := hκ.add x hx x⁻¹ (K.inv_mem hx)
    rw [mul_inv_cancel, hκ1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hmem : (w * w') ^ k * x * ((w * w') ^ k)⁻¹ * x⁻¹ ∈ N := by
    rw [← hκ.eq_zero_iff _ (K.mul_mem hKk (K.inv_mem hx)), hκ.add _ hKk _ (K.inv_mem hx), hκk,
      hκinv]
    exact add_neg_cancel _
  have hcomm : ⁅(w * w') ^ k, x⁆ ∈ N := by
    rw [commutatorElement_def]
    exact hmem
  have h2 : ⁅x, (w * w') ^ k⁆ = ⁅(w * w') ^ k, x⁆⁻¹ := (commutatorElement_inv _ _).symm
  rw [h2]
  exact N.inv_mem hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
