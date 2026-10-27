module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuWord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuWeylData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix

@[expose] def wE (k : Fin 48) : G6 := wordProd (canW k)

theorem canW_zero : canW 0 = [] := rfl

theorem wE_zero : wE 0 = 1 := rfl

theorem canW_cons : ∀ k : Fin 48, k ≠ 0 → canW k = headS k :: canW (tailIdx k) := by
  decide +kernel

theorem wE_eq_cons {k : Fin 48} (hk : k ≠ 0) : wE k = sE (headS k) * wE (tailIdx k) := by
  rw [wE, wE, canW_cons k hk, wordProd_cons]

theorem length_tailIdx {k : Fin 48} (hk : k ≠ 0) :
    (canW (tailIdx k)).length + 1 = (canW k).length := by
  rw [canW_cons k hk, List.length_cons]

theorem sE_mul_wE_bits : ∀ (s : Fin 3) (k : Fin 48),
    bmul (sB s) (bword (canW k)) = bword (canW (mulTab s k)) := by
  decide +kernel

theorem sE_mul_wE (s : Fin 3) (k : Fin 48) : sE s * wE k = wE (mulTab s k) := by
  apply gM_injective
  change sM s * gM (wordProd (canW k)) = gM (wordProd (canW (mulTab s k)))
  rw [wordProd_coe, wordProd_coe, sM_eq_toMat, ← toMat_bmul, sE_mul_wE_bits]

theorem wE_conj_bits : ∀ (k : Fin 48) (s : Fin 3),
    IsUpU (toMat (bmul (bmul (bword (canW k).reverse) (xB s)) (bword (canW k)))) ∨
      IsUpU (toMat (bmul (bmul (bword (canW k).reverse) (yB s)) (bword (canW k)))) := by
  decide +kernel

theorem conj_coe (l : List (Fin 3)) (g : G6) :
    gM (wordProd l.reverse * g * wordProd l) =
      gM (wordProd l.reverse) * gM g * gM (wordProd l) := rfl

theorem wE_conj (k : Fin 48) (s : Fin 3) :
    (wE k)⁻¹ * xE s * wE k ∈ Ugrp ∨ (wE k)⁻¹ * yE s * wE k ∈ Ugrp := by
  rw [wE, wordProd_inv, mem_Ugrp, mem_Ugrp, conj_coe, conj_coe, wordProd_coe, wordProd_coe]
  change IsUpU (_ * xM s * _) ∨ IsUpU (_ * yM s * _)
  rw [xM_eq_toMat, yM_eq_toMat, ← toMat_bmul, ← toMat_bmul, ← toMat_bmul, ← toMat_bmul]
  exact wE_conj_bits k s

theorem wE_tail_conj_bits : ∀ k : Fin 48, k ≠ 0 →
    IsUpU (toMat (bmul (bmul (bword (canW (tailIdx k)).reverse) (xB (headS k)))
      (bword (canW (tailIdx k))))) := by
  decide +kernel

theorem wE_tail_conj {k : Fin 48} (hk : k ≠ 0) :
    (wE (tailIdx k))⁻¹ * xE (headS k) * wE (tailIdx k) ∈ Ugrp := by
  rw [wE, wordProd_inv, mem_Ugrp, conj_coe, wordProd_coe, wordProd_coe]
  change IsUpU (_ * xM (headS k) * _)
  rw [xM_eq_toMat, ← toMat_bmul, ← toMat_bmul]
  exact wE_tail_conj_bits k hk

theorem canW_length_zero : ∀ j : Fin 48, (canW j).length = 0 → j = 0 := by decide +kernel

theorem canW_induction {P : Fin 48 → Prop} (h0 : P 0)
    (hstep : ∀ j : Fin 48, j ≠ 0 → P (tailIdx j) → P j) (j : Fin 48) : P j := by
  suffices ∀ n, ∀ j : Fin 48, (canW j).length = n → P j from this _ j rfl
  intro n
  induction n with
  | zero =>
    intro j hj
    rw [canW_length_zero j hj]
    exact h0
  | succ n ih =>
    intro j hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [canW_zero] at hj
      exact absurd hj (by simp)
    refine hstep j hj0 (ih _ ?_)
    have := length_tailIdx hj0
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
