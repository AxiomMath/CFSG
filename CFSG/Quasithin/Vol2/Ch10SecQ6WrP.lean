module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrGam

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

@[expose] def pairAct (g : SymFiveWrTwo) (x : Fin 5 × Fin 5) : Fin 5 × Fin 5 :=
  if g.right = 1 then (g.left 1 x.1, g.left zs x.2) else (g.left 1 x.2, g.left zs x.1)

theorem zs_ne_one : zs ≠ 1 := by decide

theorem pairAct_base {g : SymFiveWrTwo} (hg : g.right = 1) (x : Fin 5 × Fin 5) :
    pairAct g x = (g.left 1 x.1, g.left zs x.2) := by
  simp [pairAct, hg]

theorem pairAct_swap {g : SymFiveWrTwo} (hg : g.right = zs) (x : Fin 5 × Fin 5) :
    pairAct g x = (g.left 1 x.2, g.left zs x.1) := by
  simp [pairAct, hg]

theorem pairAct_one (x : Fin 5 × Fin 5) : pairAct 1 x = x := pairAct_base rfl x

theorem left_mul_apply (g h : SymFiveWrTwo) (q : Multiplicative (ZMod 2)) :
    (g * h).left q = g.left q * h.left (g.right⁻¹ * q) := rfl

theorem zs_inv_mul_one : zs⁻¹ * 1 = zs := by decide

theorem zs_inv_mul_zs : zs⁻¹ * zs = 1 := by decide

theorem one_inv_mul (q : Multiplicative (ZMod 2)) : (1 : Multiplicative (ZMod 2))⁻¹ * q = q := by
  revert q
  decide

theorem zs_mul_zs : zs * zs = 1 := by decide

theorem pairAct_mul (g h : SymFiveWrTwo) (x : Fin 5 × Fin 5) :
    pairAct (g * h) x = pairAct g (pairAct h x) := by
  have hr : (g * h).right = g.right * h.right := rfl
  rcases zmod2_cases g.right with hg | hg <;> rcases zmod2_cases h.right with hh | hh
  · rw [pairAct_base (by rw [hr, hg, hh, one_mul]), pairAct_base hh, pairAct_base hg,
      left_mul_apply, left_mul_apply, hg, one_inv_mul, one_inv_mul]
    rfl
  · rw [pairAct_swap (by rw [hr, hg, hh, one_mul]), pairAct_swap hh, pairAct_base hg,
      left_mul_apply, left_mul_apply, hg, one_inv_mul, one_inv_mul]
    rfl
  · rw [pairAct_swap (by rw [hr, hg, hh, mul_one]), pairAct_base hh, pairAct_swap hg,
      left_mul_apply, left_mul_apply, hg, zs_inv_mul_one, zs_inv_mul_zs]
    rfl
  · rw [pairAct_base (by rw [hr, hg, hh, zs_mul_zs]), pairAct_swap hh, pairAct_swap hg,
      left_mul_apply, left_mul_apply, hg, zs_inv_mul_one, zs_inv_mul_zs]
    rfl

theorem pairAct_inv_pairAct (g : SymFiveWrTwo) (x : Fin 5 × Fin 5) :
    pairAct g⁻¹ (pairAct g x) = x := by
  rw [← pairAct_mul, inv_mul_cancel, pairAct_one]

theorem pairAct_pairAct_inv (g : SymFiveWrTwo) (x : Fin 5 × Fin 5) :
    pairAct g (pairAct g⁻¹ x) = x := by
  rw [← pairAct_mul, mul_inv_cancel, pairAct_one]

@[expose] def pairPerm (g : SymFiveWrTwo) : Perm (Fin 5 × Fin 5) where
  toFun := pairAct g
  invFun := pairAct g⁻¹
  left_inv := pairAct_inv_pairAct g
  right_inv := pairAct_pairAct_inv g

theorem mem_Y0_of_pairAct {h : SymFiveWrTwo} (hh : pairAct h (4, 4) = (4, 4)) : h ∈ Y0 := by
  have h4 : h.left 1 4 = 4 ∧ h.left zs 4 = 4 := by
    rcases zmod2_cases h.right with hr | hr
    · rw [pairAct_base hr] at hh
      exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
    · rw [pairAct_swap hr] at hh
      exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  intro q
  rcases zmod2_cases q with rfl | rfl
  · exact h4.1
  · exact h4.2

@[expose] def rep (x : Fin 5 × Fin 5) : SymFiveWrTwo :=
  wrBaseHom fun q => if q = 1 then swap 4 x.1 else swap 4 x.2

theorem pairAct_rep (x : Fin 5 × Fin 5) : pairAct (rep x) (4, 4) = x := by
  unfold rep
  rw [pairAct_base (wrBaseHom_right _)]
  simp [wrBaseHom_left]

theorem rep_inv_mul_mem_Y0 (g : SymFiveWrTwo) (x : Fin 5 × Fin 5) :
    (rep (pairAct g x))⁻¹ * g * rep x ∈ Y0 := by
  have key : ∀ y, pairAct (rep y)⁻¹ y = (4, 4) := fun y => by
    conv_lhs => arg 2; rw [← pairAct_rep y]
    exact pairAct_inv_pairAct _ _
  apply mem_Y0_of_pairAct
  rw [pairAct_mul, pairAct_mul, pairAct_rep, key]

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
