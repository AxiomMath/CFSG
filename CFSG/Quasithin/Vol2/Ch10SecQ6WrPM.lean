module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrP

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

abbrev PMod : Type := Fin 5 → Fin 5 → ZMod 2

@[expose] def gP (g : SymFiveWrTwo) (p : PMod) : PMod :=
  fun i j => p (pairAct g⁻¹ (i, j)).1 (pairAct g⁻¹ (i, j)).2

theorem gP_apply (g : SymFiveWrTwo) (p : PMod) (i j : Fin 5) :
    gP g p i j = p (pairAct g⁻¹ (i, j)).1 (pairAct g⁻¹ (i, j)).2 := rfl

theorem gP_one (p : PMod) : gP 1 p = p := by
  funext i j
  rw [gP_apply, inv_one, pairAct_one]

theorem gP_mul (g h : SymFiveWrTwo) (p : PMod) : gP (g * h) p = gP g (gP h p) := by
  funext i j
  rw [gP_apply, gP_apply, gP_apply, mul_inv_rev, pairAct_mul]

theorem gP_add (g : SymFiveWrTwo) (p p' : PMod) : gP g (p + p') = gP g p + gP g p' := rfl

theorem gP_zero (g : SymFiveWrTwo) : gP g 0 = 0 := rfl

theorem gP_const (g : SymFiveWrTwo) (t : ZMod 2) : gP g (fun _ _ => t) = fun _ _ => t := rfl

theorem inv_right_base {g : SymFiveWrTwo} (hg : g.right = 1) : g⁻¹.right = 1 := by
  rw [RegularWreathProduct.inv_right, hg]
  decide

theorem inv_left_base {g : SymFiveWrTwo} (hg : g.right = 1) (q : Multiplicative (ZMod 2)) :
    g⁻¹.left q = (g.left q)⁻¹ := by
  change (g.left (g.right * q))⁻¹ = _
  rw [hg, one_mul]

theorem inv_right_swap {g : SymFiveWrTwo} (hg : g.right = zs) : g⁻¹.right = zs := by
  rw [RegularWreathProduct.inv_right, hg]
  decide

theorem inv_left_swap_one {g : SymFiveWrTwo} (hg : g.right = zs) :
    g⁻¹.left 1 = (g.left zs)⁻¹ := by
  change (g.left (g.right * 1))⁻¹ = _
  rw [hg, mul_one]

theorem inv_left_swap_zs {g : SymFiveWrTwo} (hg : g.right = zs) :
    g⁻¹.left zs = (g.left 1)⁻¹ := by
  change (g.left (g.right * zs))⁻¹ = _
  rw [hg, zs_mul_zs]

theorem gP_base {g : SymFiveWrTwo} (hg : g.right = 1) (p : PMod) (i j : Fin 5) :
    gP g p i j = p ((g.left 1)⁻¹ i) ((g.left zs)⁻¹ j) := by
  rw [gP_apply, pairAct_base (inv_right_base hg), inv_left_base hg, inv_left_base hg]

theorem gP_swap {g : SymFiveWrTwo} (hg : g.right = zs) (p : PMod) (i j : Fin 5) :
    gP g p i j = p ((g.left zs)⁻¹ j) ((g.left 1)⁻¹ i) := by
  rw [gP_apply, pairAct_swap (inv_right_swap hg), inv_left_swap_one hg, inv_left_swap_zs hg]

@[expose] def tens (a b : Fin 5 → ZMod 2) : PMod := fun i j => a i * b j

@[expose] def sumv (a b : Fin 5 → ZMod 2) : PMod := fun i j => a i + b j

theorem gP_tens_base {g : SymFiveWrTwo} (hg : g.right = 1) (a b : Fin 5 → ZMod 2) :
    gP g (tens a b) = tens (pv (g.left 1) a) (pv (g.left zs) b) := by
  funext i j
  rw [gP_base hg]
  rfl

theorem gP_tens_swap {g : SymFiveWrTwo} (hg : g.right = zs) (a b : Fin 5 → ZMod 2) :
    gP g (tens a b) = tens (pv (g.left 1) b) (pv (g.left zs) a) := by
  funext i j
  rw [gP_swap hg]
  exact mul_comm _ _

theorem gP_sumv_base {g : SymFiveWrTwo} (hg : g.right = 1) (a b : Fin 5 → ZMod 2) :
    gP g (sumv a b) = sumv (pv (g.left 1) a) (pv (g.left zs) b) := by
  funext i j
  rw [gP_base hg]
  rfl

theorem gP_sumv_swap {g : SymFiveWrTwo} (hg : g.right = zs) (a b : Fin 5 → ZMod 2) :
    gP g (sumv a b) = sumv (pv (g.left 1) b) (pv (g.left zs) a) := by
  funext i j
  rw [gP_swap hg]
  exact add_comm _ _

theorem eq_zero_of_const {u : Fin 5 → ZMod 2} (hu : IsO u) (hc : ∀ i i', u i = u i') : u = 0 := by
  have h : ∑ i, u i = 5 * u 0 := by
    rw [Finset.sum_congr rfl fun i _ => hc i 0, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  unfold IsO at hu
  rw [h] at hu
  have h5 : (5 : ZMod 2) = 1 := by decide
  rw [h5, one_mul] at hu
  funext i
  rw [hc i 0, hu]
  rfl

theorem zmod_two_add_eq {x y z w : ZMod 2} (h : x + y = z + w) : x + z = y + w := by
  revert x y z w
  decide

theorem zmod_two_eq_of_add {x y : ZMod 2} (h : x + y = 0) : x = y := by
  revert x y
  decide

theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem sumv_inj {a b a' b' : Fin 5 → ZMod 2} (ha : IsO a) (ha' : IsO a')
    (h : sumv a b = sumv a' b') : a = a' ∧ b = b' := by
  have hrow : ∀ i j, a i + a' i = b j + b' j := fun i j =>
    zmod_two_add_eq (congrFun (congrFun h i) j)
  have hd : a + a' = 0 := eq_zero_of_const (isO_add ha ha') fun i i' => by
    simp only [Pi.add_apply]
    rw [hrow i 0, hrow i' 0]
  have haa : a = a' := funext fun i => zmod_two_eq_of_add (congrFun hd i)
  refine ⟨haa, funext fun j => zmod_two_eq_of_add ?_⟩
  rw [← hrow 0 j, haa]
  exact zmod_two_add_self _

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
