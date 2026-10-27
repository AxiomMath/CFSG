module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalf

private theorem fin_ne_of_val_ne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b :=
  fun hab => h (congrArg Fin.val hab)

private def piOdd (m : ℕ) (P : Fin (m + 1 + 1)) : Equiv.Perm (Fin (m + 1 + 1 + 1)) :=
  Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc *
    Equiv.swap (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ

private def piEven (m : ℕ) (P : Fin (m + 1 + 1)) : Equiv.Perm (Fin (m + 1 + 1 + 1)) :=
  (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc *
      Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ) *
    (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) *
      Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)))

private theorem conjTM_apply {N : ℕ} (c x : SpecialLinearGroup (Fin N) F2) :
    (MulAut.conj c).toMonoidHom x = c * x * c⁻¹ := by
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

private theorem piOdd_apply_last (m : ℕ) (hm : m % 2 = 1) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) :
    piOdd m P (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) = P.castSucc := by
  rw [piOdd, Equiv.Perm.mul_apply,
    show (Equiv.swap (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ)
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from
      Equiv.swap_apply_of_ne_of_ne
        (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
        (fin_ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk]; omega)),
    Equiv.swap_apply_left]

private theorem piOdd_apply_succ (m : ℕ) (hm : m % 2 = 1) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) :
    piOdd m P (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) = P.succ := by
  rw [piOdd, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    show (Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc) P.succ = P.succ from
      Equiv.swap_apply_of_ne_of_ne
        (fin_ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk]; omega))
        (fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))]

private theorem piOdd_apply_Pcast (m : ℕ) (P : Fin (m + 1 + 1)) :
    piOdd m P P.castSucc = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
  rw [piOdd, Equiv.Perm.mul_apply,
    show (Equiv.swap (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ) P.castSucc =
        P.castSucc from
      Equiv.swap_apply_of_ne_of_ne
        (fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk]; omega))
        (fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)),
    Equiv.swap_apply_right]

private theorem piOdd_apply_Psucc (m : ℕ) (P : Fin (m + 1 + 1)) :
    piOdd m P P.succ = (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
  rw [piOdd, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
    show (Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc)
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) from
      Equiv.swap_apply_of_ne_of_ne
        (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
        (fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk]; omega))]

private theorem piOdd_apply_fixed (m : ℕ) (P : Fin (m + 1 + 1))
    (x : Fin (m + 1 + 1 + 1))
    (hxc : x ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)))
    (hxb : x ≠ (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)))
    (hxPc : x ≠ P.castSucc) (hxPs : x ≠ P.succ) :
    piOdd m P x = x := by
  rw [piOdd, Equiv.Perm.mul_apply,
    show (Equiv.swap (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ) x = x from
      Equiv.swap_apply_of_ne_of_ne hxb hxPs,
    show (Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc) x = x from
      Equiv.swap_apply_of_ne_of_ne hxc hxPc]

private theorem piEven_sigma_last (m : ℕ) :
    (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) *
        Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
          (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)))
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
  rw [Equiv.Perm.mul_apply,
    show (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)))
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from
      Equiv.swap_apply_of_ne_of_ne
        (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
        (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega)),
    Equiv.swap_apply_right]

private theorem piEven_sigma_succ (m : ℕ) :
    (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) *
        Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
          (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)))
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]

private theorem piEven_sigma_a (m : ℕ) :
    (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) *
        Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
          (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)))
        (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    show (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)))
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) from
      Equiv.swap_apply_of_ne_of_ne
        (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
        (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))]

private theorem piEven_sigma_fixed (m : ℕ) (x : Fin (m + 1 + 1 + 1))
    (hxa : x ≠ (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)))
    (hxb : x ≠ (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)))
    (hxc : x ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1))) :
    (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) *
        Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
          (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1))) x = x := by
  rw [Equiv.Perm.mul_apply,
    show (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1))) x = x from
      Equiv.swap_apply_of_ne_of_ne hxa hxb,
    show (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1))) x = x from
      Equiv.swap_apply_of_ne_of_ne hxa hxc]

private theorem piEven_apply_c1 (m : ℕ) (hm : m % 2 = 0) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) :
    piEven m P (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) = P.castSucc := by
  have hsig := piEven_sigma_last m
  have htau : (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc *
        Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ)
        (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) = P.castSucc := by
    rw [Equiv.Perm.mul_apply,
      show (Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ)
          (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) =
        (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) from
        Equiv.swap_apply_of_ne_of_ne
          (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
          (fin_ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk]; omega)),
      Equiv.swap_apply_left]
  rw [piEven, Equiv.Perm.mul_apply, hsig, htau]

private theorem piEven_apply_b (m : ℕ) (hm : m % 2 = 0) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) :
    piEven m P (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) = P.succ := by
  have hsig := piEven_sigma_succ m
  have htau : (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc *
        Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ)
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) = P.succ := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      show (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc) P.succ =
          P.succ from
        Equiv.swap_apply_of_ne_of_ne
          (fin_ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk]; omega))
          (fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))]
  rw [piEven, Equiv.Perm.mul_apply, hsig, htau]

private theorem piEven_apply_a (m : ℕ) (hm : m % 2 = 0) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) :
    piEven m P (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
  have hsig := piEven_sigma_a m
  have htau : (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc *
        Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ)
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) =
      (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
    rw [Equiv.Perm.mul_apply,
      show (Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ)
          (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) =
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) from
        Equiv.swap_apply_of_ne_of_ne
          (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
          (fin_ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk]; omega)),
      show (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc)
          (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) =
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) from
        Equiv.swap_apply_of_ne_of_ne
          (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
          (fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk]; omega))]
  rw [piEven, Equiv.Perm.mul_apply, hsig, htau]

private theorem piEven_apply_Pcast (m : ℕ) (hm : m % 2 = 0) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0)
    (hPa : P.castSucc ≠ (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))) :
    piEven m P P.castSucc = (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
  have hPval : P.val ≠ m := fun h => hPa (Fin.ext h)
  have hPlt : P.val ≤ m - 2 := by have := P.isLt; omega
  have hb : P.castSucc ≠ (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) :=
    fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk]; omega)
  have hc : P.castSucc ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) :=
    fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_mk]; omega)
  have hsig := piEven_sigma_fixed m P.castSucc hPa hb hc
  have htau : (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc *
        Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ)
        P.castSucc = (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
    rw [Equiv.Perm.mul_apply,
      show (Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ) P.castSucc =
          P.castSucc from
        Equiv.swap_apply_of_ne_of_ne hc
          (fin_ne_of_val_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)),
      Equiv.swap_apply_right]
  rw [piEven, Equiv.Perm.mul_apply, hsig, htau]

private theorem piEven_apply_Psucc (m : ℕ) (hm : m % 2 = 0) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0)
    (hPa : P.castSucc ≠ (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1))) :
    piEven m P P.succ = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
  have hPval : P.val ≠ m := fun h => hPa (Fin.ext h)
  have hPlt : P.val ≤ m - 2 := by have := P.isLt; omega
  have ha : P.succ ≠ (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) :=
    fin_ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk]; omega)
  have hb : P.succ ≠ (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) :=
    fin_ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk]; omega)
  have hc : P.succ ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) :=
    fin_ne_of_val_ne (by simp only [Fin.val_succ, Fin.val_mk]; omega)
  have hsig := piEven_sigma_fixed m P.succ ha hb hc
  have htau : (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc *
        Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ)
        P.succ = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      show (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc)
          (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) =
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from
        Equiv.swap_apply_of_ne_of_ne
          (fin_ne_of_val_ne (by simp only [Fin.val_mk]; omega))
          (fin_ne_of_val_ne (by
            simp only [Fin.val_castSucc, Fin.val_mk]
            omega))]
  rw [piEven, Equiv.Perm.mul_apply, hsig, htau]

private theorem piEven_apply_fixed (m : ℕ) (P : Fin (m + 1 + 1))
    (x : Fin (m + 1 + 1 + 1))
    (hxa : x ≠ (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)))
    (hxb : x ≠ (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)))
    (hxc : x ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)))
    (hxPc : x ≠ P.castSucc) (hxPs : x ≠ P.succ) :
    piEven m P x = x := by
  have hsig := piEven_sigma_fixed m x hxa hxb hxc
  rw [piEven, Equiv.Perm.mul_apply, hsig, Equiv.Perm.mul_apply,
    show (Equiv.swap (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) P.succ) x = x from
      Equiv.swap_apply_of_ne_of_ne hxc hxPs,
    show (Equiv.swap (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) P.castSucc) x = x from
      Equiv.swap_apply_of_ne_of_ne hxa hxPc]

private theorem piOdd_conj_last (m : ℕ) (hm : m % 2 = 1) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) :
    slPerm gf2_two (piOdd m P) * omegaBlock (m + 1 + 1) (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) *
      (slPerm gf2_two (piOdd m P))⁻¹ = omegaBlock (m + 1 + 1) P := by
  apply slPerm_conj_omegaBlock (piOdd m P)
  · rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc =
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact piOdd_apply_last m hm P hP
  · rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ =
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact piOdd_apply_succ m hm P hP

private theorem piOdd_conj_P (m : ℕ) (P : Fin (m + 1 + 1)) :
    slPerm gf2_two (piOdd m P) * omegaBlock (m + 1 + 1) P *
      (slPerm gf2_two (piOdd m P))⁻¹ = omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ := by
  apply slPerm_conj_omegaBlock (piOdd m P)
  · rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc =
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact piOdd_apply_Pcast m P
  · rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ =
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact piOdd_apply_Psucc m P

private theorem piOdd_conj_fixed (m : ℕ) (hm : m % 2 = 1) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) (k : Fin (m + 1 + 1)) (hk2 : k.val % 2 = 0)
    (hkk : k ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1))) (hkP : k ≠ P) :
    slPerm gf2_two (piOdd m P) * omegaBlock (m + 1 + 1) k *
      (slPerm gf2_two (piOdd m P))⁻¹ = omegaBlock (m + 1 + 1) k := by
  apply slPerm_conj_omegaBlock (piOdd m P)
  · apply piOdd_apply_fixed
    · intro h
      apply hkk
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_mk] at hv
      exact hv
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_mk] at hv
      omega
    · intro h
      exact hkP (Fin.castSucc_injective _ h)
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
  · apply piOdd_apply_fixed
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_mk] at hv
      omega
    · intro h
      apply hkk
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_mk] at hv
      show k.val = m + 1
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    · intro h
      exact hkP (Fin.succ_injective _ h)

private theorem piEven_conj_last (m : ℕ) (hm : m % 2 = 0) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) :
    slPerm gf2_two (piEven m P) * omegaBlock (m + 1 + 1) (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) *
      (slPerm gf2_two (piEven m P))⁻¹ = omegaBlock (m + 1 + 1) P := by
  apply slPerm_conj_omegaBlock (piEven m P)
  · rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc =
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact piEven_apply_c1 m hm P hP
  · rw [show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ =
        (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact piEven_apply_b m hm P hP

private theorem piEven_conj_P (m : ℕ) (hm : m % 2 = 0) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) (hPs : P.val + 2 < m + 1 + 1) :
    slPerm gf2_two (piEven m P) * omegaBlock (m + 1 + 1) P *
      (slPerm gf2_two (piEven m P))⁻¹ = omegaBlock (m + 1 + 1) ⟨m, by omega⟩ := by
  have hPa : P.castSucc ≠ (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_mk] at hv
    omega
  apply slPerm_conj_omegaBlock (piEven m P)
  · rw [show (⟨m, by omega⟩ : Fin (m + 1 + 1)).castSucc =
        (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact piEven_apply_Pcast m hm P hP hPa
  · rw [show (⟨m, by omega⟩ : Fin (m + 1 + 1)).succ =
        (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) from Fin.ext rfl]
    exact piEven_apply_Psucc m hm P hP hPa

private theorem piEven_conj_fixed (m : ℕ) (hm : m % 2 = 0) (P : Fin (m + 1 + 1))
    (hP : P.val % 2 = 0) (k : Fin (m + 1 + 1)) (hk2 : k.val % 2 = 0)
    (hklt : k.val + 2 < m + 1 + 1) (hkP : k ≠ P) :
    slPerm gf2_two (piEven m P) * omegaBlock (m + 1 + 1) k *
      (slPerm gf2_two (piEven m P))⁻¹ = omegaBlock (m + 1 + 1) k := by
  have hklt' : k.val ≤ m - 2 := by omega
  apply slPerm_conj_omegaBlock (piEven m P)
  · apply piEven_apply_fixed
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_mk] at hv
      omega
    · intro h
      exact hkP (Fin.castSucc_injective _ h)
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
  · apply piEven_apply_fixed
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    · intro h
      exact hkP (Fin.succ_injective _ h)

private theorem map_halfTorusK_piOdd (m : ℕ) (hm : 3 ≤ m) (hm2 : m % 2 = 1)
    (P : Fin (m + 1 + 1)) (hP : P.val % 2 = 0) :
    (halfTorusK (m + 1 + 1)).map
        (MulAut.conj (slPerm gf2_two (piOdd m P))).toMonoidHom = halfTorus (m + 1 + 1) := by
  apply le_antisymm
  · rw [halfTorusK, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro t ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    rcases hk with hkA | ⟨hk2, hkB⟩
    · have hk_eq : k = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) := by
        apply Fin.ext
        show k.val = m + 1
        omega
      rw [hk_eq, conjTM_apply, piOdd_conj_last m hm2 P hP]
      exact Subgroup.subset_closure ⟨P, hP, rfl⟩
    · by_cases hkP : k = P
      · rw [hkP, conjTM_apply, piOdd_conj_P m P]
        exact Subgroup.subset_closure ⟨⟨m + 1, by omega⟩, by simp only [Fin.val_mk]; omega, rfl⟩
      · have hkk : k ≠ (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_mk] at hv
          omega
        rw [conjTM_apply, piOdd_conj_fixed m hm2 P hP k hk2 hkk hkP]
        exact Subgroup.subset_closure ⟨k, hk2, rfl⟩
  · rw [halfTorus, halfTorusK, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro t ⟨j, hj, rfl⟩
    by_cases hjP : j = P
    · refine Subgroup.subset_closure ⟨omegaBlock (m + 1 + 1) (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)),
        ⟨_, Or.inl (by simp only [Fin.val_mk]), rfl⟩, ?_⟩
      rw [conjTM_apply, piOdd_conj_last m hm2 P hP, hjP]
    · by_cases hjl : j = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1))
      · have hPs : P.val + 2 < m + 1 + 1 := by
          have hne : P.val ≠ m + 1 := by
            intro h
            apply hjP
            rw [hjl]
            apply Fin.ext
            show (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).val = P.val
            simp only [Fin.val_mk]
            omega
          have := P.isLt
          omega
        refine Subgroup.subset_closure ⟨omegaBlock (m + 1 + 1) P,
          ⟨P, Or.inr ⟨hP, hPs⟩, rfl⟩, ?_⟩
        rw [conjTM_apply, piOdd_conj_P m P, hjl]
      · have hjs : j.val + 2 < m + 1 + 1 := by
          have hne : j.val ≠ m + 1 := by
            intro h
            apply hjl
            apply Fin.ext
            show j.val = m + 1
            exact h
          have := j.isLt
          omega
        refine Subgroup.subset_closure ⟨omegaBlock (m + 1 + 1) j,
          ⟨j, Or.inr ⟨hj, hjs⟩, rfl⟩, ?_⟩
        rw [conjTM_apply, piOdd_conj_fixed m hm2 P hP j hj hjl hjP]

private theorem map_halfTorusK_piEven (m : ℕ) (hm : 3 ≤ m) (hm2 : m % 2 = 0)
    (P : Fin (m + 1 + 1)) (hP : P.val % 2 = 0) :
    (halfTorusK (m + 1 + 1)).map
        (MulAut.conj (slPerm gf2_two (piEven m P))).toMonoidHom = halfTorus (m + 1 + 1) := by
  apply le_antisymm
  · rw [halfTorusK, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro t ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    rcases hk with hkA | ⟨hk2, hkB⟩
    · have hk_eq : k = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)) := by
        apply Fin.ext
        show k.val = m + 1
        omega
      rw [hk_eq, conjTM_apply, piEven_conj_last m hm2 P hP]
      exact Subgroup.subset_closure ⟨P, hP, rfl⟩
    · by_cases hkP : k = P
      · have hPs : P.val + 2 < m + 1 + 1 := by rw [← hkP]; exact hkB
        rw [hkP, conjTM_apply, piEven_conj_P m hm2 P hP hPs]
        exact Subgroup.subset_closure ⟨⟨m, by omega⟩, by omega, rfl⟩
      · rw [conjTM_apply, piEven_conj_fixed m hm2 P hP k hk2 hkB hkP]
        exact Subgroup.subset_closure ⟨k, hk2, rfl⟩
  · rw [halfTorus, halfTorusK, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro t ⟨j, hj, rfl⟩
    by_cases hjP : j = P
    · refine Subgroup.subset_closure ⟨omegaBlock (m + 1 + 1) (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)),
        ⟨_, Or.inl (by simp only [Fin.val_mk]), rfl⟩, ?_⟩
      rw [conjTM_apply, piEven_conj_last m hm2 P hP, hjP]
    · by_cases hjm : j.val = m
      · have hj_eq : j = (⟨m, by omega⟩ : Fin (m + 1 + 1)) := Fin.ext hjm
        have hPs : P.val + 2 < m + 1 + 1 := by
          have hPne : P.val ≠ m := by
            intro h
            apply hjP
            exact (Fin.ext (by rw [h, hjm])).symm
          have := P.isLt
          omega
        refine Subgroup.subset_closure ⟨omegaBlock (m + 1 + 1) P,
          ⟨P, Or.inr ⟨hP, hPs⟩, rfl⟩, ?_⟩
        rw [conjTM_apply, piEven_conj_P m hm2 P hP hPs, hj_eq]
      · have hjs : j.val + 2 < m + 1 + 1 := by
          have := j.isLt
          omega
        refine Subgroup.subset_closure ⟨omegaBlock (m + 1 + 1) j,
          ⟨j, Or.inr ⟨hj, hjs⟩, rfl⟩, ?_⟩
        rw [conjTM_apply, piEven_conj_fixed m hm2 P hP j hj hjs hjP]

private theorem map_slOn_levi (m : ℕ) (P : Fin (m + 1 + 1)) (π : Equiv.Perm (Fin (m + 1 + 1 + 1)))
    (h1 : π (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) = P.castSucc)
    (h2 : π (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) = P.succ) :
    (slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val ≤ m}).map
        (MulAut.conj (slPerm gf2_two π)).toMonoidHom =
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} := by
  rw [slOn_map_conj_slPerm]
  congr 1
  ext x
  rw [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor
    · intro h
      have hy1 : y = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
        apply π.injective
        rw [h1, h]
      rw [hy1] at hy
      simp only [Set.mem_setOf_eq, Fin.val_mk] at hy
      omega
    · intro h
      have hy1 : y = (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) := by
        apply π.injective
        rw [h2, h]
      rw [hy1] at hy
      simp only [Set.mem_setOf_eq, Fin.val_mk] at hy
      omega
  · intro hx
    refine ⟨π.symm x, ?_, by simp⟩
    change (π.symm x).val ≤ m
    by_contra hcon
    have hxval : (π.symm x).val = m + 1 ∨ (π.symm x).val = m + 2 := by
      have hlt := (π.symm x).isLt
      omega
    rcases hxval with h | h
    · have hxy : π.symm x = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1 + 1)) := Fin.ext h
      exact hx.1 (by rw [← h1, ← hxy, Equiv.apply_symm_apply])
    · have hxy : π.symm x = (⟨m + 2, by omega⟩ : Fin (m + 1 + 1 + 1)) := Fin.ext h
      exact hx.2 (by rw [← h2, ← hxy, Equiv.apply_symm_apply])

private theorem mem_iff_mem_map_conj {N : ℕ} (c : SpecialLinearGroup (Fin N) F2)
    (H L : Subgroup (SpecialLinearGroup (Fin N) F2))
    (hmap : H.map (MulAut.conj c).toMonoidHom = L)
    (s : SpecialLinearGroup (Fin N) F2) :
    s ∈ H ↔ c * s * c⁻¹ ∈ L := by
  have hcoe : (MulAut.conj c).toMonoidHom s = c * s * c⁻¹ := conjTM_apply c s
  rw [← hcoe, ← hmap]
  constructor
  · intro hs; exact Subgroup.mem_map_of_mem _ hs
  · intro hs
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
    have : x = s := (MulAut.conj c).injective (by simpa using hxs)
    rwa [this] at hx

theorem exists_conj_last (m : ℕ) (hm : 3 ≤ m) (P : Fin (m + 1 + 1)) (hP : P.val % 2 = 0) :
    ∃ c : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2,
      (∀ s, s ∈ halfTorusK (m + 1 + 1) ↔ c * s * c⁻¹ ∈ halfTorus (m + 1 + 1)) ∧
      c * omegaBlock (m + 1 + 1) ⟨m + 1, Nat.lt_succ_self _⟩ * c⁻¹ = omegaBlock (m + 1 + 1) P ∧
      (∀ s, s ∈ (slUpper2Hom m).range ↔
        c * s * c⁻¹ ∈ slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm0 | hm1
  · refine ⟨slPerm gf2_two (piEven m P), ?_, ?_, ?_⟩
    · intro s
      exact mem_iff_mem_map_conj (slPerm gf2_two (piEven m P)) _ _
        (map_halfTorusK_piEven m hm hm0 P hP) s
    · exact piEven_conj_last m hm0 P hP
    · intro s
      rw [range_slUpper2Hom]
      exact mem_iff_mem_map_conj (slPerm gf2_two (piEven m P)) _ _
        (map_slOn_levi m P (piEven m P)
          (piEven_apply_c1 m hm0 P hP) (piEven_apply_b m hm0 P hP)) s
  · refine ⟨slPerm gf2_two (piOdd m P), ?_, ?_, ?_⟩
    · intro s
      exact mem_iff_mem_map_conj (slPerm gf2_two (piOdd m P)) _ _
        (map_halfTorusK_piOdd m hm hm1 P hP) s
    · exact piOdd_conj_last m hm1 P hP
    · intro s
      rw [range_slUpper2Hom]
      exact mem_iff_mem_map_conj (slPerm gf2_two (piOdd m P)) _ _
        (map_slOn_levi m P (piOdd m P)
          (piOdd_apply_last m hm1 P hP) (piOdd_apply_succ m hm1 P hP)) s

end GGHalf

end CFSG.StandardType

end
