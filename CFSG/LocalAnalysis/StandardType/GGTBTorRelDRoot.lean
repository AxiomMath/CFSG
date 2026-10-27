module

public import CFSG.LocalAnalysis.StandardType.GGTorusScalar

@[expose] public section

namespace CFSG.StandardType

namespace RelD

variable {μ : Type} [CommGroup μ] {m : ℕ}

def blockCoord (a : Fin m → μ) : Fin m → μ :=
  fun i => ∏ j ∈ Finset.univ.filter (fun j : Fin m => i ≤ j), a j

@[simp] theorem blockCoord_apply (a : Fin m → μ) (i : Fin m) :
    blockCoord a i = ∏ j ∈ Finset.univ.filter (fun j : Fin m => i ≤ j), a j := rfl

theorem blockCoord_mul (a b : Fin m → μ) :
    blockCoord (a * b) = blockCoord a * blockCoord b := by
  funext i
  simp only [blockCoord, Pi.mul_apply, Finset.prod_mul_distrib]

theorem blockCoord_mul_succ (a : Fin m → μ) (i : Fin m) (hi : i.val + 1 < m) :
    blockCoord a i = a i * blockCoord a ⟨i.val + 1, hi⟩ := by
  classical
  have hset : Finset.univ.filter (fun j : Fin m => i ≤ j) =
      insert i (Finset.univ.filter
        (fun j : Fin m => (⟨i.val + 1, hi⟩ : Fin m) ≤ j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases lt_or_eq_of_le hj with hlt | heq
      · right
        have hval : (⟨i.val + 1, hi⟩ : Fin m).val = i.val + 1 := rfl
        rw [Fin.lt_def] at hlt
        rw [Fin.le_def]
        omega
      · exact Or.inl heq.symm
    · rintro (rfl | hj)
      · exact le_rfl
      · have hj' : i.val + 1 ≤ j.val := Fin.le_def.mp hj
        have hval : (⟨i.val + 1, hi⟩ : Fin m).val = i.val + 1 := rfl
        rw [Fin.le_def]
        omega
  have hnot : i ∉ Finset.univ.filter
      (fun j : Fin m => (⟨i.val + 1, hi⟩ : Fin m) ≤ j) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    have hval : (⟨i.val + 1, hi⟩ : Fin m).val = i.val + 1 := rfl
    rw [Fin.le_def] at h
    omega
  simp only [blockCoord]
  rw [hset, Finset.prod_insert hnot]

theorem blockCoord_eq_self_of_last (a : Fin m → μ) (i : Fin m) (hi : i.val + 1 = m) :
    blockCoord a i = a i := by
  classical
  have hset : Finset.univ.filter (fun j : Fin m => i ≤ j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply Fin.ext
      have := Fin.le_def.mp h
      have hj := j.isLt
      have hi' := i.isLt
      omega
    · rintro rfl
      exact le_rfl
  simp only [blockCoord]
  rw [hset, Finset.prod_singleton]

def invBlockCoord (x : Fin m → μ) : Fin m → μ :=
  fun i => if h : i.val + 1 < m then x i * (x ⟨i.val + 1, h⟩)⁻¹ else x i

theorem invBlockCoord_apply_of_lt (x : Fin m → μ) (i : Fin m) (hi : i.val + 1 < m) :
    invBlockCoord x i = x i * (x ⟨i.val + 1, hi⟩)⁻¹ := by
  simp only [invBlockCoord]
  exact dif_pos hi

theorem invBlockCoord_apply_of_not_lt (x : Fin m → μ) (i : Fin m) (hi : ¬ i.val + 1 < m) :
    invBlockCoord x i = x i := by
  simp only [invBlockCoord]
  exact dif_neg hi

theorem invBlockCoord_blockCoord (a : Fin m → μ) :
    invBlockCoord (blockCoord a) = a := by
  funext i
  by_cases hi : i.val + 1 < m
  · rw [invBlockCoord_apply_of_lt _ _ hi, blockCoord_mul_succ a i hi]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  · have hlast : i.val + 1 = m := by have := i.isLt; omega
    rw [invBlockCoord_apply_of_not_lt _ _ hi, blockCoord_eq_self_of_last a i hlast]

theorem blockCoord_invBlockCoord_succ {n : ℕ} (x : Fin (n + 1) → μ) :
    blockCoord (invBlockCoord x) = x := by
  funext i
  revert i
  refine Fin.reverseInduction (motive := fun i => blockCoord (invBlockCoord x) i = x i) ?_ ?_
  · have hlast : (Fin.last n).val + 1 = n + 1 := by simp
    rw [blockCoord_eq_self_of_last (invBlockCoord x) (Fin.last n) hlast]
    rw [invBlockCoord_apply_of_not_lt x (Fin.last n) (by simp)]
  · intro i ih
    have hi : (Fin.castSucc i).val + 1 < n + 1 := by
      simp only [Fin.val_castSucc]
      omega
    rw [blockCoord_mul_succ (invBlockCoord x) (Fin.castSucc i) hi]
    have hidx : (⟨(Fin.castSucc i).val + 1, hi⟩ : Fin (n + 1)) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ]
    rw [hidx, ih, invBlockCoord_apply_of_lt x (Fin.castSucc i) hi, hidx]
    group

theorem blockCoord_invBlockCoord (x : Fin m → μ) :
    blockCoord (invBlockCoord x) = x := by
  cases m with
  | zero => funext i; exact i.elim0
  | succ n => exact blockCoord_invBlockCoord_succ x

def blockOfRoot : (Fin m → μ) ≃* (Fin m → μ) where
  toFun := blockCoord
  invFun := invBlockCoord
  left_inv := invBlockCoord_blockCoord
  right_inv := blockCoord_invBlockCoord
  map_mul' := blockCoord_mul

theorem blockOfRoot_symm_apply_of_lt (x : Fin m → μ) (i : Fin m) (hi : i.val + 1 < m) :
    blockOfRoot.symm x i = x i * (x ⟨i.val + 1, hi⟩)⁻¹ := by
  change invBlockCoord x i = x i * (x ⟨i.val + 1, hi⟩)⁻¹
  exact invBlockCoord_apply_of_lt x i hi

theorem blockOfRoot_symm_apply_last (x : Fin m → μ) (i : Fin m) (hi : i.val + 1 = m) :
    blockOfRoot.symm x i = x i := by
  have h : ¬ i.val + 1 < m := by omega
  change invBlockCoord x i = x i
  exact invBlockCoord_apply_of_not_lt x i h

theorem blockOfRoot_mul_succ (a : Fin m → μ) (i : Fin m) (hi : i.val + 1 < m) :
    blockOfRoot a i = a i * blockOfRoot a ⟨i.val + 1, hi⟩ :=
  blockCoord_mul_succ a i hi

theorem blockOfRoot_eq_self_of_last (a : Fin m → μ) (i : Fin m) (hi : i.val + 1 = m) :
    blockOfRoot a i = a i :=
  blockCoord_eq_self_of_last a i hi

theorem reflect_apply (a : Fin m → μ) (k j : Fin m) :
    (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) j
      = a j * (a k ^ CartanMatrix.B m j k)⁻¹ := rfl

theorem blockOfRoot_reflect_of_lt (a : Fin m → μ) (k : Fin m) (hk : k.val + 1 < m) :
    blockOfRoot (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) =
      blockOfRoot a ∘ Equiv.swap k ⟨k.val + 1, hk⟩ := by
  classical
  set l : Fin m := ⟨k.val + 1, hk⟩ with hl
  have hlval : l.val = k.val + 1 := by simp [hl]
  set X : Fin m → μ := blockOfRoot a with hX
  set x : Fin m → μ := X ∘ Equiv.swap k l with hx
  have hkey : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) =
      blockOfRoot.symm x := by
    funext i
    by_cases hik : i = k
    · subst i
      rw [blockOfRoot_symm_apply_of_lt x k hk]
      have hxk : x k = X l := by simp [x]
      have hxl : x ⟨k.val + 1, hk⟩ = X k := by
        rw [show (⟨k.val + 1, hk⟩ : Fin m) = l from hl.symm]
        simp [x]
      rw [hxk, hxl]
      have hXk : X k = a k * X l := by
        simpa [hX, hl] using blockOfRoot_mul_succ a k hk
      rw [hXk]
      have ha'k : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) k =
          (a k)⁻¹ := by
        rw [reflect_apply, CartanMatrix.B_diag, zpow_two]
        group
      rw [ha'k]
      group
    · by_cases hil : i = l
      · subst i
        by_cases hilast : l.val + 1 = m
        · rw [blockOfRoot_symm_apply_last x l hilast]
          have hxl : x l = X k := by simp [x]
          rw [hxl]
          have hXk : X k = a k * X l := by
            simpa [hX, hl] using blockOfRoot_mul_succ a k hk
          have hXl : X l = a l := by
            simpa [hX, hl] using blockOfRoot_eq_self_of_last a l hilast
          rw [hXk, hXl]
          have ha'l : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) l =
              a l * a k := by
            rw [reflect_apply]
            have hB : CartanMatrix.B m l k = -1 := by
              rw [hl]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
              split_ifs <;> omega
            rw [hB, zpow_neg_one]
            group
          rw [ha'l]
          exact mul_comm _ _
        · have hlnext : l.val + 1 < m := by have := l.isLt; omega
          rw [blockOfRoot_symm_apply_of_lt x l hlnext]
          have hxl : x l = X k := by simp [x]
          have hxnext : x ⟨l.val + 1, hlnext⟩ = X ⟨l.val + 1, hlnext⟩ := by
            have hval : (⟨l.val + 1, hlnext⟩ : Fin m).val = l.val + 1 := rfl
            have hne1 : (⟨l.val + 1, hlnext⟩ : Fin m) ≠ k := by
              intro h
              have := congrArg Fin.val h
              omega
            have hne2 : (⟨l.val + 1, hlnext⟩ : Fin m) ≠ l := by
              intro h
              have := congrArg Fin.val h
              omega
            simp [x, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
          rw [hxl, hxnext]
          have hXk : X k = a k * X l := by
            simpa [hX, hl] using blockOfRoot_mul_succ a k hk
          have hXl : X l = a l * X ⟨l.val + 1, hlnext⟩ := by
            simpa [hX, hl] using blockOfRoot_mul_succ a l hlnext
          rw [hXk, hXl]
          have ha'l : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) l =
              a l * a k := by
            rw [reflect_apply]
            have hB : CartanMatrix.B m l k = -1 := by
              rw [hl]
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
              split_ifs <;> omega
            rw [hB, zpow_neg_one]
            group
          rw [ha'l, mul_comm (a l) (a k)]
          group
      · by_cases hip : i.val + 1 = k.val
        · have hi_lt : i.val + 1 < m := by rw [hip]; exact k.isLt
          rw [blockOfRoot_symm_apply_of_lt x i hi_lt]
          have hxi : x i = X i := by
            have hne1 : i ≠ k := hik
            have hne2 : i ≠ l := hil
            simp [x, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
          have hidx : (⟨i.val + 1, hi_lt⟩ : Fin m) = k := Fin.ext (by simp [hip])
          have hxnext : x ⟨i.val + 1, hi_lt⟩ = X l := by
            rw [hidx]
            simp [x]
          rw [hxi, hxnext]
          have hXi : X i = a i * X k := by
            simpa [hX, hidx] using blockOfRoot_mul_succ a i hi_lt
          have hXk : X k = a k * X l := by
            simpa [hX, hl] using blockOfRoot_mul_succ a k hk
          rw [hXi, hXk]
          have ha'i : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) i =
              a i * a k := by
            rw [reflect_apply]
            have hB : CartanMatrix.B m i k = -1 := by
              simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
              split_ifs <;> omega
            rw [hB, zpow_neg_one]
            group
          rw [ha'i]
          group
        · have hikv : i.val ≠ k.val := fun h => hik (Fin.ext h)
          have hkprev : k.val + 1 ≠ i.val := by
            intro h
            apply hil
            apply Fin.ext
            rw [hlval]
            omega
          have hBik : CartanMatrix.B m i k = 0 := by
            simp only [CartanMatrix.B, Matrix.of_apply]
            rw [if_neg hik, if_neg hip, if_neg hkprev]
          by_cases hilast : i.val + 1 = m
          · rw [blockOfRoot_symm_apply_last x i hilast]
            have hxi : x i = X i := by
              have hne1 : i ≠ k := hik
              have hne2 : i ≠ l := hil
              simp [x, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
            rw [hxi]
            have hXlast : X i = a i := by
              simpa [hX, hl] using blockOfRoot_eq_self_of_last a i hilast
            rw [hXlast]
            have ha'i : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) i =
                a i := by
              rw [reflect_apply, hBik]
              simp
            rw [ha'i]
          · have hi_lt : i.val + 1 < m := by have := i.isLt; omega
            rw [blockOfRoot_symm_apply_of_lt x i hi_lt]
            have hxi : x i = X i := by
              have hne1 : i ≠ k := hik
              have hne2 : i ≠ l := hil
              simp [x, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
            have hxnext : x ⟨i.val + 1, hi_lt⟩ = X ⟨i.val + 1, hi_lt⟩ := by
              have hval : (⟨i.val + 1, hi_lt⟩ : Fin m).val = i.val + 1 := rfl
              have hne1 : (⟨i.val + 1, hi_lt⟩ : Fin m) ≠ k := by
                intro h
                have := congrArg Fin.val h
                omega
              have hne2 : (⟨i.val + 1, hi_lt⟩ : Fin m) ≠ l := by
                intro h
                have h2 := congrArg Fin.val h
                rw [hlval] at h2
                omega
              simp [x, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
            rw [hxi, hxnext]
            have hXi : X i = a i * X ⟨i.val + 1, hi_lt⟩ := by
              simpa [hX, hl] using blockOfRoot_mul_succ a i hi_lt
            rw [hXi]
            have ha'i : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) i =
                a i := by
              rw [reflect_apply, hBik]
              simp
            rw [ha'i]
            group
  rw [hkey, MulEquiv.apply_symm_apply]

theorem blockOfRoot_reflect_last (a : Fin m → μ) (k : Fin m) (hk : k.val + 1 = m) :
    blockOfRoot (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) =
      Function.update (blockOfRoot a) k (blockOfRoot a k)⁻¹ := by
  classical
  set X : Fin m → μ := blockOfRoot a with hX
  set x : Fin m → μ := Function.update X k (X k)⁻¹ with hx
  have hkey : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) =
      blockOfRoot.symm x := by
    funext i
    by_cases hik : i = k
    · subst i
      rw [blockOfRoot_symm_apply_last x k hk]
      have hxk : x k = (X k)⁻¹ := by
        rw [hx, Function.update_self]
      rw [hxk]
      have hXk : X k = a k := by
        simpa [hX] using blockOfRoot_eq_self_of_last a k hk
      rw [hXk]
      have ha'k : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) k =
          (a k)⁻¹ := by
        rw [reflect_apply, CartanMatrix.B_diag, zpow_two]
        group
      rw [ha'k]
    · by_cases hip : i.val + 1 = k.val
      · have hi_lt : i.val + 1 < m := by rw [hip]; exact k.isLt
        rw [blockOfRoot_symm_apply_of_lt x i hi_lt]
        have hidx : (⟨i.val + 1, hi_lt⟩ : Fin m) = k := Fin.ext (by simp [hip])
        have hxi : x i = X i := by
          rw [hx, Function.update_of_ne hik]
        have hxnext : x ⟨i.val + 1, hi_lt⟩ = (X k)⁻¹ := by
          rw [hidx, hx, Function.update_self]
        rw [hxi, hxnext]
        have hXi : X i = a i * X k := by
          simpa [hX, hidx] using blockOfRoot_mul_succ a i hi_lt
        rw [hXi]
        have hXk : X k = a k := by
          simpa [hX] using blockOfRoot_eq_self_of_last a k hk
        rw [hXk]
        have ha'i : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) i =
            a i * (a k * a k) := by
          rw [reflect_apply]
          have hB : CartanMatrix.B m i k = -2 := by
            simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
            split_ifs <;> omega
          rw [hB]
          have hzpow : ((a k) ^ (-2 : ℤ))⁻¹ = a k * a k := by
            rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, inv_inv, zpow_two]
          rw [hzpow]
        rw [ha'i]
        group
      · have hikv : i.val ≠ k.val := fun h => hik (Fin.ext h)
        have hkprev : k.val + 1 ≠ i.val := by
          intro h
          have := i.isLt
          omega
        have hBik : CartanMatrix.B m i k = 0 := by
          simp only [CartanMatrix.B, Matrix.of_apply]
          rw [if_neg hik, if_neg hip, if_neg hkprev]
        have hi_lt : i.val + 1 < m := by
          have := i.isLt
          have := k.isLt
          omega
        rw [blockOfRoot_symm_apply_of_lt x i hi_lt]
        have hxi : x i = X i := by
          rw [hx, Function.update_of_ne hik]
        have hxnext : x ⟨i.val + 1, hi_lt⟩ = X ⟨i.val + 1, hi_lt⟩ := by
          have hval : (⟨i.val + 1, hi_lt⟩ : Fin m).val = i.val + 1 := rfl
          have hne : (⟨i.val + 1, hi_lt⟩ : Fin m) ≠ k := by
            intro h
            have := congrArg Fin.val h
            omega
          rw [hx, Function.update_of_ne hne]
        rw [hxi, hxnext]
        have hXi : X i = a i * X ⟨i.val + 1, hi_lt⟩ := by
          simpa [hX] using blockOfRoot_mul_succ a i hi_lt
        rw [hXi]
        have ha'i : (a * (corTuple (CartanMatrix.B m).transpose k (a k))⁻¹) i =
            a i := by
          rw [reflect_apply, hBik]
          simp
        rw [ha'i]
        group
  rw [hkey, MulEquiv.apply_symm_apply]

theorem exists_int_matrix_inverse_mod_B {M n : ℕ} (hn : 0 < n) (hM : Odd M) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ,
      (Int.castRingHom (ZMod M)).mapMatrix (CartanMatrix.B n * B) = 1 ∧
        (Int.castRingHom (ZMod M)).mapMatrix (B * CartanMatrix.B n) = 1 := by
  refine exists_int_matrix_inverse_mod_of_isUnit_det _ ?_
  rw [CartanMatrix.B_det hn]
  have h := (ZMod.isUnit_iff_coprime 2 M).mpr (Nat.coprime_two_left.mpr hM)
  simpa using h

end RelD

end CFSG.StandardType
