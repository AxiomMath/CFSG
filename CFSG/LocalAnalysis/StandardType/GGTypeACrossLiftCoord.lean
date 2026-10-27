module

public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverDefs

public section

namespace CFSG.StandardType.TypeAReflOver

private theorem kRefl_coordPerm_coord {p n : ℕ} {a : Fin (n + 1)}
    (v : Fin (n + 1) → ZMod p) (i : Fin (n + 1)) :
    coordPerm p n (Equiv.swap a (Fin.last n))
        (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) v)) i =
      v i - v a * (if i = a then 2 else 1) := by
  classical
  have hσsymm : (Equiv.swap a (Fin.last n)).symm = Equiv.swap a (Fin.last n) :=
    Equiv.symm_swap a (Fin.last n)
  have hσσ : ∀ j, Equiv.swap a (Fin.last n) (Equiv.swap a (Fin.last n) j) = j :=
    fun j => Equiv.swap_apply_self a (Fin.last n) j
  have hσlast : Equiv.swap a (Fin.last n) (Fin.last n) = a :=
    Equiv.swap_apply_right a (Fin.last n)
  have hσa : Equiv.swap a (Fin.last n) a = Fin.last n :=
    Equiv.swap_apply_left a (Fin.last n)
  have hw : ∀ j, coordPerm p n (Equiv.swap a (Fin.last n)) v j =
      v (Equiv.swap a (Fin.last n) j) := fun j => by rw [coordPerm_apply, hσsymm]
  rw [coordPerm_apply, hσsymm, kRefl_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hw, hσσ, hσlast]
  have hkroot : kRoot p n (Equiv.swap a (Fin.last n) i) = if i = a then 2 else 1 := by
    by_cases hi : i = a
    · rw [hi, hσa, if_pos rfl, kRoot, Pi.add_apply, Pi.one_apply, Pi.single_eq_same]
      norm_num
    · have hσi : Equiv.swap a (Fin.last n) i ≠ Fin.last n := by
        intro h
        have h2 : Equiv.swap a (Fin.last n) (Equiv.swap a (Fin.last n) i) =
            Equiv.swap a (Fin.last n) (Fin.last n) := by rw [h]
        rw [hσσ i, hσlast] at h2
        exact hi h2
      rw [if_neg hi, kRoot, Pi.add_apply, Pi.one_apply, Pi.single_eq_of_ne hσi]
      ring
  rw [hkroot]

theorem eq_single_zero_of_fixed {p n : ℕ} (v : Fin (n + 1) → ZMod p)
    (hσ : ∀ a b : Fin n, coordPerm p n (Equiv.swap a.succ b.succ) v = v)
    (hR : kRefl p n v = v) : v = Pi.single 0 (v 0) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    funext j
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    rw [hj, Pi.single_eq_same]
  · have hlast : v (Fin.last n) = 0 := by
      have h0 : (0 : Fin (n + 1)) ≠ Fin.last n := by
        intro h
        have h1 := congrArg Fin.val h
        rw [Fin.val_last, Fin.val_zero] at h1
        omega
      have hk : kRoot p n (0 : Fin (n + 1)) = 1 := by
        rw [kRoot, Pi.add_apply, Pi.one_apply, Pi.single_eq_of_ne h0]
        ring
      have h := congrFun hR 0
      rw [kRefl_apply] at h
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hk, mul_one] at h
      exact sub_eq_self.mp h
    funext j
    by_cases hj : j = 0
    · rw [hj, Pi.single_eq_same]
    · obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hj
      subst hk
      have hne : (k.succ : Fin (n + 1)) ≠ 0 := by
        intro h
        have h1 := congrArg Fin.val h
        rw [Fin.val_succ] at h1
        have h2 : k.val + 1 = 0 := h1
        omega
      rw [Pi.single_eq_of_ne hne]
      have hb : (⟨n - 1, by omega⟩ : Fin n).succ = Fin.last n :=
        Fin.ext (by simp only [Fin.val_succ, Fin.val_last, Fin.val_mk]; omega)
      have h := congrFun (hσ k ⟨n - 1, by omega⟩) k.succ
      rw [coordPerm_apply, Equiv.symm_swap, Equiv.swap_apply_left, hb] at h
      exact h.symm.trans hlast

theorem eq_zero_of_kThreeRefl_single {p n : ℕ} (hn : 1 ≤ n) {c : ZMod p}
    (h : kThreeRefl p n (Pi.single 0 c) = Pi.single 0 c) : c = 0 := by
  classical
  have hlast : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro h'
    have h1 := congrArg Fin.val h'
    rw [Fin.val_last, Fin.val_zero] at h1
    omega
  have hsum : (∑ i : Fin n,
      (Pi.single (0 : Fin (n + 1)) c : Fin (n + 1) → ZMod p) i.castSucc) = c := by
    have hcast := Fin.sum_univ_castSucc
      (f := fun i : Fin (n + 1) =>
        (Pi.single (0 : Fin (n + 1)) c : Fin (n + 1) → ZMod p) i)
    rw [Fintype.sum_pi_single', Pi.single_eq_of_ne hlast, add_zero] at hcast
    exact hcast.symm
  have h := congrFun h (Fin.last n)
  rw [kThreeRefl_apply] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kThreeRoot, Pi.single_eq_same,
    Pi.single_eq_of_ne hlast, mul_zero, add_zero, mul_one, zero_sub, hsum] at h
  exact neg_eq_zero.mp h

theorem kThreeRefl_commute_swap_kRefl {p n : ℕ} (hp : p ∣ n + 3) {a : Fin (n + 1)}
    (ha : a ≠ Fin.last n) (v : Fin (n + 1) → ZMod p) :
    kThreeRefl p n (coordPerm p n (Equiv.swap a (Fin.last n))
        (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) v))) =
      coordPerm p n (Equiv.swap a (Fin.last n))
        (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) (kThreeRefl p n v))) := by
  classical
  have hpc : ((n + 3 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + 3) p).mpr hp
  have h3 : (n : ZMod p) + 3 = 0 := by
    have h := hpc
    push_cast at h
    exact h
  have hv : ((n : ZMod p) + 2) * v a = -v a := by
    have h : ((n : ZMod p) + 3) * v a = 0 := by rw [h3, zero_mul]
    calc ((n : ZMod p) + 2) * v a = ((n : ZMod p) + 3) * v a - v a := by ring
      _ = -v a := by rw [h, zero_sub]
  have hThree : ∀ (y : Fin (n + 1) → ZMod p) (i : Fin (n + 1)),
      kThreeRefl p n y i = if i = Fin.last n then -(∑ j, y j) else y i := by
    intro y i
    rw [kThreeRefl_apply]
    by_cases hi : i = Fin.last n
    · subst hi
      rw [if_pos rfl, Fin.sum_univ_castSucc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kThreeRoot, Pi.single_eq_same,
        mul_one]
      ring
    · rw [if_neg hi]
      have hk : kThreeRoot p n i = 0 := by
        rw [kThreeRoot, Pi.single_apply, if_neg hi]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hk, mul_zero, sub_zero]
  have hcastsum : (∑ j : Fin n,
        coordPerm p n (Equiv.swap a (Fin.last n))
          (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) v)) j.castSucc) =
      ∑ j : Fin n, v j.castSucc - ((n : ZMod p) + 1) * v a := by
    have hne : a.val ≠ n := by
      intro h
      exact ha (Fin.ext (by rw [Fin.val_last]; exact h))
    have hlt : a.val < n := by omega
    obtain ⟨a', ha'⟩ : ∃ a' : Fin n, a'.castSucc = a :=
      ⟨⟨a.val, hlt⟩, Fin.ext rfl⟩
    have hterm : ∀ j : Fin n,
        coordPerm p n (Equiv.swap a (Fin.last n))
          (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) v)) j.castSucc =
        v j.castSucc - v a + (if j = a' then -v a else 0) := by
      intro j
      rw [kRefl_coordPerm_coord v j.castSucc]
      by_cases hj : j = a'
      · rw [hj, ha', if_pos rfl, if_pos rfl]
        ring
      · have hcond : ¬ (j.castSucc = a) := fun h =>
          hj (Fin.castSucc_injective n (h.trans ha'.symm))
        rw [if_neg hcond, if_neg hj, mul_one]
        ring
    have hcorr : (∑ j : Fin n, (if j = a' then -v a else 0)) = -v a := by
      rw [Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hcorr]
    ring
  have hsumM : (∑ j : Fin (n + 1),
        coordPerm p n (Equiv.swap a (Fin.last n))
          (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) v)) j) =
      (∑ j : Fin (n + 1), v j) - ((n : ZMod p) + 2) * v a := by
    have h1 := Fin.sum_univ_castSucc (f := fun j : Fin (n + 1) =>
      coordPerm p n (Equiv.swap a (Fin.last n))
        (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) v)) j)
    have h2 := Fin.sum_univ_castSucc (f := v)
    rw [h1, h2, hcastsum, kRefl_coordPerm_coord v (Fin.last n), if_neg ha.symm, mul_one]
    ring
  funext i
  by_cases hi : i = Fin.last n
  · subst hi
    rw [hThree (coordPerm p n (Equiv.swap a (Fin.last n))
          (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) v))) (Fin.last n), if_pos rfl,
      kRefl_coordPerm_coord (kThreeRefl p n v) (Fin.last n), hThree v (Fin.last n), if_pos rfl,
      hThree v a, if_neg ha, if_neg ha.symm, hsumM, mul_one, hv]
    ring
  · rw [hThree (coordPerm p n (Equiv.swap a (Fin.last n))
          (kRefl p n (coordPerm p n (Equiv.swap a (Fin.last n)) v))) i, if_neg hi,
      kRefl_coordPerm_coord (kThreeRefl p n v) i, hThree v i, if_neg hi, hThree v a, if_neg ha]
    exact kRefl_coordPerm_coord v i

end CFSG.StandardType.TypeAReflOver

end
