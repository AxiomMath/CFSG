module

public import CFSG.Timmesfeld.ARS.CaseERootSys
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Steinberg

namespace CaseOA

theorem sum_neg_of_nonpos_of_ne_zero {I : Type} [Fintype I] {v : I → ℤ} (h : v ≤ 0)
    (hv : v ≠ 0) : ∑ i, v i < 0 := by
  by_contra hcon
  have h0 : ∑ i, v i = 0 := le_antisymm (Finset.sum_nonpos fun i _ => h i) (not_lt.1 hcon)
  apply hv
  funext i
  exact (Finset.sum_eq_zero_iff_of_nonpos fun i _ => h i).1 h0 i (Finset.mem_univ i)

theorem sum_mul_single_comp {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Fin n → ℤ) (a : Fin n)
    (x : ℤ) : ∑ c, f c * (Pi.single a x : Fin n → ℤ) (π c) = f (π.symm a) * x := by
  rw [← Equiv.sum_comp π.symm]
  simp only [Equiv.apply_symm_apply, Pi.single_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

section TypeA

open SpecialLinear

variable {m : ℕ}

theorem exists_perm_toStd_weylAction (w : (coxeterMatrix (isFiniteType_A m)).Group) :
    ∃ π : Equiv.Perm (Fin (m + 1)),
      ∀ v, toStd m (weylAction (isFiniteType_A m) w v) = toStd m v ∘ π := by
  obtain ⟨ω, rfl⟩ := (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.wordProd_surjective w
  induction ω with
  | nil => exact ⟨1, fun v => by simp [CoxeterSystem.wordProd_nil]⟩
  | cons k ω ih =>
    obtain ⟨π, hπ⟩ := ih
    refine ⟨π * Equiv.swap k.castSucc k.succ, fun v => ?_⟩
    rw [CoxeterSystem.wordProd_cons, map_mul, Module.End.mul_apply, weylAction_simple,
      toStd_reflection, hπ]
    rfl

theorem symm_lt_of_longest_A {w₀ : (coxeterMatrix (isFiniteType_A m)).Group}
    (hw₀ : ∀ w, (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length w ≤
      (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.length w₀)
    {π : Equiv.Perm (Fin (m + 1))}
    (hπ : ∀ v, toStd m (weylAction (isFiniteType_A m) w₀ v) = toStd m v ∘ π) (k : Fin m) :
    π.symm k.succ < π.symm k.castSucc := by
  have hnp := weylAction_nonpos_of_forall_length_le (isFiniteType_A m) hw₀
    (γ := Pi.single k 1) (fun i => by simp only [Pi.single_apply]; split_ifs <;> norm_num)
  have hne := weylAction_single_ne_zero (isFiniteType_A m) w₀ k
  have hht := sum_neg_of_nonpos_of_ne_zero hnp hne
  change ht (weylAction (isFiniteType_A m) w₀ (Pi.single k 1)) < 0 at hht
  rw [ht_eq_sum_toStd, hπ, toStd_single] at hht
  simp only [Function.comp_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at hht
  rw [sum_mul_single_comp, sum_mul_single_comp] at hht
  have h1 := (π.symm k.succ).isLt
  have h2 := (π.symm k.castSucc).isLt
  rw [Fin.lt_def]
  omega

theorem weylAction_longest_ne_A3 {w₀ : (coxeterMatrix (isFiniteType_A 3)).Group}
    (hw₀ : ∀ w, (coxeterMatrix (isFiniteType_A 3)).toCoxeterSystem.length w ≤
      (coxeterMatrix (isFiniteType_A 3)).toCoxeterSystem.length w₀)
    {j : Fin 3} (hj : j ≠ 1) :
    weylAction (isFiniteType_A 3) w₀ (Pi.single j 1) ≠ -Pi.single j 1 := by
  intro hjw
  obtain ⟨π, hπ⟩ := exists_perm_toStd_weylAction w₀
  have h0 : (π.symm 1).val < (π.symm 0).val := symm_lt_of_longest_A hw₀ hπ 0
  have h1 : (π.symm 2).val < (π.symm 1).val := symm_lt_of_longest_A hw₀ hπ 1
  have h2 : (π.symm 3).val < (π.symm 2).val := symm_lt_of_longest_A hw₀ hπ 2
  have hb0 := (π.symm 0).isLt
  have hb3 := (π.symm 3).isLt
  have e0 : π.symm 0 = 3 := Fin.ext (show (π.symm 0).val = 3 by omega)
  have e2 : π.symm 2 = 1 := Fin.ext (show (π.symm 2).val = 1 by omega)
  have key := congrArg (toStd 3) hjw
  rw [hπ, toStd_neg] at key
  fin_cases j
  · have e := congrFun key (π.symm 0)
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.neg_apply] at e
    rw [e0, toStd_single] at e
    revert e
    decide
  · exact absurd rfl hj
  · have e := congrFun key (π.symm 2)
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.neg_apply] at e
    rw [e2, toStd_single] at e
    revert e
    decide

end TypeA

section TypeD

open Spin

variable {m : ℕ}

theorem exists_signedPerm_toStdD_weylAction (hm : 2 ≤ m)
    (w : (coxeterMatrix (isFiniteType_cartanD m)).Group) :
    ∃ (π : Equiv.Perm (Fin m)) (s : Fin m → ℤ), (∀ c, s c = 1 ∨ s c = -1) ∧ ∏ c, s c = 1 ∧
      ∀ v, toStdD m (weylAction (isFiniteType_cartanD m) w v) =
        fun c => s c * toStdD m v (π c) := by
  obtain ⟨ω, rfl⟩ :=
    (coxeterMatrix (isFiniteType_cartanD m)).toCoxeterSystem.wordProd_surjective w
  induction ω with
  | nil =>
    exact ⟨1, fun _ => 1, fun _ => Or.inl rfl, by simp, fun v => by
      funext c
      simp [CoxeterSystem.wordProd_nil]⟩
  | cons k ω ih =>
    obtain ⟨π, s, hs, hprod, hπ⟩ := ih
    by_cases hk : k.val + 1 < m
    · refine ⟨π * Equiv.swap k ⟨k.val + 1, hk⟩, s ∘ Equiv.swap k ⟨k.val + 1, hk⟩,
        fun c => hs _, ?_, fun v => ?_⟩
      · rw [← hprod]
        exact Equiv.prod_comp (Equiv.swap k ⟨k.val + 1, hk⟩) s
      · rw [CoxeterSystem.wordProd_cons, map_mul, Module.End.mul_apply, weylAction_simple,
          toStdD_reflection_of_lt m hk, hπ]
        rfl
    · set p : Fin m := ⟨k.val - 1, by omega⟩ with hp
      have hpk : p ≠ k := Fin.ne_of_val_ne (by simp only [hp]; omega)
      have hkm : k.val + 1 = m := by have := k.isLt; omega
      have hε : ∀ c : Fin m, (if c.val + 2 = m ∨ c.val + 1 = m then (-1 : ℤ) else 1) =
          (if c = p then -1 else 1) * (if c = k then -1 else 1) := by
        intro c
        by_cases hcp : c = p
        · rw [hcp, ite_eq_left (Or.inl (by simp only [hp]; omega)), ite_eq_left rfl,
            ite_eq_right hpk]
          ring
        by_cases hck : c = k
        · rw [hck, ite_eq_left (Or.inr hkm), ite_eq_right (Ne.symm hpk), ite_eq_left rfl]
          ring
        rw [ite_eq_right hcp, ite_eq_right hck, ite_eq_right]
        · ring
        · rintro (h' | h')
          · exact hcp (Fin.ext (by simp only [hp]; omega))
          · exact hck (Fin.ext (by omega))
      refine ⟨π * Equiv.swap p k, fun c =>
        (if c.val + 2 = m ∨ c.val + 1 = m then -1 else 1) * s (Equiv.swap p k c), fun c => ?_,
        ?_, fun v => ?_⟩
      · show (if c.val + 2 = m ∨ c.val + 1 = m then (-1 : ℤ) else 1) * s (Equiv.swap p k c) = 1 ∨
          (if c.val + 2 = m ∨ c.val + 1 = m then (-1 : ℤ) else 1) * s (Equiv.swap p k c) = -1
        rcases hs (Equiv.swap p k c) with h' | h' <;> split_ifs <;> simp [h']
      · rw [Finset.prod_mul_distrib]
        simp_rw [hε]
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq',
          Equiv.prod_comp (Equiv.swap p k) s, hprod]
        simp
      · rw [CoxeterSystem.wordProd_cons, map_mul, Module.End.mul_apply, weylAction_simple,
          toStdD_reflection, stdReflD_of_not_lt m hk, hπ]
        funext c
        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        ring

theorem weylAction_longest_spin_ne (hm : 2 ≤ m) (hodd : Odd m)
    {w₀ : (coxeterMatrix (isFiniteType_cartanD m)).Group}
    (hw₀ : ∀ w, (coxeterMatrix (isFiniteType_cartanD m)).toCoxeterSystem.length w ≤
      (coxeterMatrix (isFiniteType_cartanD m)).toCoxeterSystem.length w₀)
    {j : Fin m} (hj : j.val + 2 = m ∨ j.val + 1 = m) :
    weylAction (isFiniteType_cartanD m) w₀ (Pi.single j 1) ≠ -Pi.single j 1 := by
  intro hjw
  have hm1 : m ≠ 1 := by omega
  obtain ⟨π, s, hs, hprod, hπ⟩ := exists_signedPerm_toStdD_weylAction hm w₀
  set q : Fin m := ⟨m - 1, by omega⟩ with hq
  have hht : ∀ v, ht (weylAction (isFiniteType_cartanD m) w₀ v) =
      ∑ c : Fin m, ((m : ℤ) - 1 - c) * (s c * toStdD m v (π c)) := fun v => by
    rw [ht_eq_sum_toStdD m hm1, hπ]
  have hneg : ∀ a : Fin m, a.val + 1 < m → s (π.symm a) = -1 := by
    intro a ha
    have haq : a ≠ q := Fin.ne_of_val_ne (by simp only [hq]; omega)
    have haq' : a < q := by rw [Fin.lt_def]; simp only [hq]; omega
    have key : ∀ t : ℤ, (t = 1 ∨ t = -1) →
        ((m : ℤ) - 1 - π.symm a) * s (π.symm a) + t * (((m : ℤ) - 1 - π.symm q) *
          s (π.symm q)) < 0 := by
      intro t ht₁
      obtain ⟨v, hv, hvs⟩ := exists_mem_rootsD_toStdD_eq m haq (Or.inl rfl) ht₁
      have hpos : 0 < ht v :=
        (ht_pos_iff_of_toStdD_eq_add m hm1 haq' (Or.inl rfl) ht₁ hvs).2 rfl
      have hv0 : 0 ≤ v := by
        rcases nonneg_or_nonpos (isFiniteType_cartanD m) ∅ hv with h' | h'
        · exact h'
        · exfalso
          have : ht v ≤ 0 := Finset.sum_nonpos fun i _ => h' i
          omega
      have hnp := weylAction_nonpos_of_forall_length_le (isFiniteType_cartanD m) hw₀ hv0
      have hne : weylAction (isFiniteType_cartanD m) w₀ v ≠ 0 := by
        rw [← map_zero (weylAction (isFiniteType_cartanD m) w₀), Ne,
          (weylAction_apply_injective (isFiniteType_cartanD m) w₀).eq_iff]
        rintro rfl
        simp [ht] at hpos
      have hlt := sum_neg_of_nonpos_of_ne_zero hnp hne
      change ht (weylAction (isFiniteType_cartanD m) w₀ v) < 0 at hlt
      rw [hht, hvs] at hlt
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at hlt
      have e1 := sum_mul_single_comp π (fun c => ((m : ℤ) - 1 - c) * s c) a 1
      have e2 := sum_mul_single_comp π (fun c => ((m : ℤ) - 1 - c) * s c) q t
      simp only [mul_assoc] at e1 e2
      rw [e1, e2] at hlt
      linarith
    have k1 := key 1 (Or.inl rfl)
    have k2 := key (-1) (Or.inr rfl)
    have hb : (0 : ℤ) ≤ (m : ℤ) - 1 - π.symm a := by
      have := (π.symm a).isLt
      omega
    rcases hs (π.symm a) with h' | h'
    · rw [h'] at k1 k2
      nlinarith
    · exact h'
  have key := congrArg (toStdD m) hjw
  rw [hπ, toStdD_neg] at key
  have hlast : s (π.symm q) = -1 := by
    rcases hj with hj2 | hj1
    ·
      have hjq : (⟨j.val + 1, by omega⟩ : Fin m) = q := Fin.ext (by simp only [hq]; omega)
      have hjlt : j.val + 1 < m := by omega
      rw [toStdD_single_of_lt m hjlt, hjq] at key
      have hjq' : j ≠ q := Fin.ne_of_val_ne (by simp only [hq]; omega)
      have e := congrFun key (π.symm q)
      simp only [Equiv.apply_symm_apply, Pi.neg_apply, Pi.sub_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hjq'.symm] at e
      rcases hs (π.symm q) with h' | h'
      · exfalso
        rw [h'] at e
        have hcj : π.symm q = j := by
          by_contra hcj
          by_cases hcq : π.symm q = q
          · rw [hcq, Pi.single_eq_same, Pi.single_eq_of_ne hjq'.symm] at e
            norm_num at e
          · rw [Pi.single_eq_of_ne hcj, Pi.single_eq_of_ne hcq] at e
            norm_num at e
        have hsj := hneg j hjlt
        have e' := congrFun key (π.symm j)
        simp only [Equiv.apply_symm_apply, Pi.neg_apply, Pi.sub_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne hjq', hsj] at e'
        have hcj' : π.symm j ≠ j := fun h'' => by
          have := π.symm.injective (h''.trans hcj.symm)
          exact hjq' this
        rw [Pi.single_eq_of_ne hcj'] at e'
        by_cases hcq' : π.symm j = q
        · rw [hcq', Pi.single_eq_same] at e'
          norm_num at e'
        · rw [Pi.single_eq_of_ne hcq'] at e'
          norm_num at e'
      · exact h'
    ·
      have hjq : j = q := Fin.ext (by simp only [hq]; omega)
      have hjlt : ¬ j.val + 1 < m := by omega
      rw [toStdD_single_of_not_lt m hjlt hm, hjq] at key
      have e := congrFun key (π.symm q)
      simp only [Equiv.apply_symm_apply, Pi.neg_apply, Pi.add_apply, Pi.single_eq_same] at e
      have hpq : (⟨m - 2, by omega⟩ : Fin m) ≠ q := Fin.ne_of_val_ne (by simp only [hq]; omega)
      rw [Pi.single_eq_of_ne hpq.symm] at e
      have hnn : (0 : ℤ) ≤ (Pi.single (⟨m - 2, by omega⟩ : Fin m) (1 : ℤ) : Fin m → ℤ) (π.symm q) +
          (Pi.single q (1 : ℤ) : Fin m → ℤ) (π.symm q) := by
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      rcases hs (π.symm q) with h' | h'
      · exfalso
        rw [h'] at e
        linarith
      · exact h'
  have hall : ∀ c, s c = -1 := by
    intro c
    by_cases hc : (π c).val + 1 < m
    · have := hneg (π c) hc
      rwa [Equiv.symm_apply_apply] at this
    · have hcq : π c = q := Fin.ext (by simp only [hq]; omega)
      rw [← hlast, ← hcq, Equiv.symm_apply_apply]
  rw [Finset.prod_congr rfl fun c _ => hall c, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hodd.neg_one_pow] at hprod
  norm_num at hprod

end TypeD

end CaseOA

end CFSG.Timmesfeld.ARS
