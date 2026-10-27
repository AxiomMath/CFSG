module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112AModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable def ggAE_x {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (b : Basis (Fin n) (ZMod 3) U) (a : Fin (n + 1)) : Module.Dual (ZMod 3) U :=
  ∑ j : Fin n, ((if a = j.castSucc then (1 : ZMod 3) else 0)
      - (if a = j.succ then (1 : ZMod 3) else 0)) • b.coord j

lemma ggAE_x_self {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (b : Basis (Fin n) (ZMod 3) U) (a : Fin (n + 1)) (k : Fin n) :
    ggAE_x b a (b k) = (if a = k.castSucc then (1 : ZMod 3) else 0)
      - (if a = k.succ then (1 : ZMod 3) else 0) := by
  classical
  rw [ggAE_x, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply, Basis.repr_self_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [if_neg (fun h : k = j => hj h.symm), mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma ggAE_A_apply (n : ℕ) (u v : Fin n) :
    CartanMatrix.A n u v = if u = v then (2 : ℤ)
      else if (u.val + 1 = v.val ∨ v.val + 1 = u.val) then -1 else 0 := by
  simp [CartanMatrix.A, Matrix.of_apply]

lemma ggAE_A_eq (n : ℕ) (i j : Fin n) :
    ((CartanMatrix.A n i j : ℤ) : ZMod 3) =
      ((if i.castSucc = j.castSucc then (1 : ZMod 3) else 0)
        - (if i.castSucc = j.succ then (1 : ZMod 3) else 0))
      - ((if i.succ = j.castSucc then (1 : ZMod 3) else 0)
        - (if i.succ = j.succ then (1 : ZMod 3) else 0)) := by
  rw [ggAE_A_apply]
  push_cast
  have hcc : (i.castSucc = j.castSucc) ↔ (i = j) := by
    rw [Fin.ext_iff]; simp only [Fin.val_castSucc]; exact Fin.ext_iff.symm
  have hss : (i.succ = j.succ) ↔ (i = j) := by
    rw [Fin.ext_iff, Fin.ext_iff]; simp only [Fin.val_succ]; omega
  have hcs : (i.castSucc = j.succ) ↔ (j.val + 1 = i.val) := by
    rw [Fin.ext_iff]; simp only [Fin.val_castSucc, Fin.val_succ]; omega
  have hsc : (i.succ = j.castSucc) ↔ (i.val + 1 = j.val) := by
    rw [Fin.ext_iff]; simp only [Fin.val_succ, Fin.val_castSucc]
  rw [if_congr hcc rfl rfl, if_congr hss rfl rfl, if_congr hcs rfl rfl,
    if_congr hsc rfl rfl]
  by_cases hij : i = j
  · subst hij
    have hlt : ¬ (i.val + 1 = i.val) := by omega
    simp
    norm_num
  · simp only [if_neg hij]
    by_cases hcase : (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    · rw [if_pos hcase]
      rcases hcase with hc | hc
      · have h2 : ¬ (j.val + 1 = i.val) := by omega
        simp only [if_neg h2, if_pos hc]
        ring
      · have h1 : ¬ (i.val + 1 = j.val) := by omega
        simp only [if_pos hc, if_neg h1]
        ring
    · have h1 : ¬ (i.val + 1 = j.val) := fun h => hcase (Or.inl h)
      have h2 : ¬ (j.val + 1 = i.val) := fun h => hcase (Or.inr h)
      simp only [if_neg hcase, if_neg h1, if_neg h2]
      ring

lemma ggAE_const_of_adj {m : ℕ} {R : Type} (y : Fin (m + 1) → R)
    (hadj : ∀ i : Fin m, y i.castSucc = y i.succ) : ∀ c c', y c = y c' := by
  have hy : ∀ c : Fin (m + 1), y c = y 0 := by
    intro c
    induction c using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hadj i).symm.trans ih
  intro c c'
  rw [hy c, hy c']

private lemma ggAE_sum_pred {n : ℕ} (t : Fin n → ZMod 3) (j : Fin n) :
    (∑ k : Fin n, t k * (if k.val + 1 = j.val then (1 : ZMod 3) else 0)) =
      (if h : 0 < j.val then t ⟨j.val - 1, by have := j.isLt; omega⟩ else 0) := by
  by_cases h : 0 < j.val
  · rw [dif_pos h]
    rw [Finset.sum_eq_single ⟨j.val - 1, by have := j.isLt; omega⟩]
    · have hv : (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin n).val = j.val - 1 := rfl
      rw [hv]
      have hh : j.val - 1 + 1 = j.val := by omega
      rw [hh, if_pos rfl, mul_one]
    · intro k _ hk
      rw [if_neg, mul_zero]
      intro hc
      apply hk
      apply Fin.ext
      show k.val = j.val - 1
      omega
    · intro hj; exact absurd (Finset.mem_univ _) hj
  · rw [dif_neg h]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_neg, mul_zero]
    intro hc
    omega

private lemma ggAE_row {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (b : Basis (Fin n) (ZMod 3) U) (v : U) (j : Fin n) :
    ggAE_x b j.castSucc v =
      b.repr v j - (if h : 0 < j.val then b.repr v ⟨j.val - 1, by have := j.isLt; omega⟩
        else 0) := by
  classical
  have hrow : ∀ k : Fin n, ggAE_x b j.castSucc (b k) =
      (if j = k then (1 : ZMod 3) else 0)
        - (if k.val + 1 = j.val then (1 : ZMod 3) else 0) := by
    intro k
    rw [ggAE_x_self]
    have hc1 : (j.castSucc = k.castSucc) ↔ (j = k) := by
      rw [Fin.ext_iff]; simp only [Fin.val_castSucc]; exact Fin.ext_iff.symm
    have hc2 : (j.castSucc = k.succ) ↔ (k.val + 1 = j.val) := by
      rw [Fin.ext_iff]; simp only [Fin.val_castSucc, Fin.val_succ]; omega
    rw [if_congr hc1 rfl rfl, if_congr hc2 rfl rfl]
  conv_lhs => rw [(b.sum_repr v).symm]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  trans ∑ k : Fin n, b.repr v k *
      ((if j = k then (1 : ZMod 3) else 0)
        - (if k.val + 1 = j.val then (1 : ZMod 3) else 0))
  · exact Finset.sum_congr rfl (fun k _ => by rw [hrow k])
  · have hsum1 : (∑ k : Fin n, b.repr v k * (if j = k then (1 : ZMod 3) else 0)) =
        b.repr v j := by
      rw [Finset.sum_eq_single j]
      · rw [if_pos rfl, mul_one]
      · intro k _ hk
        rw [if_neg (fun h : j = k => hk h.symm), mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    trans (∑ k : Fin n, b.repr v k * (if j = k then (1 : ZMod 3) else 0))
        - (∑ k : Fin n, b.repr v k * (if k.val + 1 = j.val then (1 : ZMod 3) else 0))
    · rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by rw [mul_sub])
    · rw [hsum1, ggAE_sum_pred]

lemma ggAE_sep {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (b : Basis (Fin n) (ZMod 3) U) (hn : 0 < n) (v : U)
    (hv : ∀ j : Fin n, ggAE_x b j.castSucc v = 0) : v = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let t : Fin (m + 1) → ZMod 3 := fun k => b.repr v k
  have ht0 : t 0 = 0 := by
    have h0 := hv 0
    rw [ggAE_row b v 0] at h0
    simpa [t] using h0
  have ht_succ : ∀ i : Fin m, t i.succ = t i.castSucc := by
    intro i
    have hsi := hv i.succ
    rw [ggAE_row b v i.succ] at hsi
    have hpos : 0 < (i.succ : Fin (m + 1)).val := by simp [Fin.val_succ]
    rw [dif_pos hpos] at hsi
    have hpred : (⟨(i.succ : Fin (m + 1)).val - 1,
        by have := (i.succ : Fin (m + 1)).isLt; omega⟩ : Fin (m + 1)) = i.castSucc := by
      apply Fin.ext
      simp [Fin.val_succ]
    rw [hpred] at hsi
    exact sub_eq_zero.mp hsi
  have ht : ∀ k : Fin (m + 1), t k = 0 := by
    intro k
    induction k using Fin.induction with
    | zero => exact ht0
    | succ i ih => rw [ht_succ i, ih]
  have hrepr : b.repr v = 0 := Finsupp.ext (fun k => by simpa [t] using ht k)
  rw [← b.sum_repr v, hrepr]
  simp

private noncomputable def ggAE_seg {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin n → U) (lo hi : ℕ) : U :=
  ∑ k ∈ Finset.Ico lo hi, (if hk : k < n then h ⟨k, hk⟩ else 0)

private lemma ggAE_x_seg {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin n → U) (b : Basis (Fin n) (ZMod 3) U) (hb : ∀ k, h k = b k)
    (c : Fin (n + 1)) {lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ n) :
    ggAE_x b c (ggAE_seg h lo hi) =
      (if c.val = lo then (1 : ZMod 3) else 0)
        - (if c.val = hi then (1 : ZMod 3) else 0) := by
  rw [ggAE_seg, map_sum]
  trans ∑ k ∈ Finset.Ico lo hi,
      ((if c.val = k then (1 : ZMod 3) else 0)
        - (if c.val = k + 1 then (1 : ZMod 3) else 0))
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkn : k < n := by have := (Finset.mem_Ico.mp hk).2; omega
    rw [dif_pos hkn, hb ⟨k, hkn⟩, ggAE_x_self]
    have hc1 : (c = (⟨k, hkn⟩ : Fin n).castSucc) ↔ (c.val = k) := by
      rw [Fin.ext_iff]; simp only [Fin.val_castSucc]
    have hc2 : (c = (⟨k, hkn⟩ : Fin n).succ) ↔ (c.val = k + 1) := by
      rw [Fin.ext_iff]; simp only [Fin.val_succ]
    rw [if_congr hc1 rfl rfl, if_congr hc2 rfl rfl]
  · have htel := Finset.sum_Ico_sub (fun k => if c.val = k then (1 : ZMod 3) else 0) hlo
    calc ∑ k ∈ Finset.Ico lo hi,
          ((if c.val = k then (1 : ZMod 3) else 0)
            - (if c.val = k + 1 then (1 : ZMod 3) else 0))
        = -∑ k ∈ Finset.Ico lo hi,
            ((if c.val = k + 1 then (1 : ZMod 3) else 0)
              - (if c.val = k then (1 : ZMod 3) else 0)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
      _ = -((if c.val = hi then (1 : ZMod 3) else 0)
            - (if c.val = lo then (1 : ZMod 3) else 0)) := by rw [htel]
      _ = (if c.val = lo then (1 : ZMod 3) else 0)
            - (if c.val = hi then (1 : ZMod 3) else 0) := by ring

lemma ggAE_exists_diff {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin n → U) (b : Basis (Fin n) (ZMod 3) U) (hb : ∀ k, h k = b k)
    (a d : Fin (n + 1)) (had : a ≠ d) :
    ∃ u : U, ∀ c : Fin (n + 1), ggAE_x b c u =
      (if c = a then (1 : ZMod 3) else 0) - (if c = d then (1 : ZMod 3) else 0) := by
  rcases lt_or_gt_of_ne (fun hv : a.val = d.val => had (Fin.ext hv)) with hlt | hgt
  · refine ⟨ggAE_seg h a.val d.val, fun c => ?_⟩
    rw [ggAE_x_seg h b hb c (le_of_lt hlt) (Nat.le_of_lt_succ d.isLt)]
    have ha : (c.val = a.val) ↔ (c = a) := Fin.ext_iff.symm
    have hd : (c.val = d.val) ↔ (c = d) := Fin.ext_iff.symm
    rw [if_congr ha rfl rfl, if_congr hd rfl rfl]
  · refine ⟨-ggAE_seg h d.val a.val, fun c => ?_⟩
    rw [map_neg, ggAE_x_seg h b hb c (le_of_lt hgt) (Nat.le_of_lt_succ a.isLt)]
    have ha : (c.val = a.val) ↔ (c = a) := Fin.ext_iff.symm
    have hd : (c.val = d.val) ↔ (c = d) := Fin.ext_iff.symm
    rw [if_congr hd rfl rfl, if_congr ha rfl rfl]
    ring

theorem ggAE_x_equiv {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin n → U) (α : Fin n → Module.Dual (ZMod 3) U)
    (Φ : Equiv.Perm (Fin (n + 1)) →* (U ≃ₗ[ZMod 3] U))
    (hΦswap : ∀ (i : Fin n) (v : U),
      Φ (Equiv.swap i.castSucc i.succ) v = v - α i v • h i)
    (x : Fin (n + 1) → Module.Dual (ZMod 3) U)
    (hαx : ∀ i, α i = x i.castSucc - x i.succ)
    (hx_h : ∀ a i, x a (h i) =
      (if a = i.castSucc then (1 : ZMod 3) else 0)
        - (if a = i.succ then (1 : ZMod 3) else 0)) :
    ∀ σ a u, x a (Φ σ u) = x (σ⁻¹ a) u := by
  have hP : ∀ σ : Equiv.Perm (Fin (n + 1)), ∀ a u, x a (Φ σ u) = x (σ⁻¹ a) u := by
    intro σ
    refine Submonoid.dense_induction
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ)
      (Equiv.Perm.mclosure_swap_castSucc_succ n) ?_ ?_ ?_ σ
    · rintro t ⟨i, rfl⟩
      intro a u
      rw [hΦswap i u, hαx i, LinearMap.sub_apply, map_sub, map_smul, smul_eq_mul, hx_h a i,
        Equiv.swap_inv]
      by_cases h1 : a = i.castSucc
      · subst h1
        rw [Equiv.swap_apply_left, if_pos rfl, if_neg Fin.castSucc_lt_succ.ne]
        ring
      · by_cases h2 : a = i.succ
        · subst h2
          rw [Equiv.swap_apply_right, if_neg Fin.castSucc_lt_succ.ne.symm, if_pos rfl]
          ring
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, if_neg h1, if_neg h2]
          ring
    · intro a u
      simp
    · intro σ τ hσ hτ a u
      rw [map_mul, LinearEquiv.mul_apply, hσ a (Φ τ u), hτ (σ⁻¹ a) u, mul_inv_rev,
        Equiv.Perm.mul_apply]
  exact fun σ a u => hP σ a u

end CFSG.StandardType

end
