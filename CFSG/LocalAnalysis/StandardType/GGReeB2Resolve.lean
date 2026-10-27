module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import CFSG.LocalAnalysis.StandardType.GGReeB2StepThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGReeB2SigmaOrder
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

open scoped Pointwise

public section

namespace CFSG.StandardType.ReeB2Fixed

private lemma two_pow_e_eq_one (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) :
    (2 : ZMod (2 ^ e - 1)) ^ e = 1 := by
  have hpos : 0 < 2 ^ e := pow_pos (by norm_num) e
  have hsplit : (2 : ℕ) ^ e = (2 ^ e - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos hpos).symm
  have hcast :
      (2 : ZMod (2 ^ e - 1)) ^ e = ((2 ^ e : ℕ) : ZMod (2 ^ e - 1)) := by
    push_cast
    ring
  rw [hcast, hsplit, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]

private lemma two_pow_succσ (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) (p : Fin e) :
    (2 : ZMod (2 ^ e - 1)) ^ ((succσ e p : Fin e) : ℕ) = 2 ^ (p : ℕ) * r e := by
  have h2e := two_pow_e_eq_one e he h3
  have hv : ((succσ e p : Fin e) : ℕ) = (p + (e + 1) / 2) % e := rfl
  rw [hv, (pow_eq_pow_mod (p + (e + 1) / 2) h2e).symm, pow_add]
  rfl

private lemma succσ_injective (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) :
    Function.Injective (succσ e) := by
  intro p q hpq
  apply Fin.ext
  have hmod :
      ((p : ℕ) + (e + 1) / 2) % e = ((q : ℕ) + (e + 1) / 2) % e := by
    have := congrArg (fun x : Fin e => (x : ℕ)) hpq
    simpa [succσ] using this
  have hmeq : (p : ℕ) ≡ (q : ℕ) [MOD e] :=
    Nat.ModEq.add_right_cancel' ((e + 1) / 2) hmod
  exact Nat.ModEq.eq_of_lt_of_lt hmeq p.isLt q.isLt

private lemma units_add_eq_mul_r (e : ℕ) (he : Odd e) (h3 : 3 ≤ e)
    (c : ZMod (2 ^ e - 1)) (hc : c ∈ units e) :
    ∃ u ∈ units e, ∃ u' ∈ units e, u + u' = c * r e := by
  simp only [units, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · refine ⟨1, by simp [units], R e, by simp [units], ?_⟩
    have hR : R e = r e - 1 := rfl
    rw [hR]
    ring
  · refine ⟨-1, by simp [units], -R e, by simp [units], ?_⟩
    have hR : R e = r e - 1 := rfl
    rw [hR]
    ring
  · refine ⟨1, by simp [units], -R e, by simp [units], ?_⟩
    have hR : R e = r e - 1 := rfl
    have hrsq : r e ^ 2 = 2 := r_sq e he
    rw [hR]
    calc 1 + -(r e - 1) = 2 - r e := by ring
      _ = r e ^ 2 - r e := by rw [hrsq]
      _ = (r e - 1) * r e := by ring
  · refine ⟨-1, by simp [units], R e, by simp [units], ?_⟩
    have hR : R e = r e - 1 := rfl
    have hrsq : r e ^ 2 = 2 := r_sq e he
    rw [hR]
    calc -1 + (r e - 1) = r e - 2 := by ring
      _ = -(r e ^ 2 - r e) := by rw [hrsq]; ring
      _ = -(r e - 1) * r e := by ring

private lemma units_pair (e : ℕ) (he : Odd e) (h3 : 3 ≤ e)
    (c : ZMod (2 ^ e - 1)) (hc : c ∈ units e) :
    ∃ u : ZMod (2 ^ e - 1) × ZMod (2 ^ e - 1),
      u.1 ∈ units e ∧ u.2 ∈ units e ∧ u.1 + u.2 = c * r e := by
  obtain ⟨u, hu, v, hv, huv⟩ := units_add_eq_mul_r e he h3 c hc
  exact ⟨(u, v), hu, hv, huv⟩

theorem lam_resolve_subset (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) (A B : Finset (Fin e))
    (hI : IndepSigma e A) : Lam e (resolve e A B) ⊆ Lam e A + Lam e B := by
  classical
  haveI : NeZero e := ⟨by omega⟩
  intro x hx
  rcases hx with ⟨c, hc, hxeq⟩
  rw [hxeq]
  let F : Finset (Fin e) := (A ∩ B).filter fun p => succσ e p ∉ B
  have hresolve : resolve e A B = symmDiff A B ∪ F.image (succσ e) := rfl
  have hmemF : ∀ j, j ∈ A → j ∈ B → succσ e j ∉ B →
      succσ e j ∈ resolve e A B := by
    intro j hA hB hσ
    rw [hresolve]
    refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, ?_, rfl⟩))
    simp only [F, Finset.mem_filter, Finset.mem_inter]
    exact ⟨⟨hA, hB⟩, hσ⟩
  let uu : Fin e → ZMod (2 ^ e - 1) × ZMod (2 ^ e - 1) := fun j =>
    if h : j ∈ A ∧ j ∈ B ∧ succσ e j ∉ B then
      Classical.choose (units_pair e he h3 (c (succσ e j))
        (hc (succσ e j) (hmemF j h.1 h.2.1 h.2.2)))
    else (1, -1)
  have huu_units : ∀ j, (uu j).1 ∈ units e ∧ (uu j).2 ∈ units e := by
    intro j
    dsimp only [uu]
    by_cases h : j ∈ A ∧ j ∈ B ∧ succσ e j ∉ B
    · rw [dif_pos h]
      have hspec := Classical.choose_spec (units_pair e he h3 (c (succσ e j))
        (hc (succσ e j) (hmemF j h.1 h.2.1 h.2.2)))
      exact ⟨hspec.1, hspec.2.1⟩
    · rw [dif_neg h]
      simp [units]
  have huu_add : ∀ j (hA : j ∈ A) (hB : j ∈ B) (hσ : succσ e j ∉ B),
      (uu j).1 + (uu j).2 = c (succσ e j) * r e := by
    intro j hA hB hσ
    have h : j ∈ A ∧ j ∈ B ∧ succσ e j ∉ B := ⟨hA, hB, hσ⟩
    dsimp only [uu]
    rw [dif_pos h]
    exact (Classical.choose_spec (units_pair e he h3 (c (succσ e j))
      (hc (succσ e j) (hmemF j hA hB hσ)))).2.2
  let cA : Fin e → ZMod (2 ^ e - 1) := fun j =>
    if j ∈ A then (if j ∈ B then (uu j).1 else c j) else 1
  let cB : Fin e → ZMod (2 ^ e - 1) := fun j =>
    if j ∈ B then (if j ∈ A then (uu j).2 else c j) else 1
  have hcA : ∀ j ∈ A, cA j ∈ units e := by
    intro j hA
    dsimp only [cA]
    rw [if_pos hA]
    by_cases hB : j ∈ B
    · rw [if_pos hB]
      exact (huu_units j).1
    · rw [if_neg hB]
      exact hc j (by
        rw [hresolve]
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_symmDiff.mpr (Or.inl ⟨hA, hB⟩))))
  have hcB : ∀ j ∈ B, cB j ∈ units e := by
    intro j hB
    dsimp only [cB]
    rw [if_pos hB]
    by_cases hA : j ∈ A
    · rw [if_pos hA]
      exact (huu_units j).2
    · rw [if_neg hA]
      exact hc j (by
        rw [hresolve]
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_symmDiff.mpr (Or.inr ⟨hB, hA⟩))))
  let y : ZMod (2 ^ e - 1) := ∑ j ∈ A, cA j * 2 ^ (j : ℕ)
  let z : ZMod (2 ^ e - 1) := ∑ j ∈ B, cB j * 2 ^ (j : ℕ)
  have hy : y ∈ Lam e A := ⟨cA, hcA, rfl⟩
  have hz : z ∈ Lam e B := ⟨cB, hcB, rfl⟩
  refine Set.mem_add.mpr ⟨y, hy, z, hz, ?_⟩
  have hAB : A \ (A ∩ B) = A \ B := by
    ext j; simp
  have hBA : B \ (A ∩ B) = B \ A := by
    ext j; simp
  have hyA : y = (∑ j ∈ A \ B, cA j * 2 ^ (j : ℕ)) +
      ∑ j ∈ A ∩ B, cA j * 2 ^ (j : ℕ) := by
    dsimp only [y]
    have h := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := A)
      (f := fun j => cA j * 2 ^ (j : ℕ)) Finset.inter_subset_left
    rw [hAB] at h
    exact h.symm
  have hzB : z = (∑ j ∈ B \ A, cB j * 2 ^ (j : ℕ)) +
      ∑ j ∈ A ∩ B, cB j * 2 ^ (j : ℕ) := by
    dsimp only [z]
    have h := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := B)
      (f := fun j => cB j * 2 ^ (j : ℕ)) Finset.inter_subset_right
    rw [hBA] at h
    exact h.symm
  have hSA : (∑ j ∈ A \ B, cA j * 2 ^ (j : ℕ)) =
      ∑ j ∈ A \ B, c j * 2 ^ (j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hA, hBn⟩ := Finset.mem_sdiff.mp hj
    have hcAval : cA j = c j := by
      dsimp only [cA]
      rw [if_pos hA, if_neg hBn]
    rw [hcAval]
  have hSB : (∑ j ∈ B \ A, cB j * 2 ^ (j : ℕ)) =
      ∑ j ∈ B \ A, c j * 2 ^ (j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hB, hAn⟩ := Finset.mem_sdiff.mp hj
    have hcBval : cB j = c j := by
      dsimp only [cB]
      rw [if_pos hB, if_neg hAn]
    rw [hcBval]
  have hdisjSA : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hSsym : (∑ j ∈ A \ B, c j * 2 ^ (j : ℕ)) +
      (∑ j ∈ B \ A, c j * 2 ^ (j : ℕ)) =
      ∑ j ∈ symmDiff A B, c j * 2 ^ (j : ℕ) := by
    rw [← Finset.sum_union hdisjSA]
    rfl
  have hIntSplit : (∑ j ∈ A ∩ B, cA j * 2 ^ (j : ℕ)) +
      (∑ j ∈ A ∩ B, cB j * 2 ^ (j : ℕ)) =
      ∑ j ∈ A ∩ B, (cA j + cB j) * 2 ^ (j : ℕ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hIntSum : (∑ j ∈ A ∩ B, (cA j + cB j) * 2 ^ (j : ℕ)) =
      ∑ i ∈ F.image (succσ e), c i * 2 ^ (i : ℕ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (A ∩ B)
      (fun j => succσ e j ∉ B) (fun j => (cA j + cB j) * 2 ^ (j : ℕ))]
    have hF_eq : (A ∩ B).filter (fun j => succσ e j ∉ B) = F := rfl
    rw [hF_eq]
    have hnot : (∑ j ∈ (A ∩ B).filter (fun j => ¬ succσ e j ∉ B),
        (cA j + cB j) * 2 ^ (j : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjAB, hjσ⟩ := hj
      obtain ⟨hA, hB⟩ := Finset.mem_inter.mp hjAB
      have hcond : ¬ (j ∈ A ∧ j ∈ B ∧ succσ e j ∉ B) := by
        rintro ⟨-, -, hσ⟩
        exact hjσ hσ
      have huu : uu j = (1, -1) := by
        dsimp only [uu]
        rw [dif_neg hcond]
      have hcAval : cA j = 1 := by
        dsimp only [cA]; rw [if_pos hA, if_pos hB, huu]
      have hcBval : cB j = -1 := by
        dsimp only [cB]; rw [if_pos hB, if_pos hA, huu]
      rw [hcAval, hcBval]
      simp
    rw [hnot, add_zero]
    rw [Finset.sum_image (s := F) (g := succσ e)
      (f := fun i => c i * 2 ^ (i : ℕ)) ((succσ_injective e he h3).injOn)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjAB, hjσ⟩ := hj
    obtain ⟨hA, hB⟩ := Finset.mem_inter.mp hjAB
    have hcAval : cA j = (uu j).1 := by
      dsimp only [cA]; rw [if_pos hA, if_pos hB]
    have hcBval : cB j = (uu j).2 := by
      dsimp only [cB]; rw [if_pos hB, if_pos hA]
    rw [hcAval, hcBval, huu_add j hA hB hjσ]
    rw [two_pow_succσ e he h3 j]
    ring
  have hdisjX : Disjoint (symmDiff A B) (F.image (succσ e)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_symmDiff] at ha
    rw [Finset.mem_image] at hb
    obtain ⟨p, hpF, hp_eq⟩ := hb
    rw [Finset.mem_filter, Finset.mem_inter] at hpF
    obtain ⟨⟨hpA, hpB⟩, hpσ⟩ := hpF
    have hpσA : succσ e p ∉ A := hI p hpA
    rw [← hp_eq] at ha
    rcases ha with ⟨haA, _⟩ | ⟨haB, _⟩
    · exact hpσA haA
    · exact hpσ haB
  have hxsplit : (∑ j ∈ resolve e A B, c j * 2 ^ (j : ℕ)) =
      (∑ j ∈ symmDiff A B, c j * 2 ^ (j : ℕ)) +
      ∑ i ∈ F.image (succσ e), c i * 2 ^ (i : ℕ) := by
    rw [hresolve, Finset.sum_union hdisjX]
  calc y + z = ((∑ j ∈ A \ B, cA j * 2 ^ (j : ℕ)) +
        ∑ j ∈ A ∩ B, cA j * 2 ^ (j : ℕ)) +
        ((∑ j ∈ B \ A, cB j * 2 ^ (j : ℕ)) +
        ∑ j ∈ A ∩ B, cB j * 2 ^ (j : ℕ)) := by rw [hyA, hzB]
    _ = ((∑ j ∈ A \ B, cA j * 2 ^ (j : ℕ)) +
        ∑ j ∈ B \ A, cB j * 2 ^ (j : ℕ)) +
        ((∑ j ∈ A ∩ B, cA j * 2 ^ (j : ℕ)) +
        ∑ j ∈ A ∩ B, cB j * 2 ^ (j : ℕ)) := by ring
    _ = ((∑ j ∈ A \ B, c j * 2 ^ (j : ℕ)) +
        ∑ j ∈ B \ A, c j * 2 ^ (j : ℕ)) +
        ((∑ j ∈ A ∩ B, cA j * 2 ^ (j : ℕ)) +
        ∑ j ∈ A ∩ B, cB j * 2 ^ (j : ℕ)) := by rw [hSA, hSB]
    _ = (∑ j ∈ symmDiff A B, c j * 2 ^ (j : ℕ)) +
        ∑ j ∈ A ∩ B, (cA j + cB j) * 2 ^ (j : ℕ) := by rw [hSsym, hIntSplit]
    _ = (∑ j ∈ symmDiff A B, c j * 2 ^ (j : ℕ)) +
        ∑ i ∈ F.image (succσ e), c i * 2 ^ (i : ℕ) := by rw [hIntSum]
    _ = ∑ j ∈ resolve e A B, c j * 2 ^ (j : ℕ) := hxsplit.symm

end CFSG.StandardType.ReeB2Fixed
