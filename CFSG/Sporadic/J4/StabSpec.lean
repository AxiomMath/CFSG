module

public import CFSG.Sporadic.J4.GlobalSpec
import Certificates.Data.CFSGNative.J4.Orbit
import Certificates.Data.CFSGNative.J4.Global
import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4

open Native CFSG.Sporadic.Th

section Facts

variable (hF : J4NativeFacts)
include hF

theorem b_pow_four : (b : J) ^ 4 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, b_coe, gB_val hF.mat, matB_pow_four hF.mat]
  rfl

theorem a_inv_mul_self : (a⁻¹ : J) * a⁻¹ = 1 := by rw [← mul_inv_rev, a_mul_self hF, inv_one]

theorem globalAt_all : ∀ i < nPts, globalAt GD0 i = true := by
  have h := hF.global
  unfold globalOK at h
  rw [GD0_fields.1] at h
  exact parAllR_eq_true h

noncomputable abbrev schr (s : J) (i : ℕ) : J := (trans (idx nPts s i))⁻¹ * s * trans i

theorem testA {i : ℕ} (hi : i < nPts) (h : reqA GD0 i = true) : schr (a⁻¹) i ∈ Hj := by
  have hg := globalAt_all hF i hi
  unfold globalAt at hg
  simp only [h, Bool.true_or, ite_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hg
  simpa [sGen] using globalTest_spec hF hi hg.1

theorem testB {i : ℕ} (hi : i < nPts) (h : reqB GD0 i = true) : schr (b⁻¹) i ∈ Hj := by
  have hg := globalAt_all hF i hi
  unfold globalAt at hg
  simp only [h, Bool.or_true, ite_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hg
  simpa [sGen] using globalTest_spec hF hi hg.2

theorem trans_of_edge {l i j : ℕ} (hj : j < nPts) (he : treeEdge t20.1 l i j = true) :
    trans j = treeL l * trans i := treeElt_of_treeEdge (treeFacts0 hF) hj he

theorem idxA_idxA {i : ℕ} : idx nPts (a⁻¹ : J) (idx nPts (a⁻¹ : J) i) = i := by
  rw [← idx_mul, a_inv_mul_self hF, idx_one]

theorem schrA_cases {i : ℕ} (hi : i < nPts) :
    schr (a⁻¹) i ∈ Hj ∨ schr (a⁻¹) (idx nPts (a⁻¹ : J) i) ∈ Hj := by
  set j := idx nPts (a⁻¹ : J) i with hjd
  have hj : j < nPts := idx_lt _ hi
  have hta : rdU32 bs0.alpha i = j := rep_ta hF i hi
  have htj : rdU32 bs0.alpha j = i := by rw [rep_ta hF j hj, hjd, idxA_idxA hF]
  by_cases e1 : treeEdge t20.1 1 i j = true
  · left
    show (trans j)⁻¹ * a⁻¹ * trans i ∈ Hj
    rw [trans_of_edge hF hj e1]
    simp only [treeL, letterG, ite_true, mul_inv_rev, inv_mul_cancel_right, inv_mul_cancel]
    exact Hj.one_mem
  by_cases e2 : treeEdge t20.1 1 j i = true
  · left
    show (trans j)⁻¹ * a⁻¹ * trans i ∈ Hj
    rw [trans_of_edge hF hi e2]
    simp only [treeL, letterG, ite_true]
    rw [mul_assoc, ← mul_assoc (a⁻¹ : J), a_inv_mul_self hF, one_mul, inv_mul_cancel]
    exact Hj.one_mem
  rw [Bool.not_eq_true] at e1 e2
  obtain ⟨-, hga, -, -, hgp, -, -, -, -, -, -, -, -⟩ := GD0_fields
  rcases Nat.lt_or_ge i j with hlt | hle
  · right
    apply testA hF hj
    unfold reqA
    rw [hga, hgp]
    simp only [htj]
    simp [e1, e2, hlt]
  · left
    apply testA hF hi
    unfold reqA
    rw [hga, hgp]
    simp only [hta]
    simp only [e1, e2, Bool.not_false, Bool.true_and, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    omega

noncomputable abbrev nb (i : ℕ) : ℕ := idx nPts (b⁻¹ : J) i

theorem nb_four {i : ℕ} : nb (nb (nb (nb i))) = i := by
  have e4 : (b⁻¹ : J) ^ 4 = 1 := by rw [inv_pow, b_pow_four hF, inv_one]
  have e : (b⁻¹ : J) * b⁻¹ * b⁻¹ * b⁻¹ = 1 := by
    rw [← e4]
    simp only [pow_succ, pow_zero, one_mul]
  simp only [nb]
  rw [← idx_mul, ← idx_mul, ← idx_mul, e, idx_one]

theorem rdB {i : ℕ} (hi : i < nPts) : rdU32 bs0.beta i = nb i := rep_tb hF i hi

theorem schrB_of_triv {i : ℕ} (hi : i < nPts) (h : trivB GD0 i = true) : schr (b⁻¹) i ∈ Hj := by
  have hj : nb i < nPts := idx_lt _ hi
  obtain ⟨-, -, hgb, -, hgp, -, -, -, -, -, -, -, -⟩ := GD0_fields
  unfold trivB at h
  rw [hgb, hgp] at h
  simp only [rdB hF hi, Bool.or_eq_true] at h
  show (trans (nb i))⁻¹ * b⁻¹ * trans i ∈ Hj
  rcases h with h | h
  · rw [trans_of_edge hF hj h]
    simp only [treeL, letterG, ite_eq_right (by decide : (2 : ℕ) ≠ 1), ite_true, mul_inv_rev,
      inv_mul_cancel_right, inv_mul_cancel]
    exact Hj.one_mem
  · rw [trans_of_edge hF hi h]
    simp only [treeL, letterG, ite_eq_right (by decide : (3 : ℕ) ≠ 1), ite_eq_right (by decide : (3 : ℕ) ≠ 2)]
    rw [mul_assoc, ← mul_assoc (b⁻¹ : J), inv_mul_cancel, one_mul, inv_mul_cancel]
    exact Hj.one_mem

theorem schrB_cases {i : ℕ} (hi : i < nPts) :
    schr (b⁻¹) i ∈ Hj ∨
      (schr (b⁻¹) (nb i) ∈ Hj ∧ schr (b⁻¹) (nb (nb i)) ∈ Hj ∧ schr (b⁻¹) (nb (nb (nb i))) ∈ Hj) := by
  have h1 : nb i < nPts := idx_lt _ hi
  have h2 : nb (nb i) < nPts := idx_lt _ h1
  have h3 : nb (nb (nb i)) < nPts := idx_lt _ h2
  have h4 := nb_four hF (i := i)
  by_cases ht : trivB GD0 i = true
  · exact Or.inl (schrB_of_triv hF hi ht)
  by_cases hr : reqB GD0 i = true
  · exact Or.inl (testB hF hi hr)
  right
  rw [Bool.not_eq_true] at ht hr
  have hreq : ∀ {p : ℕ}, p < nPts → trivB GD0 p = false → reqB GD0 p =
      (nb p == p || nb (nb p) == p || (!trivB GD0 (nb p) && nb p < p) ||
        (!trivB GD0 (nb (nb p)) && nb (nb p) < p) ||
        (!trivB GD0 (nb (nb (nb p))) && nb (nb (nb p)) < p)) := by
    intro p hp htp
    have q1 : nb p < nPts := idx_lt _ hp
    have q2 : nb (nb p) < nPts := idx_lt _ q1
    unfold reqB
    rw [(GD0_fields).2.2.1]
    simp only [rdB hF hp, rdB hF q1, rdB hF q2, htp, Bool.not_false, Bool.true_and]
  rw [hreq hi ht] at hr
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
    Bool.not_eq_false', decide_eq_false_iff_not, not_lt] at hr
  obtain ⟨⟨⟨⟨hn1, hn2⟩, hc1⟩, hc2⟩, hc3⟩ := hr
  have mem : ∀ {p : ℕ}, p < nPts → (trivB GD0 p = true ∨ reqB GD0 p = true) →
      schr (b⁻¹) p ∈ Hj := by
    intro p hp h
    rcases h with h | h
    · exact schrB_of_triv hF hp h
    · exact testB hF hp h
  have hti : (!trivB GD0 i) = true := by rw [ht]; rfl
  refine ⟨mem h1 ?_, mem h2 ?_, mem h3 ?_⟩
  · by_cases t1 : trivB GD0 (nb i) = true
    · exact Or.inl t1
    right
    rw [Bool.not_eq_true] at t1
    rw [hreq h1 t1, h4]
    have : i < nb i := lt_of_le_of_ne (hc1.resolve_left (by rw [t1]; decide)) (Ne.symm hn1)
    simp [ht, this]
  · by_cases t2 : trivB GD0 (nb (nb i)) = true
    · exact Or.inl t2
    right
    rw [Bool.not_eq_true] at t2
    rw [hreq h2 t2, h4]
    have : i < nb (nb i) := lt_of_le_of_ne (hc2.resolve_left (by rw [t2]; decide)) (Ne.symm hn2)
    simp [ht, this]
  · by_cases t3 : trivB GD0 (nb (nb (nb i))) = true
    · exact Or.inl t3
    right
    rw [Bool.not_eq_true] at t3
    rw [hreq h3 t3, h4]
    have hne : nb (nb (nb i)) ≠ i := by
      intro e
      apply hn1
      have h4' := h4
      rw [e] at h4'
      exact h4'
    have : i < nb (nb (nb i)) := lt_of_le_of_ne (hc3.resolve_left (by rw [t3]; decide)) (Ne.symm hne)
    simp [ht, this]

noncomputable abbrev root0 : Fin nPts := ⟨0, nPts_pos hF⟩

omit hF in
theorem val_smul (g : J) (x : Fin nPts) : (g • x).val = idx nPts g x.val := by
  rw [idx_of_lt g x.isLt]

theorem stabilizer_le_Hj : MulAction.stabilizer J (root0 hF) ≤ Hj := by
  let t : Fin nPts → J := fun x => trans x.val
  have ht : ∀ x, t x • root0 hF = x := fun x => Fin.ext (by
    rw [val_smul]
    exact idx_trans hF x.isLt)
  have ht1 : t (root0 hF) = 1 := trans_zero
  have hsch : ∀ (s : J) (x : Fin nPts), (t (s • x))⁻¹ * s * t x = schr s x.val := by
    intro s x
    simp only [t, val_smul]
  have hKa := schreier_mem_of_cycle_tests Hj t (a⁻¹ : J) (d := 2) (by norm_num)
    (by rw [pow_two, a_inv_mul_self hF]) {x | (t (a⁻¹ • x))⁻¹ * a⁻¹ * t x ∈ Hj}
    (fun x hx => hx) (fun x => by
      rcases schrA_cases hF x.isLt with h | h
      · left
        show _ ∈ Hj
        rw [hsch]
        exact h
      · right
        intro k hk0 hk2
        obtain rfl : k = 1 := by omega
        show _ ∈ Hj
        rw [pow_one, hsch, val_smul]
        exact h)
  have hKb := schreier_mem_of_cycle_tests Hj t (b⁻¹ : J) (d := 4) (by norm_num)
    (by rw [inv_pow, b_pow_four hF, inv_one]) {x | (t (b⁻¹ • x))⁻¹ * b⁻¹ * t x ∈ Hj}
    (fun x hx => hx) (fun x => by
      rcases schrB_cases hF x.isLt with h | ⟨h1, h2, h3⟩
      · left
        show _ ∈ Hj
        rw [hsch]
        exact h
      · right
        intro k hk0 hk4
        show _ ∈ Hj
        rw [hsch, val_smul]
        obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
        · rw [pow_one]; exact h1
        · rw [pow_two, idx_mul]; exact h2
        · rw [pow_three, idx_mul, idx_mul]; exact h3)
  refine stabilizer_le_of_schreier_mem (root0 hF) closure_inv_ab Hj t ht ht1 fun s hs x => ?_
  rcases hs with rfl | rfl
  · exact hKa x
  · exact hKb x

theorem Hj_le_stabilizer : Hj ≤ MulAction.stabilizer J (root0 hF) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  apply Fin.ext
  rw [val_smul]
  exact idx_Hj hF hg

theorem stabilizer_eq_Hj : MulAction.stabilizer J (root0 hF) = Hj :=
  le_antisymm (stabilizer_le_Hj hF) (Hj_le_stabilizer hF)

end Facts

end CFSG.Sporadic.J4
