module

public import CFSG.Sporadic.Co2Jc.Orbits
public import Certificates.Certificate719020
public import CFSG.Sporadic.Co2Smith.GlNJH1

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open scoped commutatorElement Pointwise
open CFSG.Sporadic.Co2Jc.Data


variable (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w})
  (hb : qA 1 ∈ ⁅Qj, Qj⁆) (ha : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆)

instance : SMul ↥⁅Qj, Qj⁆ ↥O1 where
  smul g x := ⟨g.1 x.1, apply_mem_O1 (Subgroup.commutator_le_self Qj g.2) x.2⟩

instance : MulAction ↥⁅Qj, Qj⁆ ↥O1 where
  one_smul x := Subtype.ext rfl
  mul_smul g h x := Subtype.ext rfl

@[simp]
private theorem commutator_smul_coe (g : ↥⁅Qj, Qj⁆) (x : ↥O1) :
    ((g • x : ↥O1) : ↥Jc) = g.1 x.1 := rfl

private theorem simpleCheck : Native.simpleOK = true := Certificates.certificate719020

private theorem gOK : Native.gOK () = true := by
  have h := simpleCheck
  simp only [Native.simpleOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.1

private theorem perfOK : Native.perfOK () = true := by
  have h := simpleCheck
  simp only [Native.simpleOK, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

private theorem uOK : Native.uOK () = true := by
  have h := simpleCheck
  simp only [Native.simpleOK, Bool.and_eq_true] at h
  exact h.1.1.1.2

private theorem hOK : Native.hOK () = true := by
  have h := simpleCheck
  simp only [Native.simpleOK, Bool.and_eq_true] at h
  exact h.1.1.2

private theorem fixOK : Native.fixOK () = true := by
  have h := simpleCheck
  simp only [Native.simpleOK, Bool.and_eq_true] at h
  exact h.1.2

private theorem ncOK : Native.ncOK () = true := by
  have h := simpleCheck
  simp only [Native.simpleOK, Bool.and_eq_true] at h
  exact h.2


private theorem sameActBasis_spec {w w' : List Nat} (h : Native.sameActBasis w w' = true) {i : Nat}
    (hi : i < 10) : wordAct w (2 ^ i) = wordAct w' (2 ^ i) := by
  have h1 := (List.all_eq_true.1 h) i (List.mem_range.2 hi)
  simpa [Native.sameAct, beq_iff_eq] using h1

private theorem g1_ord_basis : Native.sameActBasis (g1w ++ g1w ++ g1w) [] = true := by
  have h := gOK
  simp only [Native.gOK, Bool.and_eq_true] at h
  exact h.1.1.1.1

private theorem g2_ord_basis : Native.sameActBasis (g2w ++ g2w ++ g2w ++ g2w) [] = true := by
  have h := gOK
  simp only [Native.gOK, Bool.and_eq_true] at h
  exact h.1.1.1.2

private theorem a_ord_basis : Native.sameActBasis (List.replicate 12 0) [] = true := by
  have h := gOK
  simp only [Native.gOK, Bool.and_eq_true] at h
  exact h.1.1.2

private theorem b_ord_basis : Native.sameActBasis (List.replicate 3 1) [] = true := by
  have h := gOK
  simp only [Native.gOK, Bool.and_eq_true] at h
  exact h.1.2

private theorem g1_nontrivial_basis : wordAct g1w 2 ≠ 2 := by
  have h := gOK
  simp only [Native.gOK, Bool.and_eq_true, bne_iff_ne] at h
  exact h.2

private theorem g1_pow_three_act {i : Nat} (hi : i < 10) :
    wordAct (g1w ++ g1w ++ g1w) (2 ^ i) = 2 ^ i := by
  rw [sameActBasis_spec g1_ord_basis hi]
  rfl

private theorem g2_pow_four_act {i : Nat} (hi : i < 10) :
    wordAct (g2w ++ g2w ++ g2w ++ g2w) (2 ^ i) = 2 ^ i := by
  rw [sameActBasis_spec g2_ord_basis hi]
  rfl

private theorem a_pow_twelve_act {i : Nat} (hi : i < 10) :
    wordAct (List.replicate 12 0) (2 ^ i) = 2 ^ i := by
  rw [sameActBasis_spec a_ord_basis hi]
  rfl

private theorem b_pow_three_act {i : Nat} (hi : i < 10) :
    wordAct (List.replicate 3 1) (2 ^ i) = 2 ^ i := by
  rw [sameActBasis_spec b_ord_basis hi]
  rfl


private theorem g1_ord_words : ∀ k ∈ g1w ++ g1w ++ g1w, k < 3 := by decide

private theorem qWord_g1_pow_three : qWord (g1w ++ g1w ++ g1w) = 1 := by
  apply qWord_eq_qWord (w' := []) (by decide) (by simp)
  intro i hi
  rw [g1_pow_three_act hi]
  rfl

private theorem g2_ord_words : ∀ k ∈ g2w ++ g2w ++ g2w ++ g2w, k < 3 := by decide

private theorem qWord_g2_pow_four : qWord (g2w ++ g2w ++ g2w ++ g2w) = 1 := by
  apply qWord_eq_qWord (w' := []) (by decide) (by simp)
  intro i hi
  rw [g2_pow_four_act hi]
  rfl

private theorem a_ord_words : ∀ k ∈ List.replicate 12 0, k < 3 := by decide

private theorem qWord_replicate (k n : Nat) : qWord (List.replicate n k) = (qA k) ^ n := by
  rw [qWord, List.map_replicate, List.prod_replicate]

private theorem qWord_a_pow_twelve : (qA 0) ^ 12 = 1 := by
  have h : qWord (List.replicate 12 0) = 1 := by
    apply qWord_eq_qWord (w' := []) (by decide) (by simp)
    intro i hi
    rw [a_pow_twelve_act hi]
    rfl
  rwa [qWord_replicate] at h

private theorem b_ord_words : ∀ k ∈ List.replicate 3 1, k < 3 := by decide

private theorem qWord_b_pow_three : (qA 1) ^ 3 = 1 := by
  have h : qWord (List.replicate 3 1) = 1 := by
    apply qWord_eq_qWord (w' := []) (by decide) (by simp)
    intro i hi
    rw [b_pow_three_act hi]
    rfl
  rwa [qWord_replicate] at h

private theorem g1_pow_three : qWord g1w ^ 3 = 1 := by
  have h : qWord g1w * qWord g1w * qWord g1w = 1 := by
    rw [← qWord_append, ← qWord_append]
    exact qWord_g1_pow_three
  rw [pow_three, ← mul_assoc]
  exact h

private theorem g2_pow_four : qWord g2w ^ 4 = 1 := by
  have h : qWord g2w * qWord g2w * qWord g2w * qWord g2w = 1 := by
    rw [← qWord_append, ← qWord_append, ← qWord_append]
    exact qWord_g2_pow_four
  rw [show (4:ℕ) = 3+1 by norm_num, pow_succ, pow_three, ← mul_assoc]
  exact h

private theorem inv_g1 : (qWord g1w)⁻¹ = (qWord g1w) ^ 2 := by
  have h : (qWord g1w) ^ 2 * qWord g1w = 1 := by
    have h' : (qWord g1w) ^ 2 * qWord g1w = qWord g1w ^ 3 := by
      calc (qWord g1w) ^ 2 * qWord g1w = qWord g1w ^ (2 + 1) := (pow_succ _ 2).symm
        _ = qWord g1w ^ 3 := by norm_num
    rw [h']; exact g1_pow_three
  exact (eq_inv_of_mul_eq_one_left h).symm

private theorem inv_g2 : (qWord g2w)⁻¹ = (qWord g2w) ^ 3 := by
  have h : (qWord g2w) ^ 3 * qWord g2w = 1 := by
    have h' : (qWord g2w) ^ 3 * qWord g2w = qWord g2w ^ 4 := by
      calc (qWord g2w) ^ 3 * qWord g2w = qWord g2w ^ (3 + 1) := (pow_succ _ 3).symm
        _ = qWord g2w ^ 4 := by norm_num
    rw [h']; exact g2_pow_four
  exact (eq_inv_of_mul_eq_one_left h).symm

private theorem inv_a : (qA 0)⁻¹ = (qA 0) ^ 11 := by
  have h : (qA 0) ^ 11 * qA 0 = 1 := by
    have := qWord_a_pow_twelve
    rw [show (12:ℕ) = 11+1 by norm_num, pow_succ] at this
    exact this
  exact (eq_inv_of_mul_eq_one_left h).symm

private theorem inv_b : (qA 1)⁻¹ = (qA 1) ^ 2 := by
  have h : (qA 1) ^ 2 * qA 1 = 1 := by
    have h' : (qA 1) ^ 2 * qA 1 = (qA 1) ^ 3 := by
      calc (qA 1) ^ 2 * qA 1 = (qA 1) ^ (2 + 1) := (pow_succ _ 2).symm
        _ = (qA 1) ^ 3 := by norm_num
    rw [h']; exact qWord_b_pow_three
  exact (eq_inv_of_mul_eq_one_left h).symm


private theorem qWord_dWord_append (x y : List Nat) :
    qWord (dWord (x ++ y)) = qWord (dWord x) * qWord (dWord y) := by
  simp [dWord, List.flatMap_append, qWord_append]

private theorem qWord_dWord_cons (l : Nat) (w : List Nat) :
    qWord (dWord (l :: w)) = qWord (dWord [l]) * qWord (dWord w) := by
  simpa [List.flatMap_cons] using qWord_dWord_append [l] w

private theorem qWord_dWord_single (l : Nat) (hl : l < 2) :
    qWord (dWord [l]) = if l = 0 then qWord g1w else qWord g2w := by
  interval_cases l <;> simp [dWord, g1w, g2w]

private theorem qWord_dWord_single_pow (l : Nat) (hl : l < 2) :
    qWord (dWord [l]) ^ ordD l = 1 := by
  interval_cases l
  · simpa [ordD, dWord] using g1_pow_three
  · simpa [ordD, dWord] using g2_pow_four

private theorem qWord_dWord_replicate (l n : Nat) :
    qWord (dWord (List.replicate n l)) = qWord (dWord [l]) ^ n := by
  induction n with
  | zero => simp [dWord, qWord]
  | succ n ih =>
    rw [List.replicate_succ, qWord_dWord_cons, ih, pow_succ']

private theorem pow_pred_eq_inv (a : MulAut ↥Jc) (n : Nat) (hn : 0 < n) (h : a ^ n = 1) :
    a ^ (n - 1) = a⁻¹ := by
  have h1 : a ^ (n - 1) * a = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn, h]
  exact eq_inv_of_mul_eq_one_left h1

private theorem qWord_dWord_pow_pred_inv (l : Nat) (hl : l < 2) :
    (qWord (dWord [l])) ^ (ordD l - 1) = (qWord (dWord [l]))⁻¹ :=
  pow_pred_eq_inv _ _ (by interval_cases l <;> simp [ordD]) (qWord_dWord_single_pow l hl)

private theorem qWord_dWord_single_inv (l : Nat) (hl : l < 2) :
    qWord (dWord (invD [l])) = (qWord (dWord [l]))⁻¹ := by
  have h : qWord (dWord (List.replicate (ordD l - 1) l)) =
      qWord (dWord [l]) ^ (ordD l - 1) := qWord_dWord_replicate l (ordD l - 1)
  rw [show invD [l] = List.replicate (ordD l - 1) l by simp [invD], h]
  exact qWord_dWord_pow_pred_inv l hl

private theorem qWord_dWord_inv (w : List Nat) (hw : ∀ l ∈ w, l < 2) :
    qWord (dWord (invD w)) = (qWord (dWord w))⁻¹ := by
  induction w with
  | nil => simp [invD, qWord, dWord, inv_one]
  | cons l w ih =>
    have hl : l < 2 := hw l List.mem_cons_self
    have hw' : ∀ k ∈ w, k < 2 := fun k hk => hw k (List.mem_cons_of_mem _ hk)
    calc qWord (dWord (invD (l :: w)))
        = qWord (dWord (invD w ++ List.replicate (ordD l - 1) l)) := by
          rw [show invD (l :: w) = invD w ++ List.replicate (ordD l - 1) l by
            simp [invD, List.reverse_cons, List.flatMap_append]]
      _ = qWord (dWord (invD w)) * qWord (dWord (List.replicate (ordD l - 1) l)) :=
          qWord_dWord_append _ _
      _ = (qWord (dWord w))⁻¹ * (qWord (dWord [l])) ^ (ordD l - 1) := by
          rw [ih hw', qWord_dWord_replicate]
      _ = (qWord (dWord w))⁻¹ * (qWord (dWord [l]))⁻¹ := by
          rw [qWord_dWord_pow_pred_inv l hl]
      _ = (qWord (dWord [l]) * qWord (dWord w))⁻¹ := by rw [← mul_inv_rev]
      _ = (qWord (dWord (l :: w)))⁻¹ := by rw [← qWord_dWord_cons]


private theorem qWord_dWord_commD (x y : List Nat) (hx : ∀ l ∈ x, l < 2) (hy : ∀ l ∈ y, l < 2) :
    qWord (dWord (commD x y)) = ⁅qWord (dWord x), qWord (dWord y)⁆ := by
  rw [commD, qWord_dWord_append, qWord_dWord_append, qWord_dWord_append,
    qWord_dWord_inv x hx, qWord_dWord_inv y hy, commutatorElement_def]

private theorem dWord_append (x y : List Nat) : dWord (x ++ y) = dWord x ++ dWord y := by
  simp [dWord, List.flatMap_append]

private theorem dWord_flatMap (w : List Nat) (f : Nat → List Nat) :
    dWord (w.flatMap f) = w.flatMap fun l => dWord (f l) := by
  simp only [dWord]
  rw [List.flatMap_assoc]

private theorem qWord_flatMap (w : List Nat) (f : Nat → List Nat) :
    qWord (w.flatMap f) = (w.map fun l => qWord (f l)).prod := by
  induction w with
  | nil => simp [qWord]
  | cons l w ih =>
    rw [List.flatMap_cons, qWord_append, ih, List.map_cons, List.prod_cons]


private theorem g1w_lt3 : ∀ k ∈ g1w, k < 3 := by decide

private theorem g2w_lt3 : ∀ k ∈ g2w, k < 3 := by decide

private theorem dWord_lt3 (w : List Nat) : ∀ k ∈ dWord w, k < 3 := by
  intro k hk
  simp only [dWord, List.mem_flatMap] at hk
  obtain ⟨l, _, hk⟩ := hk
  split at hk
  · exact g1w_lt3 k hk
  · exact g2w_lt3 k hk

private theorem perfW_action {j i : Nat} (hj : j < 2) (hi : i < 10) :
    wordAct (dWord (Native.perfExp j)) (2 ^ i) = wordAct (dWord [j]) (2 ^ i) := by
  have h := perfOK
  simp only [Native.perfOK, Bool.and_eq_true] at h
  have h1 := (List.all_eq_true.1 h.2) j (List.mem_range.2 hj)
  exact sameActBasis_spec h1 hi

private theorem perfW_length : perfW.length = 2 := by
  have h := perfOK
  simp only [Native.perfOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

private theorem perfX_length : perfX.length = 2 := by
  have h := perfOK
  simp only [Native.perfOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

private theorem perfW_lt2 {j : Nat} (hj : j < 2) : ∀ l ∈ perfW[j]!, l < 2 := by
  have h := perfOK
  simp only [Native.perfOK, Bool.and_eq_true] at h
  have hlen : j < perfW.length := by rw [perfW_length]; omega
  have h1 : (perfW[j]).all (fun x => x < 2) = true :=
    (List.all_eq_true.1 h.1.2) (perfW[j]) (List.getElem_mem hlen)
  rw [getElem!_pos perfW j hlen]
  simpa using List.all_eq_true.1 h1

private theorem perfX_lt2 {j : Nat} (hj : j < 2) :
    (∀ l ∈ (perfX[j]!).1, l < 2) ∧ ∀ l ∈ (perfX[j]!).2, l < 2 := by
  have h := perfOK
  simp only [Native.perfOK, Bool.and_eq_true] at h
  have hlen : j < perfX.length := by rw [perfX_length]; omega
  have hp : ((perfX[j]).1.all (fun x => x < 2) &&
      (perfX[j]).2.all (fun x => x < 2)) = true :=
    (List.all_eq_true.1 h.1.1.2) (perfX[j]) (List.getElem_mem hlen)
  simp only [Bool.and_eq_true] at hp
  rw [getElem!_pos perfX j hlen]
  exact ⟨by simpa using List.all_eq_true.1 hp.1, by simpa using List.all_eq_true.1 hp.2⟩

private theorem fix_b (m : Nat) (h : m = 1) : wordAct [1] m = 1 := by
  subst h
  have h' := fixOK
  simp only [Native.fixOK, Bool.and_eq_true, beq_iff_eq] at h'
  exact h'.1

private theorem fix_a2 (m : Nat) (h : m = 1) : wordAct [0, 0] m = 1 := by
  subst h
  have h' := fixOK
  simp only [Native.fixOK, Bool.and_eq_true, beq_iff_eq] at h'
  exact h'.2



private noncomputable def g1G : ↥⁅Qj, Qj⁆ :=
  ⟨qWord g1w, by rw [hD]; exact Subgroup.subset_closure (by simp)⟩

private noncomputable def g2G : ↥⁅Qj, Qj⁆ :=
  ⟨qWord g2w, by rw [hD]; exact Subgroup.subset_closure (by simp)⟩

private noncomputable def bG : ↥⁅Qj, Qj⁆ := ⟨qA 1, hb⟩

private noncomputable def a2G : ↥⁅Qj, Qj⁆ := ⟨qA 0 * qA 0, ha⟩

private noncomputable def HH : Subgroup ↥⁅Qj, Qj⁆ := Subgroup.closure {bG hb, a2G ha}


private theorem qWord_dWord_mem_closure {w : List Nat} (hw : ∀ l ∈ w, l < 2) :
    qWord (dWord w) ∈ Subgroup.closure ({qWord g1w, qWord g2w} : Set (MulAut ↥Jc)) := by
  induction w with
  | nil => simpa [dWord, qWord] using (Subgroup.closure _).one_mem
  | cons l w ih =>
    have hl : l < 2 := hw l List.mem_cons_self
    have hw' : ∀ k ∈ w, k < 2 := fun k hk => hw k (List.mem_cons_of_mem _ hk)
    rw [qWord_dWord_cons, qWord_dWord_single l hl]
    refine (Subgroup.closure _).mul_mem ?_ (ih hw')
    by_cases h : l = 0
    · rw [if_pos h]
      exact Subgroup.subset_closure (by simp)
    · rw [if_neg h]
      exact Subgroup.subset_closure (by simp)

private theorem c0G_word : qWord (dWord (Native.cWord 0)) =
    ⁅qWord (dWord [0]), qWord (dWord [1])⁆ := by
  have h : Native.cWord 0 = commD [0] [1] := by
    simp [Native.cWord, perfX]
  rw [h]
  exact qWord_dWord_commD [0] [1] (by decide) (by decide)

private theorem c1G_word : qWord (dWord (Native.cWord 1)) =
    ⁅qWord (dWord [0, 1]), qWord (dWord [1, 0])⁆ := by
  have h : Native.cWord 1 = commD [0, 1] [1, 0] := by
    simp [Native.cWord, perfX]
  rw [h]
  exact qWord_dWord_commD [0, 1] [1, 0] (by decide) (by decide)

private noncomputable def c0G : ↥⁅Qj, Qj⁆ :=
  ⟨qWord (dWord (Native.cWord 0)), by
    rw [Subgroup.commutator_def, c0G_word]
    exact Subgroup.subset_closure
      ⟨qWord (dWord [0]), qWord_mem (by decide), qWord (dWord [1]), qWord_mem (by decide), rfl⟩⟩

private noncomputable def c1G : ↥⁅Qj, Qj⁆ :=
  ⟨qWord (dWord (Native.cWord 1)), by
    rw [Subgroup.commutator_def, c1G_word]
    exact Subgroup.subset_closure
      ⟨qWord (dWord [0, 1]), qWord_mem (by decide),
        qWord (dWord [1, 0]), qWord_mem (by decide), rfl⟩⟩

private noncomputable def cG (l : Nat) : ↥⁅Qj, Qj⁆ := if l = 0 then c0G else c1G

private theorem cG_val_zero : (cG 0 : MulAut ↥Jc) = qWord (dWord (Native.cWord 0)) := by
  simp [cG, c0G]

private theorem cG_val_one : (cG 1 : MulAut ↥Jc) = qWord (dWord (Native.cWord 1)) := by
  simp [cG, c1G]

private theorem c0G_val : (c0G : MulAut ↥Jc) = ⁅qWord (dWord [0]), qWord (dWord [1])⁆ := by
  change qWord (dWord (Native.cWord 0)) = _
  exact c0G_word

private theorem c1G_val : (c1G : MulAut ↥Jc) = ⁅qWord (dWord [0, 1]), qWord (dWord [1, 0])⁆ := by
  change qWord (dWord (Native.cWord 1)) = _
  exact c1G_word


private theorem cG_val_of_lt {l : Nat} (hl : l < 2) :
    (cG l : MulAut ↥Jc) = qWord (dWord (Native.cWord l)) := by
  interval_cases l
  · exact cG_val_zero
  · exact cG_val_one

private noncomputable def evalC (w : List Nat) : ↥⁅Qj, Qj⁆ := (w.map cG).prod

private theorem evalC_val (w : List Nat) (hw : ∀ l ∈ w, l < 2) :
    (evalC w : MulAut ↥Jc) = qWord (dWord (w.flatMap Native.cWord)) := by
  induction w with
  | nil => simp [evalC, dWord, qWord]
  | cons l w ih =>
    have hl : l < 2 := hw l List.mem_cons_self
    have hw' : ∀ k ∈ w, k < 2 := fun k hk => hw k (List.mem_cons_of_mem _ hk)
    simp only [evalC, List.map_cons, List.prod_cons]
    change (cG l : MulAut ↥Jc) * (evalC w : MulAut ↥Jc) =
      qWord (dWord ((l :: w).flatMap Native.cWord))
    rw [cG_val_of_lt hl, ih hw']
    rw [List.flatMap_cons, dWord_append, qWord_append]

private theorem c0G_mem (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) :
    c0G ∈ ⁅(⊤ : Subgroup ↥⁅Qj, Qj⁆), (⊤ : Subgroup ↥⁅Qj, Qj⁆)⁆ := by
  let A : ↥⁅Qj, Qj⁆ :=
    ⟨qWord (dWord [0]), by rw [hD]; exact qWord_dWord_mem_closure (by decide)⟩
  let B : ↥⁅Qj, Qj⁆ :=
    ⟨qWord (dWord [1]), by rw [hD]; exact qWord_dWord_mem_closure (by decide)⟩
  have hc : c0G = ⁅A, B⁆ := by
    refine Subtype.ext ?_
    change (c0G : MulAut ↥Jc) = ((⁅A, B⁆ : ↥⁅Qj, Qj⁆) : MulAut ↥Jc)
    rw [c0G_val]
    rfl
  change c0G ∈ Subgroup.closure {g : ↥⁅Qj, Qj⁆ |
    ∃ x ∈ (⊤ : Subgroup ↥⁅Qj, Qj⁆), ∃ y ∈ (⊤ : Subgroup ↥⁅Qj, Qj⁆), ⁅x, y⁆ = g}
  rw [hc]
  exact Subgroup.subset_closure ⟨A, trivial, B, trivial, rfl⟩

private theorem c1G_mem (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) :
    c1G ∈ ⁅(⊤ : Subgroup ↥⁅Qj, Qj⁆), (⊤ : Subgroup ↥⁅Qj, Qj⁆)⁆ := by
  let A : ↥⁅Qj, Qj⁆ :=
    ⟨qWord (dWord [0, 1]), by rw [hD]; exact qWord_dWord_mem_closure (by decide)⟩
  let B : ↥⁅Qj, Qj⁆ :=
    ⟨qWord (dWord [1, 0]), by rw [hD]; exact qWord_dWord_mem_closure (by decide)⟩
  have hc : c1G = ⁅A, B⁆ := by
    refine Subtype.ext ?_
    change (c1G : MulAut ↥Jc) = ((⁅A, B⁆ : ↥⁅Qj, Qj⁆) : MulAut ↥Jc)
    rw [c1G_val]
    rfl
  change c1G ∈ Subgroup.closure {g : ↥⁅Qj, Qj⁆ |
    ∃ x ∈ (⊤ : Subgroup ↥⁅Qj, Qj⁆), ∃ y ∈ (⊤ : Subgroup ↥⁅Qj, Qj⁆), ⁅x, y⁆ = g}
  rw [hc]
  exact Subgroup.subset_closure ⟨A, trivial, B, trivial, rfl⟩


private theorem qWord_perfExp_zero : qWord (dWord (Native.perfExp 0)) = qWord g1w := by
  have h : qWord (dWord (Native.perfExp 0)) = qWord (dWord [0]) := by
    apply qWord_eq_qWord (dWord_lt3 _) (dWord_lt3 _)
    intro i hi
    rw [perfW_action (by norm_num) hi]
  rw [h, qWord_dWord_single 0 (by norm_num)]
  simp

private theorem qWord_perfExp_one : qWord (dWord (Native.perfExp 1)) = qWord g2w := by
  have h : qWord (dWord (Native.perfExp 1)) = qWord (dWord [1]) := by
    apply qWord_eq_qWord (dWord_lt3 _) (dWord_lt3 _)
    intro i hi
    rw [perfW_action (by norm_num) hi]
  rw [h, qWord_dWord_single 1 (by norm_num)]
  simp

private theorem evalC_perfW0 : evalC (perfW[0]!) = g1G hD := by
  refine Subtype.ext ?_
  change (evalC (perfW[0]!) : MulAut ↥Jc) = qWord g1w
  rw [evalC_val _ (perfW_lt2 (by norm_num))]
  simpa [Native.perfExp] using qWord_perfExp_zero

private theorem evalC_perfW1 : evalC (perfW[1]!) = g2G hD := by
  refine Subtype.ext ?_
  change (evalC (perfW[1]!) : MulAut ↥Jc) = qWord g2w
  rw [evalC_val _ (perfW_lt2 (by norm_num))]
  simpa [Native.perfExp] using qWord_perfExp_one

private theorem closure_g1g2_top :
    Subgroup.closure ({g1G hD, g2G hD} : Set ↥⁅Qj, Qj⁆) = ⊤ := by
  refine le_antisymm le_top ?_
  intro g _
  have hg : (g : MulAut ↥Jc) ∈ Subgroup.closure ({qWord g1w, qWord g2w} : Set (MulAut ↥Jc)) :=
    hD ▸ g.2
  let K : Subgroup ↥⁅Qj, Qj⁆ := Subgroup.closure {g1G hD, g2G hD}
  change g ∈ K
  have key : ∀ (x : MulAut ↥Jc) (hx : x ∈ Subgroup.closure ({qWord g1w, qWord g2w} :
      Set (MulAut ↥Jc))), (⟨x, hD.symm ▸ hx⟩ : ↥⁅Qj, Qj⁆) ∈ K := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Subgroup.subset_closure (by simp [g1G])
      · exact Subgroup.subset_closure (by simp [g2G])
    | one => exact K.one_mem
    | mul y z hy hz ihy ihz =>
      have h : (⟨y * z, hD.symm ▸ Subgroup.mul_mem (Subgroup.closure _) hy hz⟩ : ↥⁅Qj, Qj⁆) =
          (⟨y, hD.symm ▸ hy⟩ : ↥⁅Qj, Qj⁆) * ⟨z, hD.symm ▸ hz⟩ := Subtype.ext rfl
      rw [h]
      exact K.mul_mem ihy ihz
    | inv y hy ihy =>
      have h : (⟨y⁻¹, hD.symm ▸ Subgroup.inv_mem (Subgroup.closure _) hy⟩ : ↥⁅Qj, Qj⁆) =
          (⟨y, hD.symm ▸ hy⟩ : ↥⁅Qj, Qj⁆)⁻¹ := Subtype.ext rfl
      rw [h]
      exact K.inv_mem ihy
  exact key (g : MulAut ↥Jc) hg





private theorem hOrb60_length : hOrb60.length = 60 := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb60_valid :
    (hOrb60.all fun m => decide (m < 1024) && Native.glNJOm.contains m) = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb60_closed :
    (hOrb60.all fun m =>
      hOrb60.contains (wordAct [1] m) && hOrb60.contains (wordAct [0, 0] m)) = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb60_actions :
    ((List.range 60).all fun k =>
      wordAct (hExpand (hWords60[k]!)) hRep60 == hOrb60[k]!) = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb60_nodup : hOrb60.Nodup := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto


private theorem hOrb16_length : hOrb16.length = 16 := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hWords60_length : hWords60.length = 60 := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hWords16_length : hWords16.length = 16 := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb16_nodup : hOrb16.Nodup := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb16_valid :
    (hOrb16.all fun m => decide (m < 1024) && Native.glNJOm.contains m) = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb60_disj :
    (hOrb60.all fun m => !hOrb16.contains m && m != 1) = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb16_ne_one : (hOrb16.all fun m => m != 1) = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb16_closed :
    (hOrb16.all fun m =>
      hOrb16.contains (wordAct [1] m) && hOrb16.contains (wordAct [0, 0] m)) = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb16_actions :
    ((List.range 16).all fun k =>
      wordAct (hExpand (hWords16[k]!)) hRep16 == hOrb16[k]!) = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb60_rep : hOrb60[0]! = hRep60 := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb16_rep : hOrb16.contains hRep16 = true := by
  have h := hOK
  simp only [Native.hOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  tauto

private theorem hOrb60_lt {m : Nat} (hm : m ∈ hOrb60) : m < 1024 := by
  have h := (List.all_eq_true.1 hOrb60_valid) m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

private theorem hOrb60_mem_O {m : Nat} (hm : m ∈ hOrb60) : m ∈ Native.glNJOm := by
  have h := (List.all_eq_true.1 hOrb60_valid) m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact (List.contains_iff_mem).1 h.2

private theorem hOrb16_lt {m : Nat} (hm : m ∈ hOrb16) : m < 1024 := by
  have h := (List.all_eq_true.1 hOrb16_valid) m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

private theorem hOrb16_mem_O {m : Nat} (hm : m ∈ hOrb16) : m ∈ Native.glNJOm := by
  have h := (List.all_eq_true.1 hOrb16_valid) m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact (List.contains_iff_mem).1 h.2

private theorem hOrb60_not_mem16 {m : Nat} (hm : m ∈ hOrb60) : m ∉ hOrb16 := by
  have h := (List.all_eq_true.1 hOrb60_disj) m hm
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  intro h'
  have htrue : hOrb16.contains m = true := (List.contains_iff_mem).2 h'
  rw [htrue] at h
  exact Bool.noConfusion h.1

private theorem hOrb60_ne_one {m : Nat} (hm : m ∈ hOrb60) : m ≠ 1 := by
  have h := (List.all_eq_true.1 hOrb60_disj) m hm
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  exact h.2

private theorem hOrb16_ne_one' {m : Nat} (hm : m ∈ hOrb16) : m ≠ 1 := by
  have h := (List.all_eq_true.1 hOrb16_ne_one) m hm
  simpa [bne_iff_ne] using h

private theorem hOrb60_closed_b {m : Nat} (hm : m ∈ hOrb60) : wordAct [1] m ∈ hOrb60 := by
  have h := (List.all_eq_true.1 hOrb60_closed) m hm
  simp only [Bool.and_eq_true] at h
  exact (List.contains_iff_mem).1 h.1

private theorem hOrb60_closed_a2 {m : Nat} (hm : m ∈ hOrb60) : wordAct [0, 0] m ∈ hOrb60 := by
  have h := (List.all_eq_true.1 hOrb60_closed) m hm
  simp only [Bool.and_eq_true] at h
  exact (List.contains_iff_mem).1 h.2

private theorem hOrb16_closed_b {m : Nat} (hm : m ∈ hOrb16) : wordAct [1] m ∈ hOrb16 := by
  have h := (List.all_eq_true.1 hOrb16_closed) m hm
  simp only [Bool.and_eq_true] at h
  exact (List.contains_iff_mem).1 h.1

private theorem hOrb16_closed_a2 {m : Nat} (hm : m ∈ hOrb16) : wordAct [0, 0] m ∈ hOrb16 := by
  have h := (List.all_eq_true.1 hOrb16_closed) m hm
  simp only [Bool.and_eq_true] at h
  exact (List.contains_iff_mem).1 h.2

private theorem hOrb60_word {k : Nat} (hk : k < 60) :
    wordAct (hExpand (hWords60[k]!)) hRep60 = hOrb60[k]! := by
  have h := (List.all_eq_true.1 hOrb60_actions) k (List.mem_range.2 hk)
  simpa [beq_iff_eq] using h

private theorem hOrb16_word {k : Nat} (hk : k < 16) :
    wordAct (hExpand (hWords16[k]!)) hRep16 = hOrb16[k]! := by
  have h := (List.all_eq_true.1 hOrb16_actions) k (List.mem_range.2 hk)
  simpa [beq_iff_eq] using h


private noncomputable def point60 (k : Fin 60) : ↥O1 :=
  ⟨jcA (hOrb60.get ⟨k.val, by rw [hOrb60_length]; exact k.2⟩),
    (jcA_mem_O1_iff (hOrb60_lt (List.get_mem _ _))).2
      (hOrb60_mem_O (List.get_mem _ _))⟩

private noncomputable def point16 (k : Fin 16) : ↥O1 :=
  ⟨jcA (hOrb16.get ⟨k.val, by rw [hOrb16_length]; exact k.2⟩),
    (jcA_mem_O1_iff (hOrb16_lt (List.get_mem _ _))).2
      (hOrb16_mem_O (List.get_mem _ _))⟩

private noncomputable def Oa : Set ↥O1 := {⟨tA, tA_mem_O1⟩}

private theorem point60_injective : Function.Injective point60 := by
  intro a b h
  apply Fin.ext
  have hval : (point60 a : ↥Jc) = (point60 b : ↥Jc) := congrArg Subtype.val h
  have hcoords : hOrb60.get ⟨a.val, by rw [hOrb60_length]; exact a.2⟩ =
      hOrb60.get ⟨b.val, by rw [hOrb60_length]; exact b.2⟩ :=
    (jcA_inj (hOrb60_lt (List.get_mem _ _)) (hOrb60_lt (List.get_mem _ _))).1 hval
  exact congrArg Fin.val ((List.Nodup.get_inj_iff hOrb60_nodup).1 hcoords)

private theorem point16_injective : Function.Injective point16 := by
  intro a b h
  apply Fin.ext
  have hval : (point16 a : ↥Jc) = (point16 b : ↥Jc) := congrArg Subtype.val h
  have hcoords : hOrb16.get ⟨a.val, by rw [hOrb16_length]; exact a.2⟩ =
      hOrb16.get ⟨b.val, by rw [hOrb16_length]; exact b.2⟩ :=
    (jcA_inj (hOrb16_lt (List.get_mem _ _)) (hOrb16_lt (List.get_mem _ _))).1 hval
  exact congrArg Fin.val ((List.Nodup.get_inj_iff hOrb16_nodup).1 hcoords)

private theorem ncard_O60 : (Set.range point60).ncard = 60 := by
  rw [Set.ncard_range_of_injective point60_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

private theorem ncard_O16 : (Set.range point16).ncard = 16 := by
  rw [Set.ncard_range_of_injective point16_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

private theorem ncard_Oa : Oa.ncard = 1 := by
  rw [Oa, Set.ncard_singleton]

private theorem disjoint_O60_O16 : Disjoint (Set.range point60) (Set.range point16) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have hval : (point16 b : ↥Jc) = (point60 a : ↥Jc) := congrArg Subtype.val hb
  have hmem60 : hOrb60.get ⟨a.val, by rw [hOrb60_length]; exact a.2⟩ ∈ hOrb60 :=
    List.get_mem _ _
  have hmem16 : hOrb16.get ⟨b.val, by rw [hOrb16_length]; exact b.2⟩ ∈ hOrb16 :=
    List.get_mem _ _
  have hcoord : hOrb16.get ⟨b.val, by rw [hOrb16_length]; exact b.2⟩ =
      hOrb60.get ⟨a.val, by rw [hOrb60_length]; exact a.2⟩ :=
    (jcA_inj (hOrb16_lt hmem16) (hOrb60_lt hmem60)).1 hval
  exact hOrb60_not_mem16 hmem60 (hcoord ▸ hmem16)

private theorem disjoint_O60_Oa : Disjoint (Set.range point60) Oa := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ha
  have hmem : hOrb60.get ⟨a.val, by rw [hOrb60_length]; exact a.2⟩ ∈ hOrb60 :=
    List.get_mem _ _
  have hval : jcA (hOrb60.get ⟨a.val, by rw [hOrb60_length]; exact a.2⟩) = jcA 1 := by
    simpa [Oa, tA, point60] using congrArg Subtype.val ha
  have hcoord : hOrb60.get ⟨a.val, by rw [hOrb60_length]; exact a.2⟩ = 1 :=
    (jcA_inj (hOrb60_lt hmem) (by norm_num)).1 hval
  exact hOrb60_ne_one hmem hcoord

private theorem disjoint_O16_Oa : Disjoint (Set.range point16) Oa := by
  rw [Set.disjoint_left]
  rintro x ⟨b, rfl⟩ ha
  have hmem : hOrb16.get ⟨b.val, by rw [hOrb16_length]; exact b.2⟩ ∈ hOrb16 :=
    List.get_mem _ _
  have hval : jcA (hOrb16.get ⟨b.val, by rw [hOrb16_length]; exact b.2⟩) = jcA 1 := by
    simpa [Oa, tA, point16] using congrArg Subtype.val ha
  have hcoord : hOrb16.get ⟨b.val, by rw [hOrb16_length]; exact b.2⟩ = 1 :=
    (jcA_inj (hOrb16_lt hmem) (by norm_num)).1 hval
  exact hOrb16_ne_one' hmem hcoord

private theorem ncard_union_orbs :
    (Set.range point60 ∪ Set.range point16 ∪ Oa).ncard = 77 := by
  have hd : Disjoint (Set.range point60 ∪ Set.range point16) Oa := by
    rw [Set.disjoint_union_left]
    exact ⟨disjoint_O60_Oa, disjoint_O16_Oa⟩
  rw [Set.ncard_union_eq hd, Set.ncard_union_eq disjoint_O60_O16,
    ncard_O60, ncard_O16, ncard_Oa]

private theorem union_orbs_eq_univ :
    Set.range point60 ∪ Set.range point16 ∪ Oa = Set.univ := by
  refine Set.eq_of_subset_of_ncard_le (s := Set.range point60 ∪ Set.range point16 ∪ Oa)
    (t := Set.univ) (by intro x _; exact Set.mem_univ x) ?_
  rw [Set.ncard_univ, Nat.card_coe_set_eq, ncard_union_orbs, ncard_O1]


private noncomputable def hElt (w : List Nat) : ↥⁅Qj, Qj⁆ :=
  (w.map fun l => if l = 0 then bG hb else a2G ha).prod

private theorem hExpand_lt3 (w : List Nat) : ∀ k ∈ hExpand w, k < 3 := by
  intro k hk
  simp only [hExpand, List.mem_flatMap] at hk
  obtain ⟨l, _, hk⟩ := hk
  split at hk <;> simp_all

private theorem hElt_val (w : List Nat) : (hElt hb ha w : MulAut ↥Jc) = qWord (hExpand w) := by
  induction w with
  | nil => simp [hElt, hExpand, qWord]
  | cons l w ih =>
    simp only [hElt, List.map_cons, List.prod_cons, hExpand, List.flatMap_cons]
    change ((if l = 0 then bG hb else a2G ha : ↥⁅Qj, Qj⁆) : MulAut ↥Jc) *
        (hElt hb ha w : MulAut ↥Jc) =
      qWord ((if l = 0 then [1] else [0, 0]) ++ hExpand w)
    rw [ih, qWord_append]
    congr 1
    by_cases hl : l = 0
    · subst hl
      simp [bG, qWord_cons, qWord_nil]
    · simp [hl, a2G, qWord_cons, qWord_nil, mul_assoc]

private theorem hElt_smul_val (w : List Nat) {m : Nat} (hm : m < 1024) (hO : m ∈ Native.glNJOm) :
    (((hElt hb ha w) • (⟨jcA m, (jcA_mem_O1_iff hm).2 hO⟩ : ↥O1) : ↥O1) : ↥Jc) =
      jcA (wordAct (hExpand w) m) := by
  change (hElt hb ha w : MulAut ↥Jc) (jcA m) = jcA (wordAct (hExpand w) m)
  rw [hElt_val hb ha w, qWord_jcA (hExpand_lt3 w)]

private theorem hElt_mem (w : List Nat) : hElt hb ha w ∈ HH hb ha := by
  rw [HH]
  exact Subgroup.list_prod_mem _ (by
    intro x hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    by_cases hl : l = 0
    · rw [if_pos hl]
      exact Subgroup.subset_closure (by simp)
    · rw [if_neg hl]
      exact Subgroup.subset_closure (by simp))


private theorem hRep60_lt : hRep60 < 1024 := by
  rw [← hOrb60_rep]
  exact hOrb60_lt (by
    rw [getElem!_pos hOrb60 0 (by rw [hOrb60_length]; norm_num)]
    exact List.getElem_mem (by rw [hOrb60_length]; norm_num))

private theorem hRep60_mem_O : hRep60 ∈ Native.glNJOm := by
  rw [← hOrb60_rep]
  exact hOrb60_mem_O (by
    rw [getElem!_pos hOrb60 0 (by rw [hOrb60_length]; norm_num)]
    exact List.getElem_mem (by rw [hOrb60_length]; norm_num))

private theorem hRep16_lt : hRep16 < 1024 :=
  hOrb16_lt ((List.contains_iff_mem).1 hOrb16_rep)

private theorem hRep16_mem_O : hRep16 ∈ Native.glNJOm :=
  hOrb16_mem_O ((List.contains_iff_mem).1 hOrb16_rep)

private noncomputable def rep60 : ↥O1 :=
  ⟨jcA hRep60, (jcA_mem_O1_iff hRep60_lt).2 hRep60_mem_O⟩

private noncomputable def rep16 : ↥O1 :=
  ⟨jcA hRep16, (jcA_mem_O1_iff hRep16_lt).2 hRep16_mem_O⟩

private theorem hElt_smul_rep60 {w : List Nat} {k : Nat} (hk : k < 60)
    (h : wordAct (hExpand w) hRep60 = hOrb60[k]!) :
    hElt hb ha w • rep60 = point60 ⟨k, hk⟩ := by
  apply Subtype.ext
  simp only [rep60]
  change (((hElt hb ha w) •
    (⟨jcA hRep60, (jcA_mem_O1_iff hRep60_lt).2 hRep60_mem_O⟩ : ↥O1) : ↥O1) : ↥Jc) =
      (point60 ⟨k, hk⟩ : ↥Jc)
  rw [hElt_smul_val hb ha w hRep60_lt hRep60_mem_O, h,
    getElem!_pos hOrb60 k (by rw [hOrb60_length]; exact hk)]
  rfl

private theorem hElt_smul_rep16 {w : List Nat} {k : Nat} (hk : k < 16)
    (h : wordAct (hExpand w) hRep16 = hOrb16[k]!) :
    hElt hb ha w • rep16 = point16 ⟨k, hk⟩ := by
  apply Subtype.ext
  simp only [rep16]
  change (((hElt hb ha w) •
    (⟨jcA hRep16, (jcA_mem_O1_iff hRep16_lt).2 hRep16_mem_O⟩ : ↥O1) : ↥O1) : ↥Jc) =
      (point16 ⟨k, hk⟩ : ↥Jc)
  rw [hElt_smul_val hb ha w hRep16_lt hRep16_mem_O, h,
    getElem!_pos hOrb16 k (by rw [hOrb16_length]; exact hk)]
  rfl

private theorem bG_smul_alpha : bG hb • (⟨tA, tA_mem_O1⟩ : ↥O1) = ⟨tA, tA_mem_O1⟩ := by
  apply Subtype.ext
  change qA 1 tA = tA
  have hq : qA 1 = qWord [1] := by rw [qWord_cons, qWord_nil, mul_one]
  rw [hq]
  change qWord [1] (jcA 1) = jcA 1
  rw [qWord_jcA (by decide), fix_b 1 rfl]

private theorem a2G_smul_alpha : a2G ha • (⟨tA, tA_mem_O1⟩ : ↥O1) = ⟨tA, tA_mem_O1⟩ := by
  apply Subtype.ext
  change (qA 0 * qA 0) tA = tA
  have hq : qA 0 * qA 0 = qWord [0, 0] := by
    rw [qWord_cons, qWord_cons, qWord_nil]
    simp [mul_assoc]
  rw [hq]
  change qWord [0, 0] (jcA 1) = jcA 1
  rw [qWord_jcA (by decide), fix_a2 1 rfl]

private theorem HH_le_stabilizer :
    HH hb ha ≤ MulAction.stabilizer ↥⁅Qj, Qj⁆ (⟨tA, tA_mem_O1⟩ : ↥O1) := by
  rw [HH, Subgroup.closure_le]
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact (MulAction.mem_stabilizer_iff).2 (bG_smul_alpha hb)
  · exact (MulAction.mem_stabilizer_iff).2 (a2G_smul_alpha ha)

private theorem block_invariant {B : Set ↥O1} (hB : MulAction.IsBlock ↥⁅Qj, Qj⁆ B)
    (hα : (⟨tA, tA_mem_O1⟩ : ↥O1) ∈ B) :
    ∀ h ∈ HH hb ha, h • B ⊆ B := by
  intro h hh
  have hstab : h ∈ MulAction.stabilizer ↥⁅Qj, Qj⁆ B :=
    (hB.stabilizer_le hα) (HH_le_stabilizer hb ha hh)
  rw [MulAction.mem_stabilizer_iff] at hstab
  rw [hstab]


private theorem O60_subset_of_block
    (hb : qA 1 ∈ ⁅Qj, Qj⁆) (ha : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆)
    {B : Set ↥O1} (hB : MulAction.IsBlock ↥⁅Qj, Qj⁆ B)
    (hα : (⟨tA, tA_mem_O1⟩ : ↥O1) ∈ B) {y : ↥O1} (hyB : y ∈ B)
    (hyO : y ∈ Set.range point60) : Set.range point60 ⊆ B := by
  obtain ⟨k, rfl⟩ := hyO
  let w := hWords60[k.val]!
  have hw : wordAct (hExpand w) hRep60 = hOrb60[k.val]! := hOrb60_word k.2
  have hact : hElt hb ha w • rep60 = point60 k := by
    simpa using hElt_smul_rep60 hb ha k.2 hw
  have hrep : rep60 ∈ B := by
    have h1 := (block_invariant hb ha hB hα ((hElt hb ha w)⁻¹)
      (Subgroup.inv_mem (HH hb ha) (hElt_mem hb ha w))) (Set.smul_mem_smul_set hyB)
    rw [← hact, inv_smul_smul] at h1
    exact h1
  rintro x ⟨j, rfl⟩
  have hwj : wordAct (hExpand (hWords60[j.val]!)) hRep60 = hOrb60[j.val]! :=
    hOrb60_word j.2
  have hactj : hElt hb ha (hWords60[j.val]!) • rep60 = point60 j := by
    simpa using hElt_smul_rep60 hb ha j.2 hwj
  have h1 := (block_invariant hb ha hB hα (hElt hb ha (hWords60[j.val]!))
    (hElt_mem hb ha (hWords60[j.val]!))) (Set.smul_mem_smul_set hrep)
  rwa [hactj] at h1

private theorem O16_subset_of_block
    (hb : qA 1 ∈ ⁅Qj, Qj⁆) (ha : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆)
    {B : Set ↥O1} (hB : MulAction.IsBlock ↥⁅Qj, Qj⁆ B)
    (hα : (⟨tA, tA_mem_O1⟩ : ↥O1) ∈ B) {y : ↥O1} (hyB : y ∈ B)
    (hyO : y ∈ Set.range point16) : Set.range point16 ⊆ B := by
  obtain ⟨k, rfl⟩ := hyO
  let w := hWords16[k.val]!
  have hw : wordAct (hExpand w) hRep16 = hOrb16[k.val]! := hOrb16_word k.2
  have hact : hElt hb ha w • rep16 = point16 k := by
    simpa using hElt_smul_rep16 hb ha k.2 hw
  have hrep : rep16 ∈ B := by
    have h1 := (block_invariant hb ha hB hα ((hElt hb ha w)⁻¹)
      (Subgroup.inv_mem (HH hb ha) (hElt_mem hb ha w))) (Set.smul_mem_smul_set hyB)
    rw [← hact, inv_smul_smul] at h1
    exact h1
  rintro x ⟨j, rfl⟩
  have hwj : wordAct (hExpand (hWords16[j.val]!)) hRep16 = hOrb16[j.val]! :=
    hOrb16_word j.2
  have hactj : hElt hb ha (hWords16[j.val]!) • rep16 = point16 j := by
    simpa using hElt_smul_rep16 hb ha j.2 hwj
  have h1 := (block_invariant hb ha hB hα (hElt hb ha (hWords16[j.val]!))
    (hElt_mem hb ha (hWords16[j.val]!))) (Set.smul_mem_smul_set hrep)
  rwa [hactj] at h1

private theorem ncard_union_O60_Oa : (Set.range point60 ∪ Oa).ncard = 61 := by
  rw [Set.ncard_union_eq disjoint_O60_Oa, ncard_O60, ncard_Oa]

private theorem ncard_union_O16_Oa : (Set.range point16 ∪ Oa).ncard = 17 := by
  rw [Set.ncard_union_eq disjoint_O16_Oa, ncard_O16, ncard_Oa]



private theorem uD_length : uD.length = 4 := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1.1

private theorem uD_lt2 : ∀ l ∈ uD, ∀ k ∈ l, k < 2 := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  intro l hl k hk
  have hb : (uD.all fun w => w.all fun x => decide (x < 2)) = true := h.1.1.1.1.1.1.1.2
  have := (List.all_eq_true.1 hb) l hl
  simpa using (List.all_eq_true.1 this) k hk

private theorem u_pairOK :
    ((List.range 4).all fun i => (List.range 4).all fun j =>
      Native.sameActBasis (dWord (uD[i]! ++ uD[j]!)) (dWord (uD[j]! ++ uD[i]!))) = true := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

private theorem u_conjOK :
    ((List.range 4).all fun i =>
      Native.sameActBasis (dWord (uD[i]! ++ uD[i]!)) [] &&
      wordAct (dWord uD[i]!) 1 == 1 &&
      Native.sameActBasis ([0] ++ dWord uD[i]! ++ List.replicate 11 0)
        (dWord (Native.uProdWord uConjA[i]!)) &&
      Native.sameActBasis (List.replicate 11 0 ++ dWord uD[i]! ++ [0])
        (dWord (Native.uProdWord uConjAinv[i]!)) &&
      Native.sameActBasis ([1] ++ dWord uD[i]! ++ [1, 1])
        (dWord (Native.uProdWord uConjB[i]!)) &&
      Native.sameActBasis ([1, 1] ++ dWord uD[i]! ++ [1])
        (dWord (Native.uProdWord uConjBinv[i]!))) = true := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem u_pair_act {i j : Nat} (hi : i < 4) (hj : j < 4) {k : Nat} (hk : k < 10) :
    wordAct (dWord (uD[i]! ++ uD[j]!)) (2 ^ k) =
      wordAct (dWord (uD[j]! ++ uD[i]!)) (2 ^ k) := by
  have h := (List.all_eq_true.1 u_pairOK) i (List.mem_range.2 hi)
  have h' := (List.all_eq_true.1 h) j (List.mem_range.2 hj)
  exact sameActBasis_spec h' hk

private theorem u_conj_parts {i : Nat} (hi : i < 4) :
    Native.sameActBasis (dWord (uD[i]! ++ uD[i]!)) [] = true ∧
      wordAct (dWord uD[i]!) 1 = 1 ∧
      Native.sameActBasis ([0] ++ dWord uD[i]! ++ List.replicate 11 0)
        (dWord (Native.uProdWord uConjA[i]!)) = true ∧
      Native.sameActBasis (List.replicate 11 0 ++ dWord uD[i]! ++ [0])
        (dWord (Native.uProdWord uConjAinv[i]!)) = true ∧
      Native.sameActBasis ([1] ++ dWord uD[i]! ++ [1, 1])
        (dWord (Native.uProdWord uConjB[i]!)) = true ∧
      Native.sameActBasis ([1, 1] ++ dWord uD[i]! ++ [1])
        (dWord (Native.uProdWord uConjBinv[i]!)) = true := by
  have h := (List.all_eq_true.1 u_conjOK) i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto


private noncomputable def uG (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) (i : Fin 4) :
    ↥⁅Qj, Qj⁆ :=
  ⟨qWord (dWord (uD[i.val]!)), by
    rw [hD]
    refine qWord_dWord_mem_closure ?_
    intro k hk
    exact uD_lt2 (uD[i.val]!) (by
      rw [getElem!_pos uD i.val (by rw [uD_length]; exact i.2)]
      exact List.getElem_mem (by rw [uD_length]; exact i.2)) k hk⟩

private noncomputable def U (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) :
    Subgroup ↥⁅Qj, Qj⁆ := Subgroup.closure (Set.range (uG hD))

private noncomputable def V (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) :
    Subgroup (MulAut ↥Jc) := (U hD).map (Subgroup.subtype (⁅Qj, Qj⁆))

private theorem V_eq_closure (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) :
    V hD = Subgroup.closure (Set.range fun i : Fin 4 => (uG hD i : MulAut ↥Jc)) := by
  rw [V, U]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_map.2 ⟨uG hD i, Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩

private theorem mem_V_iff {hD} {u : ↥⁅Qj, Qj⁆} :
    (u : MulAut ↥Jc) ∈ V hD ↔ u ∈ U hD := by
  rw [V]
  exact Subgroup.mem_map_iff_mem (Subgroup.subtype_injective (⁅Qj, Qj⁆))

private theorem uG_comm (hD) (i j : Fin 4) : Commute (uG hD i) (uG hD j) := by
  apply Subtype.ext
  change qWord (dWord (uD[i.val]!)) * qWord (dWord (uD[j.val]!)) =
    qWord (dWord (uD[j.val]!)) * qWord (dWord (uD[i.val]!))
  rw [← qWord_dWord_append, ← qWord_dWord_append]
  apply qWord_eq_qWord (dWord_lt3 _) (dWord_lt3 _)
  intro k hk
  exact u_pair_act i.2 j.2 hk

private theorem U_comm (hD) : IsMulCommutative (U hD) := by
  apply Subgroup.isMulCommutative_closure
  rw [Set.pairwise_iff_of_refl]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact uG_comm hD i j

private theorem U_abelian (hD) {a b : ↥⁅Qj, Qj⁆} (ha : a ∈ U hD) (hb : b ∈ U hD) :
    a * b = b * a := by
  haveI := U_comm hD
  exact setLike_mul_comm ha hb


private theorem uConjA_length : uConjA.length = 4 := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.2

private theorem uConjAinv_length : uConjAinv.length = 4 := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.2

private theorem uConjB_length : uConjB.length = 4 := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.2

private theorem uConjBinv_length : uConjBinv.length = 4 := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

private theorem uConjA_mem_all (i : Fin 4) :
    uConjA[i.val]! ∈ uConjA ++ uConjAinv ++ uConjB ++ uConjBinv := by
  have hlen : i.val < uConjA.length := by rw [uConjA_length]; exact i.2
  rw [getElem!_pos uConjA i.val hlen]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.getElem_mem hlen)))

private theorem uConjAinv_mem_all (i : Fin 4) :
    uConjAinv[i.val]! ∈ uConjA ++ uConjAinv ++ uConjB ++ uConjBinv := by
  have hlen : i.val < uConjAinv.length := by rw [uConjAinv_length]; exact i.2
  rw [getElem!_pos uConjAinv i.val hlen]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.getElem_mem hlen)))

private theorem uConjB_mem_all (i : Fin 4) :
    uConjB[i.val]! ∈ uConjA ++ uConjAinv ++ uConjB ++ uConjBinv := by
  have hlen : i.val < uConjB.length := by rw [uConjB_length]; exact i.2
  rw [getElem!_pos uConjB i.val hlen]
  exact List.mem_append_left _ (List.mem_append_right _
    (List.getElem_mem hlen))

private theorem uConjBinv_mem_all (i : Fin 4) :
    uConjBinv[i.val]! ∈ uConjA ++ uConjAinv ++ uConjB ++ uConjBinv := by
  have hlen : i.val < uConjBinv.length := by rw [uConjBinv_length]; exact i.2
  rw [getElem!_pos uConjBinv i.val hlen]
  exact List.mem_append_right _ (List.getElem_mem hlen)

private theorem uConj_lt4 : ∀ s ∈ uConjA ++ uConjAinv ++ uConjB ++ uConjBinv, ∀ j ∈ s, j < 4 := by
  have h := uOK
  simp only [Native.uOK, Bool.and_eq_true, beq_iff_eq] at h
  have hG : ((uConjA ++ uConjAinv ++ uConjB ++ uConjBinv).all
      fun s => s.all fun x => decide (x < 4)) = true := h.1.1.2
  intro s hs j hj
  have := (List.all_eq_true.1 hG) s hs
  simpa using (List.all_eq_true.1 this) j hj

private theorem qWord_uProdWord (s : List Nat) :
    qWord (dWord (Native.uProdWord s)) =
      (s.map fun j => qWord (dWord (uD[j]!))).prod := by
  rw [Native.uProdWord, dWord_flatMap, qWord_flatMap]

private theorem qWord_uProd_mem_V (hD) {s : List Nat} (hs : ∀ j ∈ s, j < 4) :
    qWord (dWord (Native.uProdWord s)) ∈ V hD := by
  rw [qWord_uProdWord]
  refine Subgroup.list_prod_mem (V hD) ?_
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  rw [V_eq_closure]
  exact Subgroup.subset_closure ⟨⟨j, hs j hj⟩, rfl⟩

private theorem qWord_mem_V_of_action (hD) {w s : List Nat} (hw : ∀ k ∈ w, k < 3)
    (hs : ∀ j ∈ s, j < 4) (h : Native.sameActBasis w (dWord (Native.uProdWord s)) = true) :
    qWord w ∈ V hD := by
  rw [show qWord w = qWord (dWord (Native.uProdWord s)) from
    qWord_eq_qWord hw (dWord_lt3 _) fun k hk => sameActBasis_spec h hk]
  exact qWord_uProd_mem_V hD hs

private theorem word_a_mem (i : Fin 4) :
    ∀ k ∈ [0] ++ dWord (uD[i.val]!) ++ List.replicate 11 0, k < 3 := by
  intro k hk
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hk
  rcases hk with (rfl | hk) | ⟨_, rfl⟩
  · norm_num
  · exact dWord_lt3 _ k hk
  · norm_num

private theorem aG_norm_gen (hD) (i : Fin 4) :
    qA 0 * (uG hD i : MulAut ↥Jc) * (qA 0)⁻¹ ∈ V hD := by
  have hq0 : qA 0 = qWord [0] := by rw [qWord_cons, qWord_nil, mul_one]
  have hq0inv : (qA 0)⁻¹ = qWord (List.replicate 11 0) := by
    rw [inv_a, qWord_replicate]
  have hword : qA 0 * (uG hD i : MulAut ↥Jc) * (qA 0)⁻¹ =
      qWord ([0] ++ dWord (uD[i.val]!) ++ List.replicate 11 0) := by
    rw [hq0inv, hq0]
    change qWord [0] * qWord (dWord (uD[i.val]!)) * qWord (List.replicate 11 0) =
      qWord ([0] ++ dWord (uD[i.val]!) ++ List.replicate 11 0)
    rw [← qWord_append, ← qWord_append]
  rw [hword]
  exact qWord_mem_V_of_action hD (word_a_mem i)
    (uConj_lt4 _ (uConjA_mem_all i)) (u_conj_parts i.2).2.2.1

private theorem aGinv_norm_gen (hD) (i : Fin 4) :
    (qA 0)⁻¹ * (uG hD i : MulAut ↥Jc) * qA 0 ∈ V hD := by
  have hq0 : qA 0 = qWord [0] := by rw [qWord_cons, qWord_nil, mul_one]
  have hq0inv : (qA 0)⁻¹ = qWord (List.replicate 11 0) := by
    rw [inv_a, qWord_replicate]
  have hword : (qA 0)⁻¹ * (uG hD i : MulAut ↥Jc) * qA 0 =
      qWord (List.replicate 11 0 ++ dWord (uD[i.val]!) ++ [0]) := by
    rw [hq0inv, hq0]
    change qWord (List.replicate 11 0) * qWord (dWord (uD[i.val]!)) * qWord [0] =
      qWord (List.replicate 11 0 ++ dWord (uD[i.val]!) ++ [0])
    rw [← qWord_append, ← qWord_append]
  rw [hword]
  refine qWord_mem_V_of_action hD ?_ (uConj_lt4 _ (uConjAinv_mem_all i)) (u_conj_parts i.2).2.2.2.1
  intro k hk
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hk
  rcases hk with (⟨_, rfl⟩ | hk) | rfl
  · norm_num
  · exact dWord_lt3 _ k hk
  · norm_num




private theorem bG_norm_gen (hD) (i : Fin 4) :
    qA 1 * (uG hD i : MulAut ↥Jc) * (qA 1)⁻¹ ∈ V hD := by
  have hq1 : qA 1 = qWord [1] := by rw [qWord_cons, qWord_nil, mul_one]
  have hq1inv : (qA 1)⁻¹ = qWord [1, 1] := by
    rw [inv_b, pow_two]
    simp [qWord_cons, qWord_nil]
  have hword : qA 1 * (uG hD i : MulAut ↥Jc) * (qA 1)⁻¹ =
      qWord ([1] ++ dWord (uD[i.val]!) ++ [1, 1]) := by
    rw [hq1inv, hq1]
    change qWord [1] * qWord (dWord (uD[i.val]!)) * qWord [1, 1] =
      qWord ([1] ++ dWord (uD[i.val]!) ++ [1, 1])
    rw [← qWord_append, ← qWord_append]
  rw [hword]
  exact qWord_mem_V_of_action hD (by
    intro k hk
    simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil,
      or_false] at hk
    rcases hk with (rfl | hk) | (rfl | rfl)
    · norm_num
    · exact dWord_lt3 _ k hk
    · norm_num
    · norm_num)
    (uConj_lt4 _ (uConjB_mem_all i)) (u_conj_parts i.2).2.2.2.2.1

private theorem bGinv_norm_gen (hD) (i : Fin 4) :
    (qA 1)⁻¹ * (uG hD i : MulAut ↥Jc) * qA 1 ∈ V hD := by
  have hq1 : qA 1 = qWord [1] := by rw [qWord_cons, qWord_nil, mul_one]
  have hq1inv : (qA 1)⁻¹ = qWord [1, 1] := by
    rw [inv_b, pow_two]
    simp [qWord_cons, qWord_nil]
  have hword : (qA 1)⁻¹ * (uG hD i : MulAut ↥Jc) * qA 1 =
      qWord ([1, 1] ++ dWord (uD[i.val]!) ++ [1]) := by
    rw [hq1inv, hq1]
    change qWord [1, 1] * qWord (dWord (uD[i.val]!)) * qWord [1] =
      qWord ([1, 1] ++ dWord (uD[i.val]!) ++ [1])
    rw [← qWord_append, ← qWord_append]
  rw [hword]
  refine qWord_mem_V_of_action hD ?_ (uConj_lt4 _ (uConjBinv_mem_all i))
    (u_conj_parts i.2).2.2.2.2.2
  intro k hk
  simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil,
    or_false] at hk
  rcases hk with ((rfl | rfl) | hk) | rfl
  · norm_num
  · norm_num
  · exact dWord_lt3 _ k hk
  · norm_num


private theorem normalizes_V_of_generators (hD) {x : MulAut ↥Jc}
    (hx : ∀ i : Fin 4, x * (uG hD i : MulAut ↥Jc) * x⁻¹ ∈ V hD) :
    ∀ v ∈ V hD, x * v * x⁻¹ ∈ V hD := by
  rw [V_eq_closure]
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    have h := hx i
    rwa [V_eq_closure] at h
  | one => simp
  | mul a b _ _ iha ihb =>
    have h : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [h]
    exact (Subgroup.closure _).mul_mem iha ihb
  | inv a _ iha =>
    have h : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [h]
    exact (Subgroup.closure _).inv_mem iha

private theorem aG_norm_V (hD) : ∀ v ∈ V hD, qA 0 * v * (qA 0)⁻¹ ∈ V hD :=
  normalizes_V_of_generators hD (aG_norm_gen hD)

private theorem aGinv_norm_V (hD) : ∀ v ∈ V hD, (qA 0)⁻¹ * v * qA 0 ∈ V hD :=
  normalizes_V_of_generators hD (aGinv_norm_gen hD)

private theorem bG_norm_V (hD) : ∀ v ∈ V hD, qA 1 * v * (qA 1)⁻¹ ∈ V hD :=
  normalizes_V_of_generators hD (bG_norm_gen hD)

private theorem bGinv_norm_V (hD) : ∀ v ∈ V hD, (qA 1)⁻¹ * v * qA 1 ∈ V hD :=
  normalizes_V_of_generators hD (bGinv_norm_gen hD)


private theorem a2G_norm_U (hD) (ha : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆) :
    ∀ u ∈ U hD, a2G ha * u * (a2G ha)⁻¹ ∈ U hD := by
  intro u hu
  have hv : (u : MulAut ↥Jc) ∈ V hD := (mem_V_iff (hD := hD)).2 hu
  have h1 : qA 0 * (u : MulAut ↥Jc) * (qA 0)⁻¹ ∈ V hD := aG_norm_V hD _ hv
  have h2 : qA 0 * (qA 0 * (u : MulAut ↥Jc) * (qA 0)⁻¹) * (qA 0)⁻¹ ∈ V hD :=
    aG_norm_V hD _ h1
  refine (mem_V_iff (hD := hD)).1 ?_
  have hval : ((a2G ha * u * (a2G ha)⁻¹ : ↥⁅Qj, Qj⁆) : MulAut ↥Jc) =
      qA 0 * (qA 0 * (u : MulAut ↥Jc) * (qA 0)⁻¹) * (qA 0)⁻¹ := by
    change (qA 0 * qA 0) * (u : MulAut ↥Jc) * (qA 0 * qA 0)⁻¹ = _
    group
  rw [hval]
  exact h2

private theorem a2Ginv_norm_U (hD) (ha : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆) :
    ∀ u ∈ U hD, (a2G ha)⁻¹ * u * a2G ha ∈ U hD := by
  intro u hu
  have hv : (u : MulAut ↥Jc) ∈ V hD := (mem_V_iff (hD := hD)).2 hu
  have h1 : (qA 0)⁻¹ * (u : MulAut ↥Jc) * qA 0 ∈ V hD := aGinv_norm_V hD _ hv
  have h2 : (qA 0)⁻¹ * ((qA 0)⁻¹ * (u : MulAut ↥Jc) * qA 0) * qA 0 ∈ V hD :=
    aGinv_norm_V hD _ h1
  refine (mem_V_iff (hD := hD)).1 ?_
  have hval : (((a2G ha)⁻¹ * u * a2G ha : ↥⁅Qj, Qj⁆) : MulAut ↥Jc) =
      (qA 0)⁻¹ * ((qA 0)⁻¹ * (u : MulAut ↥Jc) * qA 0) * qA 0 := by
    change (qA 0 * qA 0)⁻¹ * (u : MulAut ↥Jc) * (qA 0 * qA 0) = _
    group
  rw [hval]
  exact h2

private theorem bG_norm_U (hD) (hb : qA 1 ∈ ⁅Qj, Qj⁆) :
    ∀ u ∈ U hD, bG hb * u * (bG hb)⁻¹ ∈ U hD := by
  intro u hu
  have hv : (u : MulAut ↥Jc) ∈ V hD := (mem_V_iff (hD := hD)).2 hu
  have h1 : qA 1 * (u : MulAut ↥Jc) * (qA 1)⁻¹ ∈ V hD := bG_norm_V hD _ hv
  refine (mem_V_iff (hD := hD)).1 ?_
  have hval : ((bG hb * u * (bG hb)⁻¹ : ↥⁅Qj, Qj⁆) : MulAut ↥Jc) =
      qA 1 * (u : MulAut ↥Jc) * (qA 1)⁻¹ := rfl
  rw [hval]
  exact h1

private theorem bGinv_norm_U (hD) (hb : qA 1 ∈ ⁅Qj, Qj⁆) :
    ∀ u ∈ U hD, (bG hb)⁻¹ * u * bG hb ∈ U hD := by
  intro u hu
  have hv : (u : MulAut ↥Jc) ∈ V hD := (mem_V_iff (hD := hD)).2 hu
  have h1 : (qA 1)⁻¹ * (u : MulAut ↥Jc) * qA 1 ∈ V hD := bGinv_norm_V hD _ hv
  refine (mem_V_iff (hD := hD)).1 ?_
  have hval : (((bG hb)⁻¹ * u * bG hb : ↥⁅Qj, Qj⁆) : MulAut ↥Jc) =
      (qA 1)⁻¹ * (u : MulAut ↥Jc) * qA 1 := rfl
  rw [hval]
  exact h1


private theorem HH_normalizes (hD) (hb : qA 1 ∈ ⁅Qj, Qj⁆) (ha : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆) :
    ∀ h ∈ HH hb ha, ∀ u ∈ U hD, h * u * h⁻¹ ∈ U hD := by
  intro h hh
  refine Subgroup.closure_induction_left (s := {bG hb, a2G ha}) ?one ?mul ?inv hh
  · intro u hu
    simpa using hu
  · intro x hx y _ ih u hu
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hxn : ∀ w ∈ U hD, x * w * x⁻¹ ∈ U hD := by
      rcases hx with rfl | rfl
      · exact bG_norm_U hD hb
      · exact a2G_norm_U hD ha
    have hstep : x * (y * u * y⁻¹) * x⁻¹ ∈ U hD := hxn _ (ih u hu)
    convert hstep using 1
    group
  · intro x hx y _ ih u hu
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hxin : ∀ w ∈ U hD, x⁻¹ * w * x ∈ U hD := by
      rcases hx with rfl | rfl
      · exact bGinv_norm_U hD hb
      · exact a2Ginv_norm_U hD ha
    have hstep : x⁻¹ * (y * u * y⁻¹) * x ∈ U hD := hxin _ (ih u hu)
    convert hstep using 1
    group


private theorem ncList_length : ncList.length = 10 := by
  have h := ncOK
  simp only [Native.ncOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

private theorem ncW_length : ncW.length = 2 := by
  have h := ncOK
  simp only [Native.ncOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

private theorem ncW_lt10 : ∀ w ∈ ncW, ∀ l ∈ w, l < 10 := by
  have h := ncOK
  simp only [Native.ncOK, Bool.and_eq_true, beq_iff_eq] at h
  intro w hw l hl
  have := (List.all_eq_true.1 h.1.1.2) w hw
  simpa using (List.all_eq_true.1 this) l hl

private theorem ncList_data : ∀ p ∈ ncList, (∀ l ∈ p.1, l < 2) ∧ p.2 < 4 := by
  have h := ncOK
  simp only [Native.ncOK, Bool.and_eq_true, beq_iff_eq] at h
  intro p hp
  have := (List.all_eq_true.1 h.1.2) p hp
  simp only [Bool.and_eq_true] at this
  exact ⟨by simpa using (List.all_eq_true.1 this.1), by simpa using this.2⟩

private theorem nc_actionOK :
    ((List.range 2).all fun j =>
      Native.sameActBasis (dWord (Native.ncExp j)) (dWord [j])) = true := by
  have h := ncOK
  simp only [Native.ncOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem nc_action {j i : Nat} (hj : j < 2) (hi : i < 10) :
    wordAct (dWord (Native.ncExp j)) (2 ^ i) = wordAct (dWord [j]) (2 ^ i) := by
  have h := (List.all_eq_true.1 nc_actionOK) j (List.mem_range.2 hj)
  exact sameActBasis_spec h hi


private theorem ncList_get_mem (j : Fin 10) : ncList[j.val]! ∈ ncList := by
  rw [getElem!_pos ncList j.val (by rw [ncList_length]; exact j.2)]
  exact List.getElem_mem (by rw [ncList_length]; exact j.2)

private noncomputable def dG (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w})
    (w : List Nat) (hw : ∀ l ∈ w, l < 2) : ↥⁅Qj, Qj⁆ :=
  ⟨qWord (dWord w), by rw [hD]; exact qWord_dWord_mem_closure hw⟩

private noncomputable def nG (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w})
    (j : Fin 10) : ↥⁅Qj, Qj⁆ :=
  dG hD (ncList[j.val]!.1) (ncList_data _ (ncList_get_mem j)).1 *
    uG hD ⟨ncList[j.val]!.2, (ncList_data _ (ncList_get_mem j)).2⟩ *
    (dG hD (ncList[j.val]!.1) (ncList_data _ (ncList_get_mem j)).1)⁻¹

private theorem nG_val (hD) (j : Fin 10) :
    (nG hD j : MulAut ↥Jc) = qWord (dWord (Native.ncWord j.val)) := by
  have hlt := (ncList_data _ (ncList_get_mem j)).1
  have hidx := (ncList_data _ (ncList_get_mem j)).2
  change qWord (dWord (ncList[j.val]!.1)) * qWord (dWord (uD[ncList[j.val]!.2]!)) *
      (qWord (dWord (ncList[j.val]!.1)))⁻¹ =
    qWord (dWord (ncList[j.val]!.1 ++ uD[ncList[j.val]!.2]! ++ invD ncList[j.val]!.1))
  rw [← qWord_dWord_inv _ hlt]
  rw [qWord_dWord_append, qWord_dWord_append]

private noncomputable def nGOf (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w})
    (l : Nat) : ↥⁅Qj, Qj⁆ :=
  if h : l < 10 then nG hD ⟨l, h⟩ else 1

private theorem nGOf_val (hD) {l : Nat} (hl : l < 10) :
    (nGOf hD l : MulAut ↥Jc) = qWord (dWord (Native.ncWord l)) := by
  simp [nGOf, hl, nG_val]

private noncomputable def evalN (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w})
    (w : List Nat) : ↥⁅Qj, Qj⁆ := (w.map (nGOf hD)).prod

private theorem evalN_val (hD) (w : List Nat) (hw : ∀ l ∈ w, l < 10) :
    (evalN hD w : MulAut ↥Jc) = qWord (dWord (w.flatMap Native.ncWord)) := by
  induction w with
  | nil => simp [evalN, dWord, qWord]
  | cons l w ih =>
    have hl : l < 10 := hw l List.mem_cons_self
    have hw' : ∀ k ∈ w, k < 10 := fun k hk => hw k (List.mem_cons_of_mem _ hk)
    simp only [evalN, List.map_cons, List.prod_cons]
    change (nGOf hD l : MulAut ↥Jc) * (evalN hD w : MulAut ↥Jc) =
      qWord (dWord ((l :: w).flatMap Native.ncWord))
    rw [nGOf_val hD hl, ih hw']
    rw [List.flatMap_cons, dWord_append, qWord_append]

private theorem nG_mem_normalClosure (hD) (j : Fin 10) :
    nG hD j ∈ Subgroup.normalClosure (U hD : Set ↥⁅Qj, Qj⁆) := by
  have hdata := ncList_data _ (ncList_get_mem j)
  have hu : uG hD ⟨ncList[j.val]!.2, hdata.2⟩ ∈ U hD :=
    Subgroup.subset_closure ⟨_, rfl⟩
  have hle : U hD ≤ Subgroup.normalClosure (U hD : Set ↥⁅Qj, Qj⁆) :=
    Subgroup.le_normalClosure
  exact (Subgroup.normalClosure_normal (s := (U hD : Set ↥⁅Qj, Qj⁆))).conj_mem
    (uG hD ⟨ncList[j.val]!.2, hdata.2⟩) (hle hu) (dG hD (ncList[j.val]!.1) hdata.1)

private theorem evalN_mem_normalClosure (hD) (w : List Nat) (hw : ∀ l ∈ w, l < 10) :
    evalN hD w ∈ Subgroup.normalClosure (U hD : Set ↥⁅Qj, Qj⁆) := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  by_cases h : l < 10
  · rw [show nGOf hD l = nG hD ⟨l, h⟩ by simp [nGOf, h]]
    exact nG_mem_normalClosure hD ⟨l, h⟩
  · rw [show nGOf hD l = 1 by simp [nGOf, h]]
    exact (Subgroup.normalClosure _).one_mem


private theorem ncW_get_mem (j : Nat) (hj : j < 2) : ncW[j]! ∈ ncW := by
  rw [getElem!_pos ncW j (by rw [ncW_length]; exact hj)]
  exact List.getElem_mem (by rw [ncW_length]; exact hj)

private theorem qWord_ncExp_zero : qWord (dWord (Native.ncExp 0)) = qWord g1w := by
  have h : qWord (dWord (Native.ncExp 0)) = qWord (dWord [0]) := by
    apply qWord_eq_qWord (dWord_lt3 _) (dWord_lt3 _)
    intro i hi
    rw [nc_action (by norm_num) hi]
  rw [h, qWord_dWord_single 0 (by norm_num)]
  simp

private theorem qWord_ncExp_one : qWord (dWord (Native.ncExp 1)) = qWord g2w := by
  have h : qWord (dWord (Native.ncExp 1)) = qWord (dWord [1]) := by
    apply qWord_eq_qWord (dWord_lt3 _) (dWord_lt3 _)
    intro i hi
    rw [nc_action (by norm_num) hi]
  rw [h, qWord_dWord_single 1 (by norm_num)]
  simp

private theorem evalN_ncW0 (hD) : evalN hD (ncW[0]!) = g1G hD := by
  refine Subtype.ext ?_
  change (evalN hD (ncW[0]!) : MulAut ↥Jc) = qWord g1w
  rw [evalN_val hD _ (ncW_lt10 _ (ncW_get_mem 0 (by norm_num)))]
  simpa [Native.ncExp] using qWord_ncExp_zero

private theorem evalN_ncW1 (hD) : evalN hD (ncW[1]!) = g2G hD := by
  refine Subtype.ext ?_
  change (evalN hD (ncW[1]!) : MulAut ↥Jc) = qWord g2w
  rw [evalN_val hD _ (ncW_lt10 _ (ncW_get_mem 1 (by norm_num)))]
  simpa [Native.ncExp] using qWord_ncExp_one

private theorem normalClosure_eq_top (hD) :
    Subgroup.normalClosure (U hD : Set ↥⁅Qj, Qj⁆) = ⊤ := by
  refine le_antisymm le_top ?_
  have hg1 : g1G hD ∈ Subgroup.normalClosure (U hD : Set ↥⁅Qj, Qj⁆) := by
    rw [← evalN_ncW0 hD]
    exact evalN_mem_normalClosure hD _ (ncW_lt10 _ (ncW_get_mem 0 (by norm_num)))
  have hg2 : g2G hD ∈ Subgroup.normalClosure (U hD : Set ↥⁅Qj, Qj⁆) := by
    rw [← evalN_ncW1 hD]
    exact evalN_mem_normalClosure hD _ (ncW_lt10 _ (ncW_get_mem 1 (by norm_num)))
  rw [← closure_g1g2_top hD]
  exact (Subgroup.closure_le _).2 (by
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hg1
    · exact hg2)


private theorem closure_ab_normalizes_V_both (hD) :
    ∀ x ∈ Subgroup.closure ({qA 0, qA 1} : Set (MulAut ↥Jc)),
      (∀ v ∈ V hD, x * v * x⁻¹ ∈ V hD) ∧
        ∀ v ∈ V hD, x⁻¹ * v * x ∈ V hD := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨aG_norm_V hD, aGinv_norm_V hD⟩
    · exact ⟨bG_norm_V hD, bGinv_norm_V hD⟩
  | one => exact ⟨fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩
  | mul a b _ _ iha ihb =>
    refine ⟨?_, ?_⟩
    · intro v hv
      have h : (a * b) * v * (a * b)⁻¹ = a * (b * v * b⁻¹) * a⁻¹ := by group
      rw [h]
      exact iha.1 _ (ihb.1 v hv)
    · intro v hv
      have h : (a * b)⁻¹ * v * (a * b) = b⁻¹ * (a⁻¹ * v * a) * b := by group
      rw [h]
      exact ihb.2 _ (iha.2 v hv)
  | inv a _ iha =>
    refine ⟨?_, ?_⟩
    · exact iha.2
    · intro v hv
      have h : (a⁻¹)⁻¹ * v * a⁻¹ = a * v * a⁻¹ := by group
      rw [h]
      exact iha.1 v hv

private theorem closure_ab_normalizes_V (hD) :
    ∀ x ∈ Subgroup.closure ({qA 0, qA 1} : Set (MulAut ↥Jc)),
      ∀ v ∈ V hD, x * v * x⁻¹ ∈ V hD :=
  fun x hx => (closure_ab_normalizes_V_both hD x hx).1

private theorem stabilizer_normalizes_U (hD) {h : ↥⁅Qj, Qj⁆}
    (hh : h ∈ MulAction.stabilizer ↥⁅Qj, Qj⁆ (⟨tA, tA_mem_O1⟩ : ↥O1)) :
    ∀ u ∈ U hD, h * u * h⁻¹ ∈ U hD := by
  have hsm : h • (⟨tA, tA_mem_O1⟩ : ↥O1) = (⟨tA, tA_mem_O1⟩ : ↥O1) :=
    (MulAction.mem_stabilizer_iff).1 hh
  have ht : (h : MulAut ↥Jc) tA = tA := congrArg Subtype.val hsm
  have hmem : (h : MulAut ↥Jc) ∈ Subgroup.closure ({qA 0, qA 1} : Set (MulAut ↥Jc)) :=
    mem_closure_of_apply_tA (Subgroup.commutator_le_self Qj h.2) ht
  intro u hu
  refine (mem_V_iff (hD := hD)).1 ?_
  change (h : MulAut ↥Jc) * (u : MulAut ↥Jc) * (h : MulAut ↥Jc)⁻¹ ∈ V hD
  exact closure_ab_normalizes_V hD _ hmem _ ((mem_V_iff (hD := hD)).2 hu)

private theorem wordAct_lt {w : List Nat} (hw : ∀ k ∈ w, k < 3) {m : Nat} (hm : m < 1024) :
    wordAct w m < 1024 := by
  induction w with
  | nil => simpa [wordAct] using hm
  | cons k w ih =>
    have hk : k < 3 := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 3 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [wordAct]
    change Co2Smith.Native.glNJT k (wordAct w m) < 1024
    exact glNJT_lt hk _
private theorem g1G_ne_one (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) :
    g1G hD ≠ 1 := by
  intro h
  have hv : qWord g1w = (1 : MulAut ↥Jc) := by
    have := congrArg (fun x : ↥⁅Qj, Qj⁆ => (x : MulAut ↥Jc)) h
    simpa [g1G] using this
  have hfix : qWord g1w (jcA 2) = jcA 2 := by rw [hv]; rfl
  rw [qWord_jcA (by decide)] at hfix
  have hcoord : wordAct g1w 2 = 2 :=
    (jcA_inj (wordAct_lt g1w_lt3 (by norm_num)) (by norm_num)).1 hfix
  exact g1_nontrivial_basis hcoord

private theorem nontrivial_G (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) :
    Nontrivial ↥⁅Qj, Qj⁆ :=
  ⟨⟨g1G hD, 1, g1G_ne_one hD⟩⟩

private theorem faithful_G : FaithfulSMul ↥⁅Qj, Qj⁆ ↥O1 := by
  rw [faithfulSMul_iff]
  intro g hg
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  have hy : y ∈ Subgroup.closure (O1 : Set ↥Jc) := by rw [closure_O1]; trivial
  have hfixO : ∀ x ∈ O1, (g : MulAut ↥Jc) x = x := by
    intro x hx
    have h1 : g • (⟨x, hx⟩ : ↥O1) = ⟨x, hx⟩ := hg ⟨x, hx⟩
    exact congrArg Subtype.val h1
  refine Subgroup.closure_induction (p := fun z _ => (g : MulAut ↥Jc) z = z)
    (fun x hx => hfixO x hx) ?_ ?_ ?_ hy
  · exact map_one (g : MulAut ↥Jc)
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb]
  · intro a _ ha
    rw [map_inv, ha]

private theorem pretransitive_G
    (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) :
    MulAction.IsPretransitive ↥⁅Qj, Qj⁆ ↥O1 := by
  have h1 : qWord g1w ∈ ⁅Qj, Qj⁆ := by
    rw [hD]; exact Subgroup.subset_closure (by simp)
  have h2 : qWord g2w ∈ ⁅Qj, Qj⁆ := by
    rw [hD]; exact Subgroup.subset_closure (by simp)
  rw [MulAction.isPretransitive_iff_base (⟨tA, tA_mem_O1⟩ : ↥O1)]
  intro x
  obtain ⟨gQ, hgQ, hx⟩ := exists_apply_tA_eq x.2
  let S : Set ↥Jc := {z | ∃ g : ↥⁅Qj, Qj⁆, (g : MulAut ↥Jc) tA = z}
  have hS : ∀ g ∈ (⁅Qj, Qj⁆ : Subgroup (MulAut ↥Jc)), ∀ s ∈ S,
      (g : MulAut ↥Jc) s ∈ S := by
    rintro g hg s ⟨h, hh⟩
    refine ⟨⟨g, hg⟩ * h, ?_⟩
    rw [Subgroup.coe_mul]
    change g ((h : MulAut ↥Jc) tA) = g s
    rw [hh]
  have htS : tA ∈ S := ⟨1, by simp⟩
  obtain ⟨g, hgval⟩ := apply_mem_of_invariant h1 h2 hS hgQ htS
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change (g : MulAut ↥Jc) tA = (x : ↥Jc)
  rw [hgval, hx]

private theorem perfect
    (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w}) : commutator ↥⁅Qj, Qj⁆ = ⊤ := by
  let K : Subgroup ↥⁅Qj, Qj⁆ := commutator ↥⁅Qj, Qj⁆
  have hc0 : c0G ∈ K := c0G_mem hD
  have hc1 : c1G ∈ K := c1G_mem hD
  have hcG : ∀ l, cG l ∈ K := by
    intro l
    by_cases h : l = 0
    · simpa [K, cG, h] using hc0
    · simpa [K, cG, h] using hc1
  have heval : ∀ w : List Nat, evalC w ∈ K := by
    intro w
    exact Subgroup.list_prod_mem K (by
      intro x hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
      exact hcG l)
  have hg1 : g1G hD ∈ K := by
    rw [← evalC_perfW0 hD]
    exact heval _
  have hg2 : g2G hD ∈ K := by
    rw [← evalC_perfW1 hD]
    exact heval _
  have htop : K = (⊤ : Subgroup ↥⁅Qj, Qj⁆) := by
    refine le_antisymm le_top ?_
    rw [← closure_g1g2_top hD]
    exact (Subgroup.closure_le K).2 (by
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hg1
      · exact hg2)
  exact htop

private theorem preprimitive (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w})
    (hb : qA 1 ∈ ⁅Qj, Qj⁆) (ha : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆) :
    MulAction.IsPreprimitive ↥⁅Qj, Qj⁆ ↥O1 := by
  haveI := pretransitive_G hD
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base (⟨tA, tA_mem_O1⟩ : ↥O1) ?_
  intro B hα hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  · right
    have hnot : ∃ y ∈ B, y ≠ (⟨tA, tA_mem_O1⟩ : ↥O1) := by
      by_contra h
      push Not at h
      exact hsub (by
        intro x hx y hy
        rw [h x hx, h y hy])
    obtain ⟨y, hyB, hyne⟩ := hnot
    have hyuniv : y ∈ (Set.range point60 ∪ Set.range point16 ∪ Oa) := by
      rw [union_orbs_eq_univ]
      exact Set.mem_univ y
    have hge : 17 ≤ B.ncard := by
      rcases hyuniv with (hy60 | hy16) | hya
      · have hsub60 := O60_subset_of_block hb ha hB hα hyB hy60
        have hsubU : (Set.range point60 ∪ Oa) ⊆ B := by
          rw [Set.union_subset_iff]
          exact ⟨hsub60, by rw [Oa]; exact Set.singleton_subset_iff.2 hα⟩
        have hle := Set.ncard_le_ncard hsubU
        rw [ncard_union_O60_Oa] at hle
        omega
      · have hsub16 := O16_subset_of_block hb ha hB hα hyB hy16
        have hsubU : (Set.range point16 ∪ Oa) ⊆ B := by
          rw [Set.union_subset_iff]
          exact ⟨hsub16, by rw [Oa]; exact Set.singleton_subset_iff.2 hα⟩
        have hle := Set.ncard_le_ncard hsubU
        rw [ncard_union_O16_Oa] at hle
        omega
      · rw [Oa, Set.mem_singleton_iff] at hya
        exact (hyne hya).elim
    have hdiv : B.ncard ∣ Nat.card ↥O1 := MulAction.IsBlock.ncard_dvd_card hB ⟨_, hα⟩
    rw [Nat.card_coe_set_eq, ncard_O1] at hdiv
    have hle77 : B.ncard ≤ 77 := by
      have h := Set.ncard_le_ncard (Set.subset_univ B) (Set.finite_univ)
      rwa [Set.ncard_univ, Nat.card_coe_set_eq, ncard_O1] at h
    have hcases : B.ncard = 77 := by
      obtain ⟨c, hc⟩ := hdiv
      have hcpos : 0 < c := by
        by_contra hc0
        have hc0' : c = 0 := Nat.eq_zero_of_not_pos hc0
        rw [hc0', mul_zero] at hc
        omega
      have hcle : c ≤ 4 := by nlinarith [hc, hge]
      interval_cases c
      · omega
      · omega
      · omega
      · omega
    refine Set.eq_of_subset_of_ncard_le (s := B) (t := Set.univ)
      (by intro x _; exact Set.mem_univ x) ?_
    rw [Set.ncard_univ, Nat.card_coe_set_eq, ncard_O1, hcases]

theorem isSimpleGroup_commutator_Qj (hD : ⁅Qj, Qj⁆ = Subgroup.closure {qWord g1w, qWord g2w})
    (hb : qA 1 ∈ ⁅Qj, Qj⁆) (ha : qA 0 * qA 0 ∈ ⁅Qj, Qj⁆) : IsSimpleGroup ↥⁅Qj, Qj⁆ := by
  haveI : Nontrivial ↥⁅Qj, Qj⁆ := nontrivial_G hD
  haveI : FaithfulSMul ↥⁅Qj, Qj⁆ ↥O1 := faithful_G
  haveI : MulAction.IsPreprimitive ↥⁅Qj, Qj⁆ ↥O1 := preprimitive hD hb ha
  exact CFSG.GroupActions.isSimpleGroup_of_iwasawa (perfect hD)
    (⟨tA, tA_mem_O1⟩ : ↥O1) (A := U hD)
    (fun h hh u hu => stabilizer_normalizes_U hD hh u hu)
    (fun a ha b hb => U_abelian hD ha hb)
    (normalClosure_eq_top hD)

end CFSG.Sporadic.Co2Jc
