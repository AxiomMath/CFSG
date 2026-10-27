module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafSel

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open CFSG.Assembly
open CFSG.StandardType (GGLabelIso GGLabQTwo)

variable {m : Fin 6} {T : Chk.Tabs}

@[expose] def tagIdx : LargeEvenLieTag → ℕ
  | .A => 0
  | .twA => 1
  | .B => 2
  | .C => 3
  | .D => 4
  | .twD => 5
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8
  | .F4 => 9
  | .twE6 => 10
  | .triD4 => 11
  | .G2 => 12
  | .twB2 => 13
  | .twF4 => 14
  | .B2der => 15
  | .G2der => 16
  | .twF4der => 17

@[expose] def encL (L : LargeEvenLabel) : ℕ × ℕ × ℕ := (tagIdx L.tag, L.rank, L.n)

private theorem fold_bool_add (P : ℕ → Bool) (f : ℕ → ℕ) (n a : ℕ) :
    Nat.fold n (fun i _ acc => if P i then acc + f i else acc) a =
      a + ∑ i : Fin n, (if P i.val then f i.val else 0) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Nat.fold_succ, ih, Fin.sum_univ_castSucc]
    cases h : P n <;> simp [h, Nat.add_assoc]

private theorem countP_range_eq_sumFin (p : ℕ → Bool) (r : ℕ) :
    (List.range r).countP p = ∑ i : Fin r, (if p i.val then 1 else 0) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.countP_append, ih, Fin.sum_univ_castSucc]
    simp [Nat.add_comm]

private theorem orthN_eq_sum {T : Chk.Tabs} (r c : ℕ) :
    Chk.orthN T r c = ∑ i : Fin r, ∑ j : Fin r,
      (if c.testBit i.val && c.testBit j.val && ((T.pair[i.val]!)[j.val]! == 0) then 1
        else 0) := by
  have hinner : ∀ (i : ℕ) (a : ℕ),
      Nat.fold r (fun j _ acc => if c.testBit j && ((T.pair[i]!)[j]! == 0) then acc + 1
        else acc) a =
        a + ∑ j : Fin r,
          (if c.testBit j.val && ((T.pair[i]!)[j.val]! == 0) then 1 else 0) :=
    fun i a => fold_bool_add _ _ _ _
  unfold Chk.orthN
  simp only [hinner]
  rw [fold_bool_add]
  simp only [Nat.zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hi : c.testBit i.val <;> simp

private theorem orthCount_eq_sum (m : Fin 6) (c : ℕ) :
    orthCount m (ofMask m c) = ∑ i : Fin (nroots m), ∑ j : Fin (nroots m),
      (if c.testBit i.val = true ∧ c.testBit j.val = true ∧ pairing m i j = 0 then 1
        else 0) := by
  have h : ((Finset.univ.filter fun t : Root m => c.testBit t.val = true) ×ˢ
        (Finset.univ.filter fun t : Root m => c.testBit t.val = true)).filter
        (fun p => pairing m p.1 p.2 = 0)
      = (Finset.univ ×ˢ Finset.univ : Finset (Root m × Root m)).filter
        (fun p => c.testBit p.1.val = true ∧ c.testBit p.2.val = true ∧
          pairing m p.1 p.2 = 0) := by
    ext p
    simp [and_assoc]
  unfold orthCount ofMask
  rw [h, Finset.card_filter, Finset.sum_product]

private theorem longN_eq (m : Fin 6) (c : ℕ) :
    Chk.longN (nroots m) c = longCount m (ofMask m c) := by
  unfold Chk.longN longCount
  rw [countP_range_eq_sumFin, ofMask, Finset.card_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h1 : c.testBit ↑i <;> cases h2 : tabFix1.getD ↑i false <;> simp

private theorem orthN_eq {T : Chk.Tabs} (hT : Chk.tabsOK m T = true) (c : ℕ) :
    Chk.orthN T (nroots m) c = orthCount m (ofMask m c) := by
  rw [orthN_eq_sum, orthCount_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [tabsOK_pair hT i j]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]

private theorem labF4N_eq (n : ℕ) : Chk.labF4N n = encL (labelF4 n) := by
  unfold Chk.labF4N labelF4
  split <;> simp_all [encL, tagIdx]

private theorem labE6RelN_eq (n l : ℕ) : Chk.labE6RelN n l = encL (labelE6Rel n l) := by
  unfold Chk.labE6RelN labelE6Rel
  split <;> simp_all [encL, tagIdx]

private theorem labSLN_eq (n o : ℕ) : Chk.labSLN n o = encL (labelSL n o) := by
  unfold Chk.labSLN labelSL
  split <;> simp_all only [encL, tagIdx]
  split_ifs with ho <;> simp

private theorem tagIdx_zero (t : LargeEvenLieTag) : tagIdx t = 0 ↔ t = .A := by
  cases t <;> simp [tagIdx]

private theorem tagIdx_one (t : LargeEvenLieTag) : tagIdx t = 1 ↔ t = .twA := by
  cases t <;> simp [tagIdx]

private theorem tagIdx_four (t : LargeEvenLieTag) : tagIdx t = 4 ↔ t = .D := by
  cases t <;> simp [tagIdx]

private theorem tagIdx_six (t : LargeEvenLieTag) : tagIdx t = 6 ↔ t = .E6 := by
  cases t <;> simp [tagIdx]

private theorem tagIdx_ten (t : LargeEvenLieTag) : tagIdx t = 10 ↔ t = .twE6 := by
  cases t <;> simp [tagIdx]

theorem labelOf_eq (hT : Chk.tabsOK m T = true) (c : ℕ) :
    Chk.labelOf T m c = encL (label m (ofMask m c)) := by
  obtain ⟨v, hv⟩ := m
  rcases v with _ | _ | k
  · change Chk.labF4N (Chk.cardN (nroots (⟨0, hv⟩ : Fin 6)) c) =
      encL (labelF4 (ofMask (⟨0, hv⟩ : Fin 6) c).card)
    rw [card_ofMask, labF4N_eq]
  · change Chk.labE6RelN (Chk.cardN (nroots (⟨1, hv⟩ : Fin 6)) c)
        (Chk.longN (nroots (⟨1, hv⟩ : Fin 6)) c) =
      encL (labelE6Rel (ofMask (⟨1, hv⟩ : Fin 6) c).card
        (longCount (⟨1, hv⟩ : Fin 6) (ofMask (⟨1, hv⟩ : Fin 6) c)))
    rw [card_ofMask, longN_eq, labE6RelN_eq]
  · change Chk.labSLN (Chk.cardN (nroots (⟨Nat.succ (Nat.succ k), hv⟩ : Fin 6)) c)
        (Chk.orthN T (nroots (⟨Nat.succ (Nat.succ k), hv⟩ : Fin 6)) c) =
      encL (labelSL (ofMask (⟨Nat.succ (Nat.succ k), hv⟩ : Fin 6) c).card
        (orthCount (⟨Nat.succ (Nat.succ k), hv⟩ : Fin 6)
          (ofMask (⟨Nat.succ (Nat.succ k), hv⟩ : Fin 6) c)))
    rw [card_ofMask, orthN_eq hT, labSLN_eq]

theorem lam2N_encL (L : LargeEvenLabel) :
    Chk.lam2N (encL L) = true ↔ LargeEvenInLambda2 L := by
  obtain ⟨tag, rank, n⟩ := L
  cases tag <;>
    dsimp only [encL] <;>
    simp only [Chk.lam2N, tagIdx, LargeEvenInLambda2, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq, bne_iff_ne, Nat.odd_iff] <;>
    tauto

private theorem q2_of_iso {lab L : LargeEvenLabel} (hlab : lab.n < 2) (h : GGLabelIso lab L) :
    L.n < 2 ∨ L = ⟨.A, 1, 2⟩ := by
  unfold GGLabelIso at h
  rcases h with rfl | h | h | h | h | h | h | h
  · exact Or.inl hlab
  · obtain ⟨-, -, -, hn⟩ := h
    exact Or.inl (hn ▸ hlab)
  · obtain ⟨-, h2⟩ := h
    rw [h2] at ⊢
    exact Or.inl hlab
  · obtain ⟨-, h2⟩ := h
    rw [h2] at ⊢
    exact Or.inl hlab
  · obtain ⟨-, h2⟩ := h
    rw [h2] at ⊢
    exact Or.inl hlab
  · obtain ⟨-, h2⟩ := h
    rw [h2] at ⊢
    exact Or.inl hlab
  · obtain ⟨-, h2⟩ := h
    have hLn : L.n = 2 * lab.n := congrArg LargeEvenLabel.n h2
    rw [hLn]
    have hn : lab.n = 0 ∨ lab.n = 1 := by omega
    rcases hn with hn | hn
    · left; rw [hn]; omega
    · right; rw [h2, hn]
  · obtain ⟨-, h2⟩ := h
    have hlabn : lab.n = 2 * L.n := congrArg LargeEvenLabel.n h2
    rw [hlabn] at hlab
    left
    omega

theorem q2N_encL (L : LargeEvenLabel) :
    Chk.q2N (encL L) = true ↔ ∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab L := by
  obtain ⟨t, r, n⟩ := L
  dsimp only [encL]
  simp only [Chk.q2N, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    GGLabQTwo, tagIdx_zero]
  constructor
  · rintro (hn | ⟨⟨h1, h2⟩, h3⟩)
    · exact ⟨⟨t, r, n⟩, hn, Or.inl rfl⟩
    · subst h1 h2 h3
      exact ⟨⟨.twD, 2, 1⟩, by decide,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))⟩
  · rintro ⟨lab, hlab, hiso⟩
    rcases q2_of_iso hlab hiso with hn | hL
    · left; exact hn
    · right
      have ht : t = .A := congrArg LargeEvenLabel.tag hL
      have hr : r = 1 := congrArg LargeEvenLabel.rank hL
      have hn2 : n = 2 := congrArg LargeEvenLabel.n hL
      subst ht
      subst hr
      subst hn2
      simp

theorem twoNodeN_encL (X J : LargeEvenLabel) :
    Chk.twoNodeN (encL X) (encL J) = true ↔ TwoNodeLabels 3 X J := by
  obtain ⟨xt, xr, xn⟩ := X
  obtain ⟨jt, jr, jn⟩ := J
  simp only [encL, Chk.twoNodeN, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    tagIdx_zero, tagIdx_one, tagIdx_four, tagIdx_six, tagIdx_ten,
    TwoNodeLabels, Nat.dvd_iff_mod_eq_zero]
  tauto

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
