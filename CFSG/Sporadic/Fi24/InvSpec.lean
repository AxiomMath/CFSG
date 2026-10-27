module

public import CFSG.Sporadic.Fi24.RRefSpec

public section

namespace CFSG.Sporadic.Fi24.Native

open Matrix CFSG.F3.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def invPiv (d : ℕ) (a : Array W) (c l : ℕ) (bit : UInt64) : ℕ :=
  (List.range' c (d - c)).foldl (fun p i => if p == d && a[i]!.nz l bit then i else p) d

@[expose] def invElim (c l : ℕ) (bit : UInt64) (pa pb : W) (s : Array W × Array W) (i : ℕ) :
    Array W × Array W :=
  if i != c then
    if s.1[i]!.limbP l &&& bit != 0 then (s.1.modify i (·.sub pa), s.2.modify i (·.sub pb))
    else if s.1[i]!.limbM l &&& bit != 0 then (s.1.modify i (·.add pa), s.2.modify i (·.add pb))
    else s
  else s

@[expose] def invNorm (c l : ℕ) (bit : UInt64) (s : Array W × Array W) : Array W × Array W :=
  if s.1[c]!.limbM l &&& bit != 0 then (s.1.modify c W.neg, s.2.modify c W.neg) else s

@[expose] def invCol (d : ℕ) (s : Array W × Array W) (c : ℕ) : Array W × Array W :=
  let l := c >>> 6
  let bit : UInt64 := (1 : UInt64) <<< (c &&& 63).toUInt64
  let p := invPiv d s.1 c l bit
  if p < d then
    let t := invNorm c l bit (s.1.swapIfInBounds c p, s.2.swapIfInBounds c p)
    (List.range' 0 d).foldl (invElim c l bit t.1[c]! t.2[c]!) t
  else s

theorem forIn_id_eq {α β : Type} (l : List α) (init : β) {f : α → β → Id (ForInStep β)}
    (g : α → β → β) (h : ∀ a b, f a b = ForInStep.yield (g a b)) :
    forIn l init f = l.foldl (fun b a => g a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih => rw [List.forIn_cons, h]; exact ih _

theorem id_bind {α β : Type} (x : Id α) (k : α → Id β) : (x >>= k) = k x := rfl

theorem invW_eq (d : ℕ) (M : Array W) :
    invW d M = ((List.range' 0 d).foldl (invCol d) (M, idW d)).2 := by
  unfold invW
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_id_eq _ _ (fun c s => invCol d s c)]
  · rfl
  intro c s
  unfold invCol invPiv
  rw [forIn_id_eq _ _ (fun i p => if p == d && s.1[i]!.nz (c >>> 6) (1 <<< (c &&& 63).toUInt64) then i else p)]
  · simp only [id_bind]
    generalize List.foldl _ d (List.range' c (d - c)) = p
    by_cases hp : p < d
    · rw [if_pos hp, if_pos hp]
      unfold invNorm
      split_ifs with hn
      · rw [forIn_id_eq _ _ (fun i t => invElim c (c >>> 6) (1 <<< (c &&& 63).toUInt64)
          ((s.1.swapIfInBounds c p).modify c W.neg)[c]! ((s.2.swapIfInBounds c p).modify c W.neg)[c]!
          t i)]
        · rfl
        · intro i t
          unfold invElim
          split_ifs <;> rfl
      · rw [forIn_id_eq _ _ (fun i t => invElim c (c >>> 6) (1 <<< (c &&& 63).toUInt64)
          (s.1.swapIfInBounds c p)[c]! (s.2.swapIfInBounds c p)[c]! t i)]
        · rfl
        · intro i t
          unfold invElim
          split_ifs <;> rfl
    · rw [if_neg hp, if_neg hp]
      rfl
  · intro i p
    split_ifs <;> rfl

theorem testBit_bitOf_pow (c : ℕ) : ((1 : UInt64) <<< (c &&& 63).toUInt64).toNat = 2 ^ (c % 64) := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_one_shift, Nat.testBit_two_pow]
  by_cases h : t = c % 64
  · subst h; simp
  · simp [h, Ne.symm h]

theorem and_bit_ne (y : UInt64) (c : ℕ) :
    (y &&& (1 : UInt64) <<< (c &&& 63).toUInt64 != 0) = y.toNat.testBit (c % 64) := by
  rw [CFSG.Sporadic.Fi23.Native.uint64_ne_zero, UInt64.toNat_and, testBit_bitOf_pow,
    Nat.and_two_pow]
  cases y.toNat.testBit (c % 64) <;> simp

theorem limbP_bit (x : W) (c : ℕ) :
    (x.limbP (c >>> 6) &&& (1 : UInt64) <<< (c &&& 63).toUInt64 != 0) = x.bitP c := by
  rw [and_bit_ne, W.bitP_eq, CFSG.Sporadic.Fi23.Native.shiftRight_six]

theorem limbM_bit (x : W) (c : ℕ) :
    (x.limbM (c >>> 6) &&& (1 : UInt64) <<< (c &&& 63).toUInt64 != 0) = x.bitM c := by
  rw [and_bit_ne, W.bitM_eq, CFSG.Sporadic.Fi23.Native.shiftRight_six]

theorem nz_bit (x : W) (c : ℕ) :
    x.nz (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64) = (x.bitP c || x.bitM c) := by
  unfold W.nz
  rw [and_bit_ne, UInt64.toNat_or, Nat.testBit_or, W.bitP_eq, W.bitM_eq,
    CFSG.Sporadic.Fi23.Native.shiftRight_six]

theorem val_eq_one_of_bitP {x : W} (hx : x.wf = true) {c : ℕ} (h : x.bitP c = true) :
    x.val c = 1 := by
  have := W.not_both hx c
  unfold W.val; rw [h] at this ⊢; simp at this; rw [this]; rfl

theorem val_eq_two_of_bitM {x : W} (hx : x.wf = true) {c : ℕ} (h : x.bitM c = true) :
    x.val c = 2 := by
  have := W.not_both hx c
  unfold W.val; rw [h] at this ⊢; simp at this; rw [this]; rfl

theorem val_eq_zero_of_bits {x : W} {c : ℕ} (h1 : x.bitP c = false) (h2 : x.bitM c = false) :
    x.val c = 0 := by
  unfold W.val; rw [h1, h2]; rfl

theorem val_ne_zero_iff {x : W} (hx : x.wf = true) (c : ℕ) :
    x.val c ≠ 0 ↔ (x.bitP c || x.bitM c) = true := by
  cases h1 : x.bitP c
  · cases h2 : x.bitM c
    · simp [val_eq_zero_of_bits h1 h2]
    · simp [val_eq_two_of_bitM hx h2]; decide
  · simp [val_eq_one_of_bitP hx h1]

section RowOps

variable {d : ℕ}

theorem rowW_swapIfInBounds {X : Array W} {c p : ℕ} (hc : c < X.size) (hp : p < X.size) (k : ℕ) :
    rowW (X.swapIfInBounds c p) k = rowW X (if k = c then p else if k = p then c else k) := by
  unfold rowW
  by_cases hk : k < X.size
  · rw [Array.getElem?_eq_getElem (by simpa using hk), Array.getElem_swapIfInBounds]
    by_cases h1 : k = c
    · simp [h1, hp, Array.getElem?_eq_getElem hp]
    · by_cases h2 : k = p
      · subst h2
        simp [h1, Array.getElem?_eq_getElem hc, hc]
      · simp [h1, h2, Array.getElem?_eq_getElem hk]
  · rw [Array.getElem?_eq_none (by simpa using hk)]
    have h1 : k ≠ c := by omega
    have h2 : k ≠ p := by omega
    simp [h1, h2, Array.getElem?_eq_none (by omega : X.size ≤ k)]

theorem matW_swap {X : Array W} {c p : ℕ} (hX : X.size = d) (hc : c < d) (hp : p < d) :
    matW d d (X.swapIfInBounds c p) =
      (1 : Matrix (Fin d) (Fin d) (ZMod 3)).submatrix (Equiv.swap ⟨c, hc⟩ ⟨p, hp⟩) id *
        matW d d X := by
  rw [← Matrix.submatrix_id_id (matW d d X), ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    Matrix.one_mul]
  ext i j
  rw [Matrix.submatrix_apply, matW_apply, matW_apply, id,
    rowW_swapIfInBounds (by omega) (by omega)]
  congr 2
  by_cases h1 : i = ⟨c, hc⟩
  · subst h1; simp
  · by_cases h2 : i = ⟨p, hp⟩
    · subst h2
      have : (p : ℕ) ≠ c := fun e => h1 (Fin.ext e)
      simp [this]
    · have e1 : i.val ≠ c := fun e => h1 (Fin.ext e)
      have e2 : i.val ≠ p := fun e => h2 (Fin.ext e)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp [e1, e2]

theorem det_swap_ne (c p : Fin d) :
    ((1 : Matrix (Fin d) (Fin d) (ZMod 3)).submatrix (Equiv.swap c p) id).det ≠ 0 := by
  rw [Matrix.det_permute, Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap c p)) with h | h <;> rw [h] <;> decide

theorem matW_neg {X : Array W} (hX : RowsWF X) (hs : X.size = d) {c : ℕ} (hc : c < d) :
    matW d d (X.modify c W.neg) =
      Matrix.diagonal (Function.update (1 : Fin d → ZMod 3) ⟨c, hc⟩ (-1)) * matW d d X := by
  ext i j
  rw [Matrix.diagonal_mul, matW_apply, matW_apply, rowW_modify]
  by_cases h : i = ⟨c, hc⟩
  · subst h
    rw [if_pos ⟨rfl, by omega⟩, W.val_neg (hX.row c), Function.update_self]
    exact (neg_one_mul _).symm
  · have e : ¬(c = i.val ∧ i.val < X.size) := fun e => h (Fin.ext e.1.symm)
    rw [if_neg e, Function.update_of_ne h]
    simp

theorem det_neg_ne (c : Fin d) :
    (Matrix.diagonal (Function.update (1 : Fin d → ZMod 3) c (-1))).det ≠ 0 := by
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ c)]
  simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
  decide

theorem matW_addRow {X : Array W} (hX : RowsWF X) (hs : X.size = d) {i c : ℕ} (hi : i < d)
    (hc : c < d) (s : ZMod 3) {f : W → W}
    (hf : ∀ j, (f (rowW X i)).val j = (rowW X i).val j + s * (rowW X c).val j) :
    matW d d (X.modify i f) = Matrix.transvection ⟨i, hi⟩ ⟨c, hc⟩ s * matW d d X := by
  ext k j
  by_cases h : k = ⟨i, hi⟩
  · subst h
    rw [Matrix.transvection_mul_apply_same, matW_apply, matW_apply, matW_apply, rowW_modify,
      if_pos ⟨rfl, by omega⟩, hf]
  · rw [Matrix.transvection_mul_apply_of_ne (ha := h), matW_apply, matW_apply, rowW_modify,
      if_neg (fun e => h (Fin.ext e.1.symm))]

end RowOps

structure InvState (d c : ℕ) (N : Matrix (Fin d) (Fin d) (ZMod 3)) (s : Array W × Array W) :
    Prop where
  sa : s.1.size = d
  sb : s.2.size = d
  wa : RowsWF s.1
  wb : RowsWF s.2
  zb : ∀ i j, d ≤ j → (rowW s.2 i).val j = 0
  rel : matW d d s.1 = matW d d s.2 * N
  det : (matW d d s.2).det ≠ 0
  col : ∀ i j, i < d → j < c → (rowW s.1 i).val j = if i = j then 1 else 0

structure ElimState (d c : ℕ) (N : Matrix (Fin d) (Fin d) (ZMod 3)) (pa pb : W) (S : ℕ → Prop)
    (s : Array W × Array W) : Prop where
  sa : s.1.size = d
  sb : s.2.size = d
  wa : RowsWF s.1
  wb : RowsWF s.2
  zb : ∀ i j, d ≤ j → (rowW s.2 i).val j = 0
  rel : matW d d s.1 = matW d d s.2 * N
  det : (matW d d s.2).det ≠ 0
  ra : rowW s.1 c = pa
  rb : rowW s.2 c = pb
  col : ∀ i j, i < d → j < c → (rowW s.1 i).val j = if i = j then 1 else 0
  done : ∀ i, i < d → S i → i ≠ c → (rowW s.1 i).val c = 0

section Elim

variable {d c : ℕ} {N : Matrix (Fin d) (Fin d) (ZMod 3)}

theorem rel_op {A B A' B' E : Matrix (Fin d) (Fin d) (ZMod 3)} (h : A = B * N) (hA : A' = E * A)
    (hB : B' = E * B) : A' = B' * N := by
  rw [hA, hB, h, Matrix.mul_assoc]

theorem det_op {B B' E : Matrix (Fin d) (Fin d) (ZMod 3)} (hB : B' = E * B) (hE : E.det ≠ 0)
    (h : B.det ≠ 0) : B'.det ≠ 0 := by
  rw [hB, Matrix.det_mul]; exact mul_ne_zero hE h

theorem rowW_modify_size {X : Array W} {i k : ℕ} {f : W → W} (hk : k ≠ i) :
    rowW (X.modify i f) k = rowW X k := by
  rw [rowW_modify, if_neg (fun e => hk e.1.symm)]

theorem elim_row {pa pb : W} {S : ℕ → Prop} {s : Array W × Array W} (hc : c < d) (hd : d ≤ 781)
    (h : ElimState d c N pa pb S s) {i : ℕ} (hi : i < d) (hic : i ≠ c) (e : ZMod 3)
    (fa fb : W → W)
    (hfa : ∀ x, x.wf = true → (fa x).wf = true ∧ ∀ j, (fa x).val j = x.val j + e * pa.val j)
    (hfb : ∀ x, x.wf = true → (fb x).wf = true ∧ ∀ j, (fb x).val j = x.val j + e * pb.val j)
    (hpa1 : pa.val c = 1) (hz : (rowW s.1 i).val c + e = 0) :
    ElimState d c N pa pb (fun k => S k ∨ k = i) (s.1.modify i fa, s.2.modify i fb) := by
  have hpa : pa.wf = true := h.ra ▸ h.wa.row c
  have hpb : pb.wf = true := h.rb ▸ h.wb.row c
  have hA : matW d d (s.1.modify i fa) = Matrix.transvection ⟨i, hi⟩ ⟨c, hc⟩ e * matW d d s.1 :=
    matW_addRow h.wa h.sa hi hc e (fun j => by rw [(hfa _ (h.wa.row i)).2, h.ra])
  have hB : matW d d (s.2.modify i fb) = Matrix.transvection ⟨i, hi⟩ ⟨c, hc⟩ e * matW d d s.2 :=
    matW_addRow h.wb h.sb hi hc e (fun j => by rw [(hfb _ (h.wb.row i)).2, h.rb])
  have hne : (⟨i, hi⟩ : Fin d) ≠ ⟨c, hc⟩ := fun e => hic (congrArg Fin.val e)
  have hE : (Matrix.transvection (⟨i, hi⟩ : Fin d) ⟨c, hc⟩ e).det ≠ 0 := by
    rw [Matrix.det_transvection_of_ne (h := hne)]; exact one_ne_zero
  have hrow : ∀ (X : Array W) (f : W → W) k, rowW (X.modify i f) k =
      if k = i ∧ k < X.size then f (rowW X k) else rowW X k := by
    intro X f k
    rw [rowW_modify]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk, Ne.symm hk]
  refine ⟨by simp [h.sa], by simp [h.sb], RowsWF.modify h.wa i (fun x hx => (hfa x hx).1),
    RowsWF.modify h.wb i (fun x hx => (hfb x hx).1), ?_, rel_op h.rel hA hB, det_op hB hE h.det,
    by rw [rowW_modify_size (Ne.symm hic)]; exact h.ra,
    by rw [rowW_modify_size (Ne.symm hic)]; exact h.rb, ?_, ?_⟩
  · intro k j hj
    rw [hrow]
    split_ifs
    · rw [(hfb _ (h.wb.row k)).2, h.zb k j hj, ← h.rb, h.zb c j hj, mul_zero, add_zero]
    · exact h.zb k j hj
  · intro k j hk hj
    rw [hrow]
    by_cases hm : k = i ∧ k < s.1.size
    · rw [if_pos hm, (hfa _ (h.wa.row k)).2, ← h.ra, h.col c j hc hj, if_neg (by omega), mul_zero,
        add_zero]
      exact h.col k j hk hj
    · rw [if_neg hm]
      exact h.col k j hk hj
  · intro k hk hS hkc
    rw [hrow]
    split_ifs with h1
    · rw [(hfa _ (h.wa.row k)).2, h1.1, ← h.ra]
      rw [h.ra, hpa1, mul_one]
      exact hz
    · rcases hS with hS | hS
      · exact h.done k hk hS hkc
      · exact absurd ⟨hS, by rw [h.sa]; exact hk⟩ h1

theorem ElimState.mono {pa pb : W} {S S' : ℕ → Prop} {s : Array W × Array W}
    (h : ElimState d c N pa pb S s) (hS : ∀ k, S' k → S k) : ElimState d c N pa pb S' s :=
  { h with done := fun i hi hs hic => h.done i hi (hS i hs) hic }

theorem invElim_spec {pa pb : W} {S : ℕ → Prop} {s : Array W × Array W} (hc : c < d)
    (hd : d ≤ 781) (h : ElimState d c N pa pb S s) (hpa1 : pa.val c = 1) {i : ℕ} (hi : i < d) :
    ElimState d c N pa pb (fun k => S k ∨ k = i)
      (invElim c (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64) pa pb s i) := by
  have hpa : pa.wf = true := h.ra ▸ h.wa.row c
  have hpb : pb.wf = true := h.rb ▸ h.wb.row c
  unfold invElim
  by_cases hic : i = c
  · rw [if_neg (by simp [hic])]
    refine { h with done := ?_ }
    intro k hk hs hkc
    rcases hs with hs | e
    · exact h.done k hk hs hkc
    · exact absurd (e.trans hic) hkc
  rw [if_pos (by simpa using hic), rowW_getElem!, limbP_bit, limbM_bit]
  have hxw := h.wa.row i
  by_cases h1 : (rowW s.1 i).bitP c = true
  · rw [if_pos h1]
    refine elim_row hc hd h hi hic (-1) _ _ (fun x hx => ⟨W.wf_sub hx hpa, fun j => ?_⟩)
      (fun x hx => ⟨W.wf_sub hx hpb, fun j => ?_⟩) hpa1 ?_
    · rw [W.val_sub hx hpa, neg_one_mul, sub_eq_add_neg]
    · rw [W.val_sub hx hpb, neg_one_mul, sub_eq_add_neg]
    · rw [val_eq_one_of_bitP hxw h1, add_neg_cancel]
  · rw [if_neg h1]
    by_cases h2 : (rowW s.1 i).bitM c = true
    · rw [if_pos h2]
      refine elim_row hc hd h hi hic 1 _ _ (fun x hx => ⟨W.wf_add hx hpa, fun j => ?_⟩)
        (fun x hx => ⟨W.wf_add hx hpb, fun j => ?_⟩) hpa1 ?_
      · rw [W.val_add hx hpa, one_mul]
      · rw [W.val_add hx hpb, one_mul]
      · rw [val_eq_two_of_bitM hxw h2]; decide
    · rw [if_neg h2]
      have h0 : (rowW s.1 i).val c = 0 :=
        val_eq_zero_of_bits (by simpa using h1) (by simpa using h2)
      refine { h with done := ?_ }
      intro k hk hs hkc
      rcases hs with hs | rfl
      · exact h.done k hk hs hkc
      · exact h0

theorem invElim_fold {pa pb : W} (hc : c < d) (hd : d ≤ 781) (hpa1 : pa.val c = 1) :
    ∀ (L : List ℕ) {S : ℕ → Prop} {s : Array W × Array W}, (∀ i ∈ L, i < d) →
      ElimState d c N pa pb S s →
      ElimState d c N pa pb (fun k => S k ∨ k ∈ L)
        (L.foldl (invElim c (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64) pa pb) s)
  | [], S, s, _, h => h.mono fun k hk => hk.elim id (fun e => absurd e (by simp))
  | i :: L, S, s, hL, h => by
    rw [List.foldl_cons]
    have h1 := invElim_spec hc hd h hpa1 (hL i List.mem_cons_self)
    have h2 := invElim_fold hc hd hpa1 L (fun j hj => hL j (List.mem_cons_of_mem _ hj)) h1
    refine h2.mono fun k hk => ?_
    rcases hk with hk | hk
    · exact Or.inl (Or.inl hk)
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hk

end Elim

theorem invPiv_fold {d : ℕ} {Q : ℕ → Bool} {lo : ℕ} : ∀ (L : List ℕ) (p0 : ℕ),
    (∀ i ∈ L, lo ≤ i ∧ i < d) → (p0 = d ∨ (p0 < d ∧ lo ≤ p0 ∧ Q p0 = true)) →
    let r := L.foldl (fun p i => if (p == d && Q i) = true then i else p) p0
    (r = d ∨ (r < d ∧ lo ≤ r ∧ Q r = true)) ∧ (r = d → p0 = d ∧ ∀ i ∈ L, Q i = false)
  | [], p0, _, h0 => ⟨h0, fun e => ⟨e, by simp⟩⟩
  | i :: L, p0, hL, h0 => by
    intro r
    have hi := hL i List.mem_cons_self
    have hL' : ∀ j ∈ L, lo ≤ j ∧ j < d := fun j hj => hL j (List.mem_cons_of_mem _ hj)
    by_cases hb : (p0 == d && Q i) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      have h1 := invPiv_fold L i hL' (Or.inr ⟨hi.2, hi.1, hb.2⟩)
      have e : r = L.foldl (fun p i => if (p == d && Q i) = true then i else p) i := by
        simp only [r, List.foldl_cons, Bool.and_eq_true, beq_iff_eq, hb, and_self, ite_true]
      rw [e]
      refine ⟨h1.1, fun hr => absurd (h1.2 hr).1 (by omega)⟩
    · have h1 := invPiv_fold L p0 hL' h0
      have e : r = L.foldl (fun p i => if (p == d && Q i) = true then i else p) p0 := by
        simp only [r, List.foldl_cons]
        rw [if_neg hb]
      rw [e]
      refine ⟨h1.1, fun hr => ⟨(h1.2 hr).1, ?_⟩⟩
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · have := (h1.2 hr).1
        simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hb
        simpa using hb this
      · exact (h1.2 hr).2 j hj

section Outer

variable {d c : ℕ} {N : Matrix (Fin d) (Fin d) (ZMod 3)}

theorem det_eq_zero_of_col {A : Matrix (Fin d) (Fin d) (ZMod 3)} (hc : c < d)
    (hcol : ∀ i j : Fin d, j.val < c → A i j = if i = j then 1 else 0)
    (hz : ∀ i : Fin d, c ≤ i.val → A i ⟨c, hc⟩ = 0) : A.det = 0 := by
  classical
  let cc : Fin d := ⟨c, hc⟩
  let v : Fin d → ZMod 3 := fun j => if j = cc then 1 else if j.val < c then -A j cc else 0
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, fun h => ?_, ?_⟩
  · have := congrFun h cc
    simp [v] at this
  · funext i
    have key : ∀ j, A i j * v j =
        (if j = cc then A i cc else 0) + (if j = i then (if j.val < c then -A i cc else 0) else 0) := by
      intro j
      by_cases h1 : j = cc
      · subst h1
        have : ¬(cc.val < c) := by simp [cc]
        simp [v, this]
      · by_cases h2 : j.val < c
        · rw [hcol i j h2]
          by_cases h3 : i = j
          · subst h3; simp [v, h1, h2]
          · simp [v, h1, h2, h3, Ne.symm h3]
        · simp [v, h1, h2]
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct]
    simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hi : i.val < c
    · rw [if_pos hi, add_neg_cancel]
    · rw [if_neg hi, hz i (by omega), add_zero]

theorem pivot_state {s : Array W × Array W} (hc : c < d) (h : InvState d c N s) {p : ℕ}
    (hp : p < d) (hcp : c ≤ p) (hnz : (rowW s.1 p).val c ≠ 0) :
    InvState d c N (invNorm c (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64)
        (s.1.swapIfInBounds c p, s.2.swapIfInBounds c p)) ∧
      (rowW (invNorm c (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64)
        (s.1.swapIfInBounds c p, s.2.swapIfInBounds c p)).1 c).val c = 1 := by
  have hca : c < s.1.size := by rw [h.sa]; exact hc
  have hpa : p < s.1.size := by rw [h.sa]; exact hp
  have hcb : c < s.2.size := by rw [h.sb]; exact hc
  have hpb : p < s.2.size := by rw [h.sb]; exact hp
  have hrc : rowW (s.1.swapIfInBounds c p) c = rowW s.1 p := by
    rw [rowW_swapIfInBounds hca hpa, if_pos rfl]
  have h1 : InvState d c N (s.1.swapIfInBounds c p, s.2.swapIfInBounds c p) := by
    refine ⟨by simp [h.sa], by simp [h.sb], RowsWF.swapIfInBounds h.wa c p,
      RowsWF.swapIfInBounds h.wb c p, ?_, rel_op h.rel (matW_swap h.sa hc hp) (matW_swap h.sb hc hp),
      det_op (matW_swap h.sb hc hp) (det_swap_ne _ _) h.det, ?_⟩
    · intro i j hj
      rw [rowW_swapIfInBounds hcb hpb]
      exact h.zb _ j hj
    · intro i j hi hj
      dsimp only
      rw [rowW_swapIfInBounds hca hpa]
      by_cases e1 : i = c
      · rw [if_pos e1, h.col p j hp hj, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg e1]
        by_cases e2 : i = p
        · rw [if_pos e2, h.col c j hc hj, if_neg (by omega), if_neg (by omega)]
        · rw [if_neg e2]
          exact h.col i j hi hj
  have hw : (rowW s.1 p).wf = true := h.wa.row p
  unfold invNorm
  dsimp only
  rw [rowW_getElem!, limbM_bit, hrc]
  by_cases hm : (rowW s.1 p).bitM c = true
  · rw [if_pos hm]
    have hA := matW_neg h1.wa h1.sa hc
    have hB := matW_neg h1.wb h1.sb hc
    have hrow : ∀ (X : Array W) k, rowW (X.modify c W.neg) k =
        if k = c ∧ k < X.size then (rowW X k).neg else rowW X k := by
      intro X k
      rw [rowW_modify]
      by_cases hk : k = c
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    refine ⟨⟨by simp [h1.sa], by simp [h1.sb], RowsWF.modify h1.wa c (fun x hx => W.wf_neg hx),
      RowsWF.modify h1.wb c (fun x hx => W.wf_neg hx), ?_, rel_op h1.rel hA hB,
      det_op hB (det_neg_ne _) h1.det, ?_⟩, ?_⟩
    · intro i j hj
      rw [hrow]
      split_ifs
      · rw [W.val_neg (h1.wb.row i), h1.zb i j hj]
        decide
      · exact h1.zb i j hj
    · intro i j hi hj
      rw [hrow]
      by_cases e : i = c ∧ i < (s.1.swapIfInBounds c p, s.2.swapIfInBounds c p).1.size
      · rw [if_pos e, W.val_neg (h1.wa.row i), h1.col i j hi hj, if_neg (by omega)]
        decide
      · rw [if_neg e]
        exact h1.col i j hi hj
    · rw [hrow, if_pos ⟨rfl, by simp [h.sa, hc]⟩, W.val_neg (h1.wa.row c), hrc,
        val_eq_two_of_bitM hw hm]
      decide
  · rw [if_neg hm]
    refine ⟨h1, ?_⟩
    rw [hrc]
    have := (val_ne_zero_iff hw c).1 hnz
    rw [Bool.or_eq_true] at this
    rcases this with h2 | h2
    · exact val_eq_one_of_bitP hw h2
    · exact absurd h2 hm

theorem invCol_spec {s : Array W × Array W} (hc : c < d) (hd : d ≤ 781) (hN : N.det ≠ 0)
    (h : InvState d c N s) : InvState d (c + 1) N (invCol d s c) := by
  have hpiv := invPiv_fold (d := d)
    (Q := fun i => s.1[i]!.nz (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64)) (lo := c)
    (List.range' c (d - c)) d (fun i hi => by rw [List.mem_range'_1] at hi; omega) (Or.inl rfl)
  unfold invCol invPiv
  dsimp only at hpiv ⊢
  generalize List.foldl _ d (List.range' c (d - c)) = p at hpiv ⊢
  by_cases hpd : p < d
  · rw [if_pos hpd]
    rcases hpiv.1 with hpe | ⟨-, hcp, hQ⟩
    · omega
    rw [rowW_getElem!, nz_bit, ← val_ne_zero_iff (h.wa.row p)] at hQ
    obtain ⟨ht, ht1⟩ := pivot_state hc h hpd hcp hQ
    generalize invNorm c (c >>> 6) ((1 : UInt64) <<< (c &&& 63).toUInt64)
      (s.1.swapIfInBounds c p, s.2.swapIfInBounds c p) = t at ht ht1 ⊢
    have he : ElimState d c N t.1[c]! t.2[c]! (fun _ => False) t :=
      ⟨ht.sa, ht.sb, ht.wa, ht.wb, ht.zb, ht.rel, ht.det, (rowW_getElem! _ _).symm,
        (rowW_getElem! _ _).symm, ht.col, fun _ _ hf _ => hf.elim⟩
    have hf := invElim_fold hc hd (by rw [rowW_getElem!]; exact ht1) (List.range' 0 d)
      (fun i hi => by rw [List.mem_range'_1] at hi; omega) he
    refine ⟨hf.sa, hf.sb, hf.wa, hf.wb, hf.zb, hf.rel, hf.det, ?_⟩
    intro i j hi hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hf.col i j hi hj
    · by_cases hic : i = j
      · subst hic
        rw [if_pos rfl, hf.ra, rowW_getElem!]
        exact ht1
      · rw [if_neg hic]
        exact hf.done i hi (Or.inr (by rw [List.mem_range'_1]; omega)) hic
  · exfalso
    have hpe : p = d := by rcases hpiv.1 with h' | h' <;> omega
    have hall := (hpiv.2 hpe).2
    have hdet : (matW d d s.1).det = 0 := by
      refine det_eq_zero_of_col hc (fun i j hj => ?_) (fun i hi => ?_)
      · rw [matW_apply, h.col i j i.isLt hj]
        by_cases e : i = j
        · simp [e]
        · have : i.val ≠ j.val := fun e' => e (Fin.ext e')
          simp [e, this]
      · have := hall i (by rw [List.mem_range'_1]; omega)
        rw [rowW_getElem!, nz_bit] at this
        rw [matW_apply]
        by_contra hne
        have := (val_ne_zero_iff (h.wa.row i) c).1 hne
        simp_all
    rw [h.rel, Matrix.det_mul] at hdet
    exact mul_ne_zero h.det hN hdet

theorem invCols_spec {s : Array W × Array W} (hd : d ≤ 781) (hN : N.det ≠ 0)
    (h : InvState d 0 N s) : ∀ n ≤ d, InvState d n N ((List.range' 0 n).foldl (invCol d) s)
  | 0, _ => h
  | n + 1, hn => by
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    exact invCol_spec (by omega) hd hN (invCols_spec hd hN h n (by omega))

end Outer

theorem invW_spec {d : ℕ} (hd : d ≤ 781) {M : Array W} (hs : M.size = d) (hw : RowsWF M)
    (hN : (matW d d M).det ≠ 0) :
    (invW d M).size = d ∧ RowsWF (invW d M) ∧ (∀ i j, d ≤ j → (rowW (invW d M) i).val j = 0) ∧
      matW d d (invW d M) * matW d d M = 1 := by
  have h0 : InvState d 0 (matW d d M) (M, idW d) := by
    refine ⟨hs, idW_size d, hw, RowsWF.idW (by omega), ?_, ?_, ?_, fun _ _ _ hj => absurd hj (by omega)⟩
    · intro i j hj
      by_cases hi : i < d
      · rw [rowW_idW i hi, W.val_setTrit (by omega) (W.val_zero _), if_neg (by omega), W.val_zero]
      · rw [rowW_ge (by rw [idW_size]; omega), W.val_zero]
    · dsimp only
      rw [matW_idW (by omega), Matrix.one_mul]
    · dsimp only
      rw [matW_idW (by omega), Matrix.det_one]
      exact one_ne_zero
  have hf := invCols_spec hd hN h0 d le_rfl
  rw [invW_eq]
  have hA : matW d d ((List.range' 0 d).foldl (invCol d) (M, idW d)).1 = 1 := by
    ext i j
    rw [matW_apply, hf.col i j i.isLt j.isLt, Matrix.one_apply]
    by_cases e : i = j
    · simp [e]
    · have : i.val ≠ j.val := fun e' => e (Fin.ext e')
      simp [e, this]
  refine ⟨hf.sb, hf.wb, hf.zb, ?_⟩
  rw [← hf.rel, hA]

end CFSG.Sporadic.Fi24.Native
