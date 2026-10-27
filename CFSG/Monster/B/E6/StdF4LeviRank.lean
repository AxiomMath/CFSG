module

public import CFSG.Monster.B.Classical.E6AdjointGroup

public section

namespace CFSG.Monster.B.E6.StdF4

open Module CFSG.Blueprint.Chevalley CFSG.Monster.B.Classical.E6Adjoint

@[expose] def colIdx (A b : ℕ) : List ℕ :=
  b :: (brIdx A b ++ if fbit A b then [A] else [])

@[expose] def applyIdx (A : ℕ) (L : List ℕ) : List ℕ := L.flatMap (colIdx A)

@[expose] def idxMask (L : List ℕ) : ℕ := xorMap (fun l => 1 <<< l) L

variable {R : Type*} [Field R]

theorem lvec_append
    (L M : List ℕ) : lvec R (L ++ M) = lvec R L + lvec R M := by
  simp [lvec, List.map_append, List.sum_append]

theorem lvec_singleton {b : ℕ} (hb : b < 78) :
    lvec R [b] = Finsupp.single (lab ⟨b, hb⟩) 1 := by
  rw [lvec_cons, lvec_nil, add_zero, toVec_one_shiftLeft' hb]

theorem toVec_idxMask
    [CharP R 2] (L : List ℕ) : toVec R (idxMask L) = lvec R L := by
  rw [idxMask, toVec_xorMap]
  rfl

theorem certRoot_simple : ∀ i : Fin Tag.E6.rank, e6Certificate.root i = Pi.single i 1 := by
  decide

theorem val_lt_six (i : Fin Tag.E6.rank) : (i : ℕ) < 6 := i.2

theorem six_add_lt (i : Fin Tag.E6.rank) : 6 + (i : ℕ) < 78 := by
  have := val_lt_six i
  omega

theorem rootVec_single (i : Fin Tag.E6.rank) :
    rootVec Tag.E6 R (Pi.single i 1) = Finsupp.single (lab ⟨6 + i, six_add_lt i⟩) 1 := by
  rw [rootVec_eq_single (isRoot_single Tag.E6 i), lab_of_ge (by simp)]
  congr 3
  rw [show (6 + (i : ℕ)) - 6 = i by omega, certRoot_simple]

theorem card_label_E6' : Fintype.card (Label Tag.E6) = 78 := by
  rw [Fintype.card_sum, Fintype.card_fin, card_isRoot]
  rfl

theorem lab_bijective : Function.Bijective lab :=
  (Fintype.bijective_iff_surjective_and_card lab).2
    ⟨lab_surjective, by rw [Fintype.card_fin, card_label_E6']⟩

theorem toVec_apply_lab (m : ℕ) (q : Fin 78) :
    toVec R m (lab q) = if m.testBit q then 1 else 0 := by
  rw [toVec, Finsupp.finsetSum_apply, Finset.sum_eq_single q]
  · split_ifs <;> simp
  · intro k _ hk
    split_ifs
    · rw [Finsupp.single_apply, ite_eq_right_iff]
      intro h
      exact absurd (lab_bijective.1 h) hk
    · rfl
  · simp

section CharTwo

variable [CharP R 2]

theorem colIdx_lt (i : Fin Tag.E6.rank) (b : Fin 78) : ∀ l ∈ colIdx (6 + i) b, l < 78 := by
  intro l hl
  simp only [colIdx, List.mem_cons, List.mem_append] at hl
  rcases hl with rfl | hl | hl
  · exact b.2
  · exact brIdx_lt ⟨6 + i, six_add_lt i⟩ b l hl
  · split_ifs at hl
    · rw [List.mem_singleton] at hl
      rw [hl]
      exact six_add_lt i
    · simp at hl

theorem xOp_one_single
    (i : Fin Tag.E6.rank) (b : Fin 78) :
    xOp Tag.E6 R i 1 (Finsupp.single (lab b) 1) = lvec R (colIdx (6 + i) b) := by
  have e1 : lvec R (brIdx (6 + i) b) = toVec R (brMask (6 + i) b) :=
    (toVec_brMask ⟨6 + i, six_add_lt i⟩ b).symm
  have e2 : lvec R (if fbit (6 + i) b then [6 + i] else []) =
      (if fbit (6 + i) b then (1 : R) else 0) • Finsupp.single (lab ⟨6 + i, six_add_lt i⟩) 1 := by
    split_ifs
    · rw [one_smul, lvec_singleton]
    · rw [zero_smul, lvec_nil]
  rw [xOp_eq, rootOp_apply, rootVec_single, one_smul, one_pow, one_smul,
    bracket_lab ⟨6 + i, six_add_lt i⟩ b, form_lab ⟨6 + i, six_add_lt i⟩ b, colIdx,
    lvec_cons, lvec_append, e1, e2, toVec_one_shiftLeft b, add_assoc]

theorem xOp_one_lvec
    (i : Fin Tag.E6.rank) {L : List ℕ} (hL : ∀ l ∈ L, l < 78) :
    xOp Tag.E6 R i 1 (lvec R L) = lvec R (applyIdx (6 + i) L) := by
  induction L with
  | nil => simp [lvec_nil, applyIdx]
  | cons b L ih =>
    have hb : b < 78 := hL b List.mem_cons_self
    have e : applyIdx (6 + i) (b :: L) = colIdx (6 + i) b ++ applyIdx (6 + i) L :=
      List.flatMap_cons
    rw [lvec_cons, map_add, ih fun l h => hL l (List.mem_cons_of_mem _ h),
      toVec_one_shiftLeft' hb, xOp_one_single i ⟨b, hb⟩, e, lvec_append]

theorem applyIdx_lt (i : Fin Tag.E6.rank) {L : List ℕ} (hL : ∀ l ∈ L, l < 78) :
    ∀ l ∈ applyIdx (6 + i) L, l < 78 := by
  intro l hl
  obtain ⟨b, hb, hl⟩ := List.mem_flatMap.1 hl
  exact colIdx_lt i ⟨b, hL b hb⟩ l hl

theorem sub_one_lvec
    {f : Module.End R (RootModule Tag.E6 R)} {fIdx : List ℕ → List ℕ} {L : List ℕ}
    (hf : f (lvec R L) = lvec R (fIdx L)) : (f - 1) (lvec R L) = lvec R (L ++ fIdx L) := by
  have hneg : -lvec R L = lvec R L := by
    ext l
    rw [Finsupp.neg_apply, CharTwo.neg_eq]
  rw [LinearMap.sub_apply, hf, Module.End.one_apply, sub_eq_add_neg, hneg, lvec_append, add_comm]

end CharTwo

@[expose] def certOK (fIdx : List ℕ → List ℕ) (piv : List ℕ) (pre : List (List ℕ))
    (zs : List ℕ) : Bool :=
  (pre.length == piv.length && zs == pre.map fun s => idxMask (fIdx s)) &&
  ((piv.all fun p => decide (p < 78)) && pre.all fun s => s.all fun l => decide (l < 78)) &&
  ((List.range piv.length).all fun j => (List.range piv.length).all fun k =>
    (zs.getD j 0).testBit (piv.getD k 0) == (j == k)) &&
  (List.range 78).all fun b =>
    idxMask (fIdx [b]) == xorMap (fun k => zs.getD k 0)
      ((List.range piv.length).filter fun k => (idxMask (fIdx [b])).testBit (piv.getD k 0))

theorem list_sum_mem_span {M : Type*} [AddCommGroup M] [Module R M] {s : Set M} :
    ∀ L : List M, (∀ x ∈ L, x ∈ s) → L.sum ∈ Submodule.span R s
  | [], _ => by simp
  | x :: L, h => by
    rw [List.sum_cons]
    exact add_mem (Submodule.subset_span (h x List.mem_cons_self))
      (list_sum_mem_span L fun y hy => h y (List.mem_cons_of_mem _ hy))

variable [CharP R 2]

theorem finrank_range_of_certOK
    (f : Module.End R (RootModule Tag.E6 R)) (fIdx : List ℕ → List ℕ)
    (hf : ∀ L : List ℕ, (∀ l ∈ L, l < 78) → f (lvec R L) = lvec R (fIdx L))
    (piv : List ℕ) (pre : List (List ℕ)) (zs : List ℕ) (h : certOK fIdx piv pre zs = true) :
    finrank R (LinearMap.range f) = piv.length := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hlen, hzs⟩, hpiv, hpre⟩, hdiag⟩, hcol⟩ := h
  set r := piv.length
  have hzk : ∀ k : Fin r, zs.getD k 0 = idxMask (fIdx (pre.getD k [])) := by
    intro k
    rw [hzs, List.getD_eq_getElem _ _ (by rw [List.length_map, hlen]; exact k.2),
      List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2), List.getElem_map]
  have hpk : ∀ k : Fin r, piv.getD k 0 < 78 := fun k => by
    rw [List.getD_eq_getElem _ _ k.2]
    exact hpiv _ (List.getElem_mem _)
  let z : Fin r → RootModule Tag.E6 R := fun k => toVec R (zs.getD k 0)
  have hz : ∀ k, z k = f (lvec R (pre.getD k [])) := by
    intro k
    have hmem : pre.getD k [] ∈ pre := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
      exact List.getElem_mem _
    change toVec R (zs.getD k 0) = _
    rw [hzk, toVec_idxMask, hf _ (hpre _ hmem)]
  have hli : LinearIndependent R z := by
    refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
    have h1 := congrArg (fun v : RootModule Tag.E6 R => v (lab ⟨_, hpk k⟩)) hg
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply, z, toVec_apply_lab] at h1
    rw [Finset.sum_eq_single k] at h1
    · rw [hdiag k k.2 k k.2, beq_self_eq_true] at h1
      simpa using h1
    · intro j _ hj
      rw [hdiag j j.2 k k.2]
      have : (j : ℕ) ≠ k := fun e => hj (Fin.ext e)
      simp [this]
    · simp
  have hrange : LinearMap.range f = Submodule.span R (Set.range z) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨v, rfl⟩
      induction v using Finsupp.induction_linear with
      | zero => rw [map_zero]; exact zero_mem _
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
      | single l c =>
        obtain ⟨b, rfl⟩ := lab_surjective l
        have hc : Finsupp.single (lab b) c = c • Finsupp.single (lab b) (1 : R) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hc, map_smul]
        refine Submodule.smul_mem _ _ ?_
        rw [← lvec_singleton b.2, hf _ (by simp), ← toVec_idxMask, hcol b b.2, toVec_xorMap]
        refine list_sum_mem_span _ fun x hx => ?_
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
        exact ⟨⟨k, (List.mem_range.1 (List.mem_filter.1 hk).1)⟩, rfl⟩
    · rintro _ ⟨k, rfl⟩
      rw [hz]
      exact LinearMap.mem_range_self _ _
  rw [hrange, finrank_span_eq_card hli, Fintype.card_fin]

@[expose] def fIdx₁ (L : List ℕ) : List ℕ := L ++ applyIdx 9 L

@[expose] def fIdx₂ (L : List ℕ) : List ℕ := L ++ applyIdx 6 (applyIdx 11 L)

@[expose] def fIdx₃ (L : List ℕ) : List ℕ := L ++ applyIdx 6 (applyIdx 9 (applyIdx 11 L))

@[expose] def piv₁ : List ℕ := [
  9, 15, 17, 19, 24, 3, 31, 14, 16, 20, 23, 49, 32, 54, 58, 62, 47, 52, 57, 60, 74, 73]

@[expose] def pre₁ : List (List ℕ) := [
  [1], [7], [8], [10], [13], [1, 18], [21], [25], [28], [30], [33], [38], [42], [45], [50], [55],
  [56], [59], [63], [66], [72], [75]]

@[expose] def zs₁ : List ℕ := [
  512, 32768, 131072, 524288, 16777216, 8, 2147483648, 16384, 65536, 1048576, 8388608,
  562949953421312, 4294967296, 18014398509481984, 288230376151711744, 4611686018427387904,
  140737488355328, 4503599627370496, 144115188075855872, 1152921504606846976,
  18889465931478580854784, 9444732965739290427392]

@[expose] def piv₂ : List ℕ := [
  6, 11, 13, 21, 0, 24, 31, 5, 16, 34, 39, 35, 20, 28, 46, 45, 30, 36, 40, 55, 37, 54, 47, 44, 62,
  56, 52, 67, 68, 59, 65, 69]

@[expose] def pre₂ : List (List ℕ) := [
  [2], [4], [8], [10], [2, 12], [17], [19], [4, 22], [23], [26], [27], [29, 35], [32], [33], [35],
  [38, 45], [42], [43], [44], [45], [48], [49, 54], [52], [44, 53], [54], [59], [52, 60], [61],
  [64], [59, 66], [70], [71]]

@[expose] def zs₂ : List ℕ := [
  64, 2048, 8192, 2097152, 1, 16777216, 2147483648, 32, 65536, 17179869184, 549755813888,
  2233382993920, 1048576, 268435456, 70368744177664, 1161084278931456, 1073741824, 68719476736,
  1099511627776, 36028797018963968, 137438953472, 306244774661193728, 140737488355328,
  2269391999729664, 4611686018427387904, 72057594037927936, 148618787703226368,
  147573952589676412928, 295147905179352825856, 9799832789158199296, 36893488147419103232,
  590295810358705651712]

@[expose] def piv₃ : List ℕ := [
  9, 6, 11, 15, 13, 19, 0, 24, 3, 31, 5, 16, 14, 34, 39, 35, 20, 23, 46, 45, 30, 36, 40, 54, 37,
  55, 62, 47, 44, 52, 56, 67, 68, 57, 65, 69, 74, 73]

@[expose] def pre₃ : List (List ℕ) := [
  [1], [1, 2], [1, 4], [7], [8, 13], [10, 19], [1, 2, 12], [13], [1, 18], [19], [1, 4, 22], [23],
  [25], [26], [27], [29, 35], [30], [23, 33], [35], [38, 45], [30, 42], [43], [44], [45, 50], [48],
  [45, 49], [45, 49, 50], [52], [44, 53], [52, 59, 60, 66], [60, 66], [61], [64], [59, 66], [70],
  [71], [72], [75]]

@[expose] def zs₃ : List ℕ := [
  512, 64, 2048, 32768, 139264, 2621440, 1, 16777216, 8, 2147483648, 32, 65536, 16384, 17179869184,
  549755813888, 2233382993920, 1048576, 276824064, 70368744177664, 289954410384064512, 5368709120,
  68719476736, 1099511627776, 306244774661193728, 137438953472, 324259173170675712,
  4611686018427387904, 140737488355328, 2269391999729664, 10957257893392416768,
  11024811887802974208, 147573952589676412928, 295147905179352825856, 11096869481840902144,
  36893488147419103232, 590295810358705651712, 18889465931478580854784, 9444732965739290427392]

theorem certOK₁ : certOK fIdx₁ piv₁ pre₁ zs₁ = true := by decide +kernel

theorem certOK₂ : certOK fIdx₂ piv₂ pre₂ zs₂ = true := by decide +kernel

theorem certOK₃ : certOK fIdx₃ piv₃ pre₃ zs₃ = true := by decide +kernel

theorem finrank_range_xOp_three :
    finrank R (LinearMap.range (xOp Tag.E6 R (3 : Fin 6) 1 - 1)) = 22 :=
  finrank_range_of_certOK _ fIdx₁ (fun _ hL => sub_one_lvec (xOp_one_lvec (3 : Fin 6) hL)) _ _ _
    certOK₁

theorem finrank_range_xOp_zero_five :
    finrank R (LinearMap.range
      (xOp Tag.E6 R (0 : Fin 6) 1 * xOp Tag.E6 R (5 : Fin 6) 1 - 1)) = 32 := by
  refine finrank_range_of_certOK _ fIdx₂
    (fun L hL => sub_one_lvec (fIdx := fun L => applyIdx 6 (applyIdx 11 L)) ?_) _ _ _ certOK₂
  rw [Module.End.mul_apply, xOp_one_lvec (5 : Fin 6) hL,
    xOp_one_lvec (0 : Fin 6) (applyIdx_lt (5 : Fin 6) hL)]
  rfl

theorem finrank_range_xOp_zero_three_five :
    finrank R (LinearMap.range (xOp Tag.E6 R (0 : Fin 6) 1 * xOp Tag.E6 R (3 : Fin 6) 1 *
      xOp Tag.E6 R (5 : Fin 6) 1 - 1)) = 38 := by
  refine finrank_range_of_certOK _ fIdx₃
    (fun L hL => sub_one_lvec (fIdx := fun L => applyIdx 6 (applyIdx 9 (applyIdx 11 L))) ?_)
    _ _ _ certOK₃
  rw [Module.End.mul_apply, Module.End.mul_apply, xOp_one_lvec (5 : Fin 6) hL,
    xOp_one_lvec (3 : Fin 6) (applyIdx_lt (5 : Fin 6) hL),
    xOp_one_lvec (0 : Fin 6) (applyIdx_lt (3 : Fin 6) (applyIdx_lt (5 : Fin 6) hL))]
  rfl

end CFSG.Monster.B.E6.StdF4
