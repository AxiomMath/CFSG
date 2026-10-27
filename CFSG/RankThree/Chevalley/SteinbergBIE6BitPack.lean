module

public import CFSG.Monster.B.E6.StdF4LeviRank

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.Monster.B.Classical.E6Adjoint CFSG.Monster.B.E6.StdF4

@[expose] def mask78 : ℕ := 0x3fffffffffffffffffff

theorem mask78_eq : mask78 = 2 ^ 78 - 1 := by decide

@[expose] def packCol (P c : ℕ) : ℕ := Nat.land (Nat.shiftRight P (Nat.mul 78 c)) mask78

@[expose] def xorSum (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0 (fun a _ ih => Nat.xor a ih) l

@[expose] def packCols (vs : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0 (fun v _ ih => Nat.lor v (Nat.shiftLeft ih 78)) vs

@[expose] def packMul (P : ℕ) (L : List (List ℕ)) : ℕ :=
  packCols (L.map fun rows => xorSum (rows.map (packCol P)))

@[expose] def idPack : ℕ := packCols ((List.range 78).map (Nat.shiftLeft 1))

@[expose] def wordPack (letter : ℕ → List (List ℕ)) (w : List ℕ) : ℕ :=
  w.foldl (fun acc a => packMul acc (letter a)) idPack

@[expose] def certPack (letter : ℕ → List (List ℕ)) (W : List (List ℕ)) : ℕ :=
  xorSum (W.map (wordPack letter))

@[expose] def sparseOK (L : List (List ℕ)) : Bool :=
  L.all fun rows => rows.all fun k => decide (k < 78)

theorem xorSum_nil : xorSum [] = 0 := rfl

theorem xorSum_cons (a : ℕ) (l : List ℕ) : xorSum (a :: l) = a ^^^ xorSum l := rfl

theorem packCols_nil : packCols [] = 0 := rfl

theorem packCols_cons (v : ℕ) (vs : List ℕ) :
    packCols (v :: vs) = v ||| (packCols vs <<< 78) := rfl

theorem packCol_lt (P c : ℕ) : packCol P c < 2 ^ 78 := by
  rw [packCol, mask78_eq]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem xorSum_lt {l : List ℕ} (h : ∀ a ∈ l, a < 2 ^ 78) : xorSum l < 2 ^ 78 := by
  induction l with
  | nil => exact Nat.two_pow_pos _
  | cons a l ih =>
    rw [xorSum_cons]
    exact Nat.xor_lt_two_pow (h a List.mem_cons_self)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem testBit_packCol (P c j : ℕ) :
    (packCol P c).testBit j = (decide (j < 78) && P.testBit (78 * c + j)) := by
  change ((P >>> (78 * c)) &&& mask78).testBit j = _
  rw [mask78_eq, Nat.testBit_land, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    Bool.and_comm]

theorem packCol_xor (P Q c : ℕ) : packCol (P ^^^ Q) c = packCol P c ^^^ packCol Q c := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_packCol, Nat.testBit_xor, Nat.testBit_xor, testBit_packCol, testBit_packCol]
  cases decide (j < 78) <;> simp

theorem packCol_packCols_cons_zero {v : ℕ} (hv : v < 2 ^ 78) (vs : List ℕ) :
    packCol (packCols (v :: vs)) 0 = v := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_packCol, packCols_cons, Nat.testBit_or, Nat.mul_zero, Nat.zero_add,
    Nat.testBit_shiftLeft]
  by_cases hj : j < 78
  · simp [hj, show ¬(78 ≤ j) by omega]
  · have : v.testBit j = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, this]

theorem packCol_packCols_cons_succ (v : ℕ) (hv : v < 2 ^ 78) (vs : List ℕ) (c : ℕ) :
    packCol (packCols (v :: vs)) (c + 1) = packCol (packCols vs) c := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [testBit_packCol, testBit_packCol, packCols_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hv' : v.testBit (78 * (c + 1) + j) = false := Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [hv', Bool.false_or, show 78 * (c + 1) + j - 78 = 78 * c + j by omega]
  simp [show 78 ≤ 78 * (c + 1) + j by omega]

theorem packCol_packCols {vs : List ℕ} (hvs : ∀ v ∈ vs, v < 2 ^ 78) (c : ℕ) :
    packCol (packCols vs) c = vs.getD c 0 := by
  induction vs generalizing c with
  | nil =>
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [testBit_packCol, packCols_nil]
    simp
  | cons v vs ih =>
    have hv := hvs v List.mem_cons_self
    cases c with
    | zero => rw [packCol_packCols_cons_zero hv, List.getD_cons_zero]
    | succ c =>
      rw [packCol_packCols_cons_succ v hv, List.getD_cons_succ,
        ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw))]

section Semantics

variable (R : Type*) [Field R]

@[expose] def labIndex (l : Label Tag.E6) : ℕ :=
  ((Equiv.ofBijective lab lab_bijective).symm l : Fin 78)

theorem labIndex_lab (c : Fin 78) : labIndex (lab c) = c := by
  rw [labIndex]
  congr 1
  exact (Equiv.ofBijective lab lab_bijective).symm_apply_apply c

@[expose] def packEnd (P : ℕ) : Module.End R (RootModule Tag.E6 R) :=
  Finsupp.linearCombination R fun l => toVec R (packCol P (labIndex l))

@[expose] def sparseEnd (L : List (List ℕ)) : Module.End R (RootModule Tag.E6 R) :=
  Finsupp.linearCombination R fun l => lvec R (L.getD (labIndex l) [])

variable {R}

theorem packEnd_single (P : ℕ) (c : Fin 78) :
    packEnd R P (Finsupp.single (lab c) 1) = toVec R (packCol P c) := by
  rw [packEnd, Finsupp.linearCombination_single, one_smul, labIndex_lab]

theorem sparseEnd_single (L : List (List ℕ)) (c : Fin 78) :
    sparseEnd R L (Finsupp.single (lab c) 1) = lvec R (L.getD c []) := by
  rw [sparseEnd, Finsupp.linearCombination_single, one_smul, labIndex_lab]

theorem packEnd_toVec_one_shiftLeft (P : ℕ) {k : ℕ} (hk : k < 78) :
    packEnd R P (toVec R (1 <<< k)) = toVec R (packCol P k) := by
  rw [toVec_one_shiftLeft' hk, packEnd_single]

theorem packEnd_lvec (P : ℕ) {rows : List ℕ} (h : ∀ k ∈ rows, k < 78) :
    packEnd R P (lvec R rows) = (rows.map fun k => toVec R (packCol P k)).sum := by
  rw [lvec, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  exact packEnd_toVec_one_shiftLeft P (h k hk)

theorem packEnd_idPack : packEnd R idPack = 1 :=
  ext_lab fun c => by
    rw [packEnd_single, idPack, packCol_packCols (fun v hv => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
      change 1 <<< k < 2 ^ 78
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (List.mem_range.1 hk)),
      List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
      Module.End.one_apply]
    exact toVec_one_shiftLeft c

section CharTwo

variable [CharP R 2]

theorem toVec_xorSum (l : List ℕ) : toVec R (xorSum l) = (l.map (toVec R)).sum := by
  induction l with
  | nil => rw [xorSum_nil, toVec_zero, List.map_nil, List.sum_nil]
  | cons a l ih => rw [xorSum_cons, toVec_xor, ih, List.map_cons, List.sum_cons]

theorem packEnd_xor (P Q : ℕ) : packEnd R (P ^^^ Q) = packEnd R P + packEnd R Q :=
  ext_lab fun c => by
    rw [LinearMap.add_apply, packEnd_single, packEnd_single, packEnd_single, packCol_xor,
      toVec_xor]

theorem packEnd_xorSum (l : List ℕ) : packEnd R (xorSum l) = (l.map (packEnd R)).sum := by
  induction l with
  | nil =>
    refine ext_lab fun c => ?_
    rw [xorSum_nil, packEnd_single, List.map_nil, List.sum_nil, LinearMap.zero_apply]
    refine (congrArg (toVec R) (Nat.eq_of_testBit_eq fun j => ?_)).trans toVec_zero
    rw [testBit_packCol]
    simp
  | cons a l ih => rw [xorSum_cons, packEnd_xor, ih, List.map_cons, List.sum_cons]

theorem packEnd_packMul (P : ℕ) {L : List (List ℕ)} (hL : sparseOK L = true) :
    packEnd R (packMul P L) = packEnd R P * sparseEnd R L := by
  simp only [sparseOK, List.all_eq_true, decide_eq_true_eq] at hL
  refine ext_lab fun c => ?_
  rw [Module.End.mul_apply, sparseEnd_single, packEnd_single, packMul,
    packCol_packCols (fun v hv => by
      obtain ⟨rows, -, rfl⟩ := List.mem_map.1 hv
      exact xorSum_lt fun a ha => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 ha
        exact packCol_lt P k)]
  have hrows : ∀ k ∈ L.getD c [], k < 78 := by
    intro k hk
    by_cases hc : (c : ℕ) < L.length
    · rw [List.getD_eq_getElem _ _ hc] at hk
      exact hL _ (List.getElem_mem hc) k hk
    · rw [List.getD_eq_default _ _ (by omega)] at hk
      simp at hk
  have hg : (L.map fun rows => xorSum (rows.map (packCol P))).getD c 0 =
      xorSum ((L.getD c []).map (packCol P)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases L[(c : ℕ)]? <;> rfl
  rw [hg, toVec_xorSum, packEnd_lvec P hrows, List.map_map]
  rfl

theorem packEnd_wordPack_aux (letter : ℕ → List (List ℕ)) (w : List ℕ)
    (hw : ∀ a ∈ w, sparseOK (letter a) = true) (acc : ℕ) :
    packEnd R (w.foldl (fun acc a => packMul acc (letter a)) acc) =
      packEnd R acc * (w.map fun a => sparseEnd R (letter a)).prod := by
  induction w generalizing acc with
  | nil => rw [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons a w ih =>
    rw [List.foldl_cons, ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)),
      packEnd_packMul acc (hw a List.mem_cons_self), List.map_cons, List.prod_cons, mul_assoc]

theorem packEnd_wordPack (letter : ℕ → List (List ℕ)) (w : List ℕ)
    (hw : ∀ a ∈ w, sparseOK (letter a) = true) :
    packEnd R (wordPack letter w) = (w.map fun a => sparseEnd R (letter a)).prod := by
  rw [wordPack, packEnd_wordPack_aux letter w hw, packEnd_idPack, one_mul]

theorem commute_packEnd_certPack {X : Module.End R (RootModule Tag.E6 R)}
    (letter : ℕ → List (List ℕ)) (W : List (List ℕ))
    (hW : ∀ w ∈ W, ∀ a ∈ w, sparseOK (letter a) = true ∧ Commute X (sparseEnd R (letter a))) :
    Commute X (packEnd R (certPack letter W)) := by
  rw [certPack, packEnd_xorSum, List.map_map]
  refine Commute.list_sum_right _ _ fun Y hY => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hY
  rw [Function.comp_apply, packEnd_wordPack letter w fun a ha => (hW w hw a ha).1]
  refine Commute.list_prod_right _ _ fun Z hZ => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hZ
  exact (hW w hw a ha).2

theorem packEnd_packMul_idPack {L : List (List ℕ)} (hL : sparseOK L = true) :
    packEnd R (packMul idPack L) = sparseEnd R L := by
  rw [packEnd_packMul idPack hL, packEnd_idPack, one_mul]

theorem commute_sparseEnd_of_cert {X : Module.End R (RootModule Tag.E6 R)}
    (letter : ℕ → List (List ℕ)) (W : List (List ℕ)) {T : List (List ℕ)}
    (hcert : (certPack letter W == packMul idPack T) = true) (hT : sparseOK T = true)
    (hW : ∀ w ∈ W, ∀ a ∈ w, sparseOK (letter a) = true ∧ Commute X (sparseEnd R (letter a))) :
    Commute X (sparseEnd R T) := by
  rw [← packEnd_packMul_idPack hT, ← beq_iff_eq.1 hcert]
  exact commute_packEnd_certPack letter W hW

end CharTwo

end Semantics

section Letters

variable {R : Type*} [Field R]

@[expose] def adSparse (A : ℕ) : List (List ℕ) := (List.range 78).map (brIdx A)

@[expose] def tensorSparse (A : ℕ) : List (List ℕ) :=
  (List.range 78).map fun b => if fbit A b then [A] else []

@[expose] def idSparse : List (List ℕ) := (List.range 78).map fun b => [b]

@[expose] def opSparse (A : ℕ) : List (List ℕ) := (List.range 78).map (colIdx A)

@[expose] def opSubSparse (A : ℕ) : List (List ℕ) :=
  (List.range 78).map fun b => brIdx A b ++ if fbit A b then [A] else []

theorem getD_range_map {α : Type*} (f : ℕ → α) (d : α) (c : Fin 78) :
    ((List.range 78).map f).getD c d = f c := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

theorem lvec_ite_singleton (p : Bool) (A : Fin 78) :
    lvec R (if p then [(A : ℕ)] else []) =
      (if p then (1 : R) else 0) • Finsupp.single (lab A) 1 := by
  cases p
  · simp [lvec_nil]
  · simp [lvec_singleton A.2]

theorem sparseEnd_idSparse : sparseEnd R idSparse = 1 :=
  ext_lab fun b => by
    rw [sparseEnd_single, idSparse, getD_range_map, lvec_singleton b.2, Module.End.one_apply]

variable [CharP R 2]

theorem sparseEnd_adSparse (A : Fin 78) :
    sparseEnd R (adSparse A) = ad R (Finsupp.single (lab A) 1) :=
  ext_lab fun b => by
    rw [sparseEnd_single, adSparse, getD_range_map, ad_apply, bracket_lab, toVec_brMask]

theorem sparseEnd_tensorSparse (A : Fin 78) :
    sparseEnd R (tensorSparse A) = formTensor R (Finsupp.single (lab A) 1) :=
  ext_lab fun b => by
    rw [sparseEnd_single, tensorSparse, getD_range_map, formTensor_apply, form_lab,
      lvec_ite_singleton]

theorem sparseEnd_opSubSparse (A : Fin 78) :
    sparseEnd R (opSubSparse A) =
      ad R (Finsupp.single (lab A) 1) + formTensor R (Finsupp.single (lab A) 1) :=
  ext_lab fun b => by
    rw [sparseEnd_single, opSubSparse, getD_range_map, lvec_append, LinearMap.add_apply, ad_apply,
      bracket_lab, toVec_brMask, formTensor_apply, form_lab, lvec_ite_singleton]

theorem sparseEnd_opSparse (A : Fin 78) :
    sparseEnd R (opSparse A) =
      1 + ad R (Finsupp.single (lab A) 1) + formTensor R (Finsupp.single (lab A) 1) :=
  ext_lab fun b => by
    rw [sparseEnd_single, opSparse, getD_range_map, colIdx, lvec_cons, lvec_append,
      LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, ad_apply, bracket_lab,
      toVec_brMask, formTensor_apply, form_lab, lvec_ite_singleton, toVec_one_shiftLeft,
      add_assoc]

end Letters

theorem certRoot_neg_simple : ∀ i : Fin Tag.E6.rank,
    e6Certificate.root (6 + 2 * (i : ℕ)) = -Pi.single i 1 := by
  decide

theorem twelve_add_lt (i : Fin Tag.E6.rank) : 12 + 2 * (i : ℕ) < 78 := by
  have := val_lt_six i
  omega

theorem rootVec_neg_single_lab {R : Type*} [CommRing R] (i : Fin Tag.E6.rank) :
    rootVec Tag.E6 R (-Pi.single i 1) = Finsupp.single (lab ⟨12 + 2 * i, twelve_add_lt i⟩) 1 := by
  rw [rootVec_eq_single (isRoot_neg_single Tag.E6 i),
    lab_of_ge (show ¬(12 + 2 * (i : ℕ) < 6) by omega)]
  congr 3
  rw [show (12 + 2 * (i : ℕ)) - 6 = 6 + 2 * i by omega, certRoot_neg_simple]

section Operators

variable {R : Type*} [Field R] [CharP R 2]

theorem xOp_eq_lab (i : Fin Tag.E6.rank) (c : R) :
    xOp Tag.E6 R i c = 1 + c • ad R (Finsupp.single (lab ⟨6 + i, six_add_lt i⟩) 1) +
      c ^ 2 • formTensor R (Finsupp.single (lab ⟨6 + i, six_add_lt i⟩) 1) := by
  rw [xOp_eq, rootVec_single]

theorem yOp_eq_lab (i : Fin Tag.E6.rank) (c : R) :
    yOp Tag.E6 R i c = 1 + c • ad R (Finsupp.single (lab ⟨12 + 2 * i, twelve_add_lt i⟩) 1) +
      c ^ 2 • formTensor R (Finsupp.single (lab ⟨12 + 2 * i, twelve_add_lt i⟩) 1) := by
  rw [yOp_eq, rootVec_neg_single_lab]

theorem sparseEnd_opSparse_x (i : Fin Tag.E6.rank) :
    sparseEnd R (opSparse (6 + i)) = xOp Tag.E6 R i 1 := by
  rw [xOp_eq_lab, one_smul, one_pow, one_smul]
  exact sparseEnd_opSparse ⟨6 + i, six_add_lt i⟩

theorem sparseEnd_opSparse_y (i : Fin Tag.E6.rank) :
    sparseEnd R (opSparse (12 + 2 * i)) = yOp Tag.E6 R i 1 := by
  rw [yOp_eq_lab, one_smul, one_pow, one_smul]
  exact sparseEnd_opSparse ⟨12 + 2 * i, twelve_add_lt i⟩

end Operators

end CFSG.RankThree.Chevalley
