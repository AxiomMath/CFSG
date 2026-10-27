module

public import CFSG.Sporadic.Co2Schreier.SixCheck

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

structure SixFacts : Prop where
  size : sixPacked.size = 6
  lt : ∀ k < 6, sixPacked[k]! < 2 ^ 22
  indep : ∀ m < 64, (m == 0 || xorBits sixPacked m != 0) = true
  idx_lt : ∀ k < 6, sixIdx k < 2300
  anchor_lt : sixAnchorIdx < 2300
  imgC : ∀ i < 2, ∀ k < 6, sixImage cArrs[i]! k =
    xorBits sixPacked (colBits (witRec.wLocal.sixRows.getD i []) k)
  imgQ : ∀ m < 8, ∀ k < 6, sixImage qArrs[m]! k = sixPacked[k]!
  chain : recordOK 63 witRec.wLocal.sixActionChain 4 = true
  orbits : recordOrbits 63 witRec.wLocal.sixActionChain = [63, 32, 15, 8, 3, 2]
  perm : ∀ i < 2, ∀ p < 63, (witRec.wLocal.sixActionChain.origArrs[i]!)[p]! + 1 =
    colMul (witRec.wLocal.sixRows.getD i []) (p + 1)

theorem sixFacts : SixFacts := by
  have h := six_check
  simp only [sixCheck, Bool.and_eq_true, beq_iff_eq, allLt_iff, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, fun m hm => by simpa using h3 m hm, h4, h5, h6, h7, h8, h9, h10⟩

theorem xorBits_lt {vs : Array ℕ} {d : ℕ} (hvs : ∀ k < vs.size, vs[k]! < 2 ^ d) (m : ℕ) :
    xorBits vs m < 2 ^ d := by
  rw [xorBits]
  suffices ∀ (l : List ℕ) (acc : ℕ), acc < 2 ^ d → (∀ i ∈ l, i < vs.size) →
      l.foldl (fun acc i => if m.testBit i then acc ^^^ vs[i]! else acc) acc < 2 ^ d from
    this _ 0 (Nat.two_pow_pos d) fun i hi => List.mem_range.1 hi
  intro l
  induction l with
  | nil => intro acc h _; exact h
  | cons i l ih =>
    intro acc hacc hl
    rw [List.foldl_cons]
    refine ih _ ?_ fun j hj => hl j (List.mem_cons_of_mem _ hj)
    split_ifs
    · exact Nat.xor_lt_two_pow hacc (hvs i (hl i List.mem_cons_self))
    · exact hacc

theorem sixPacked_get {k : ℕ} (hk : k < 6) :
    sixPacked[k]! = co2PackedVecs[sixIdx k]! ^^^ co2PackedVecs[sixAnchorIdx]! := by
  rw [sixPacked, getElem!_pos _ k (by simpa using hk)]
  simp

@[expose] def sixVec (k : Fin 6) : Co2V := co2Vec (sixIdx k) + co2Vec sixAnchorIdx

theorem sixVec_eq
    (k : Fin 6) : sixVec k = toVecD 22 sixPacked[(k : ℕ)]! := by
  rw [sixVec, co2Vec_eq_toVecD (sixFacts.idx_lt k k.2), co2Vec_eq_toVecD sixFacts.anchor_lt,
    sixPacked_get k.2, toVecD_xor]

theorem sum_sixVec (m : ℕ) :
    ∑ k : Fin 6, (if m.testBit k then sixVec k else 0) = toVecD 22 (xorBits sixPacked m) := by
  rw [toVecD_xorBits, sixFacts.size, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sixVec_eq]

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide

theorem sixVec_sum_eq_zero
    (g : Fin 6 → ZMod 2) (hg : ∑ i, g i • sixVec i = 0) :
    ∀ i, g i = 0 := by
  set m := ofBits 6 fun k => if h : k < 6 then g ⟨k, h⟩ == 1 else false with hm
  have hbit : ∀ k : Fin 6, m.testBit k = (g k == 1) := by
    intro k
    rw [hm, ofBits_testBit]
    simp [k.2]
  have hsum : ∑ k : Fin 6, g k • sixVec k = ∑ k : Fin 6, (if m.testBit k then sixVec k else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hbit k]
    rcases zmod_two_cases (g k) with h | h <;> simp [h]
  rw [hsum, sum_sixVec, ← toVecD_zero 22] at hg
  have h0 : xorBits sixPacked m = 0 :=
    toVecD_injective (xorBits_lt (fun k hk => sixFacts.lt k (sixFacts.size ▸ hk)) m)
      (by norm_num) hg
  have hm0 : m = 0 := by
    have := sixFacts.indep m (ofBits_lt 6 _)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    rcases this with h | h
    · exact h
    · exact absurd h0 h
  intro k
  have := hbit k
  rw [hm0, Nat.zero_testBit] at this
  rcases zmod_two_cases (g k) with h | h
  · exact h
  · rw [h] at this
    exact absurd this (by decide)

theorem sixVec_linearIndependent :
    LinearIndependent (ZMod 2) sixVec := by
  refine Fintype.linearIndependent_iffₛ.2 fun f g hfg i => ?_
  have h := sixVec_sum_eq_zero (f - g) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hfg, sub_self])
  exact sub_eq_zero.1 (h i)

@[expose] def V6 : Submodule (ZMod 2) Co2V := Submodule.span (ZMod 2) (Set.range sixVec)

@[expose] def sixBasis :
    Module.Basis (Fin 6) (ZMod 2) V6 :=
  Module.Basis.span sixVec_linearIndependent

theorem sixBasis_apply
    (k : Fin 6) : (sixBasis k : Co2V) = sixVec k :=
  congrArg Subtype.val (Module.Basis.span_apply sixVec_linearIndependent k)

theorem finrank_V6 :
    Module.finrank (ZMod 2) V6 = 6 := by
  rw [Module.finrank_eq_card_basis sixBasis, Fintype.card_fin]

@[expose] def sixGram : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun k l => if (witRec.wLocal.sixGramRows.getD k 0).testBit l then 1 else 0

@[expose] def sixGramLit : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun k l => if ([54, 21, 59, 52, 47, 29].getD k 0).testBit l then 1 else 0

theorem sixGram_eq : sixGram = sixGramLit := by
  rw [sixGram, sixGramLit, six_basis_eq.2.2]

@[expose] def sixGramInv : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 0, 1, 0; 1, 0, 0, 1, 0, 0; 1, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 1;
    0, 0, 1, 1, 1, 0]

theorem sixGramLit_symm : sixGramLitᵀ = sixGramLit := by
  decide

theorem sixGramLit_diag (k : Fin 6) : sixGramLit k k = 0 := by
  revert k
  decide

theorem sixGramLit_mul_inv : sixGramLit * sixGramInv = 1 := by
  decide

@[expose] def sixForm :
    LinearMap.BilinForm (ZMod 2) V6 := Matrix.toBilin sixBasis sixGram

theorem toMatrix_sixForm :
    LinearMap.BilinForm.toMatrix sixBasis sixForm = sixGram :=
  LinearMap.BilinForm.toMatrix_toBilin sixBasis sixGram

theorem dot_sixGramLit_self (c : Fin 6 → ZMod 2) :
    ∑ i, ∑ j, c i * sixGramLit i j * c j = 0 := by
  revert c
  decide

theorem sixForm_isAlt :
    sixForm.IsAlt := by
  intro x
  rw [sixForm, Matrix.toBilin_apply, sixGram_eq]
  exact dot_sixGramLit_self _

theorem sixGramLit_det_ne_zero : sixGramLit.det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse sixGramLit_mul_inv

theorem sixForm_nondegenerate :
    sixForm.Nondegenerate := by
  have h : sixGram.Nondegenerate := by
    rw [sixGram_eq]
    exact Matrix.nondegenerate_of_det_ne_zero sixGramLit_det_ne_zero
  exact (Matrix.nondegenerate_toBilin_iff sixBasis).2 h

end CFSG.Sporadic.Co2Schreier
