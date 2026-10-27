
module

public import CFSG.Monster.VisCert.FrameOrbit
public import CFSG.Monster.B.Co2.Data
public import CFSG.Monster.B.Short.TransitivityBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv

structure MatFacts : Prop where
  inv : ∀ j < 2, ∀ i < 24,
    VisCert.Native.actRows VisCert.Native.frameRows[j + 1]! (Native.frameInv[j + 1]!)[i]! = 1 <<< i
  recs : ∀ r < 24, ∀ k < 24,
    Native.recordAct Native.genRecords[r]! (1 <<< k) = (Native.genRecords[r]!.matrix)[k]!
  fix : ∀ r < 24, VisCert.Native.actRows Native.genRecords[r]!.matrix Native.vSeed = Native.vSeed
  quot_lt : ∀ r < 24, ∀ t < 22, (Native.genRecords[r]!.quotientMatrix)[t]! < 2 ^ 22
  quot : ∀ r < 24, ∀ t < 22,
    (VisCert.Native.actRows Native.genRecords[r]!.matrix Native.quotientBasis[t]! ^^^
      Native.actD 22 Native.quotientBasis (Native.genRecords[r]!.quotientMatrix)[t]!) = 0 ∨
    (VisCert.Native.actRows Native.genRecords[r]!.matrix Native.quotientBasis[t]! ^^^
      Native.actD 22 Native.quotientBasis (Native.genRecords[r]!.quotientMatrix)[t]!) = Native.vSeed
  vec_lt : ∀ j < 2300, Native.vectors[j]! < 2 ^ 22
  vec_pos : ∀ j < 2300, Native.vecPos[Native.vectors[j]!]! = j
  span_size : Native.spanIdx.size = 22
  span_lt : ∀ t < 22, Native.spanIdx[t]! < 2300
  span : ∀ t < 22,
    Native.actD 22 (Native.spanIdx.map fun j => Native.vectors[j]!) Native.spanInv[t]! = 1 <<< t
  perm : ∀ r < 24, ∀ j < 2300, Native.actD 22 Native.genRecords[r]!.quotientMatrix
    Native.vectors[j]! = Native.vectors[(Native.permutations[r]!)[j]!]!
  pair : ∀ i < 2, Native.eqA 2300 Native.pairPerms[i]! (Native.wordPermA Native.pairWords[i]!) = true
  ord_a : Native.eqA 2300 (Native.powA Native.pairPerms[0]! 2) (Native.idA 2300) = true
  ord_b : Native.eqA 2300 (Native.powA Native.pairPerms[1]! 5) (Native.idA 2300) = true
  ord_ab : Native.eqA 2300
    (Native.powA (Native.compA 2300 Native.pairPerms[0]! Native.pairPerms[1]!) 23)
    (Native.idA 2300) = true
  ne_a : Native.eqA 2300 Native.pairPerms[0]! (Native.idA 2300) = false
  ne_b : Native.eqA 2300 Native.pairPerms[1]! (Native.idA 2300) = false
  ne_ab : Native.eqA 2300 (Native.compA 2300 Native.pairPerms[0]! Native.pairPerms[1]!)
    (Native.idA 2300) = false

theorem testBit_one_shiftLeft (k i : ℕ) : (1 <<< k).testBit i = decide (i = k) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = k
  · simp [h]
  · simp [h, Ne.symm h]

theorem bvec_one_shiftLeft (k : ℕ) (i : Fin 24) :
    bvec 24 (1 <<< k) i = if (i : ℕ) = k then 1 else 0 := by
  rw [bvec_apply, testBit_one_shiftLeft]
  by_cases h : (i : ℕ) = k <;> simp [h]

theorem dec_one_shiftLeft (k : Fin 24) : dec (1 <<< (k : ℕ)) = ellCls k := by
  rw [dec, Finset.sum_eq_single k]
  · rw [bvec_one_shiftLeft, ite_eq_left rfl, one_smul]
  · intro i _ hik
    rw [bvec_one_shiftLeft, ite_eq_right (fun h => hik (Fin.ext h)), zero_smul]
  · simp

theorem glv_smul (u : GLV) (x : L2) : u • x = (u : Module.End (ZMod 2) L2) x := rfl

theorem glv_smul_dec (u : GLV) (rows : Array ℕ)
    (h : ∀ k : Fin 24, u • ellCls k = dec rows[(k : ℕ)]!) (x : ℕ) :
    u • dec x = dec (VisCert.actRows rows x) := by
  rw [dec_actRows, glv_smul, dec, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← glv_smul, h i]

theorem actQ_frameQ {j : ℕ} (hj : j < 15) : (actQ (frameQ j)).unop = kGen ⟨j, hj⟩ := by
  rw [frameQ, dite_eq_left hj, actQ_mk]
  rfl

theorem smul_dec_frameQ {j : ℕ} (hj : j < 15) (x : ℕ) :
    (actQ (frameQ j)).unop • dec x = dec (VisCert.Native.actRows VisCert.Native.frameRows[j]! x) := by
  rw [actQ_frameQ hj, kGen_smul_dec, native_actRows_eq, native_frameRows_eq]

@[expose] def rowsMap (rows : Array ℕ) : Module.End (ZMod 2) L2 :=
  ellBasis.constr (ZMod 2) fun k => dec rows[(k : ℕ)]!

theorem rowsMap_ellCls (rows : Array ℕ) (k : Fin 24) : rowsMap rows (ellCls k) = dec rows[(k : ℕ)]! := by
  rw [rowsMap, ← ellBasis_apply, Module.Basis.constr_basis]

theorem rowsMap_dec (rows : Array ℕ) (x : ℕ) : rowsMap rows (dec x) = dec (VisCert.actRows rows x) := by
  rw [dec_actRows, dec, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rowsMap_ellCls]

theorem actQ_mul_smul (a b : OLq) (x : L2) :
    (actQ (a * b)).unop • x = (actQ b).unop • (actQ a).unop • x := by
  rw [map_mul, MulOpposite.unop_mul, mul_smul]

theorem smul_dec_frameWordQ :
    ∀ w : List ℤ, (∀ l ∈ w, 0 ≤ l ∧ l ≤ 14) → ∀ x : ℕ,
      (actQ (frameWordQ w)).unop • dec x = dec (Native.frameWordAct w x)
  | [], _, x => by
    simp [frameWordQ, Native.frameWordAct]
  | l :: w, hw, x => by
    have hl := hw l List.mem_cons_self
    have hw' : ∀ l ∈ w, 0 ≤ l ∧ l ≤ 14 := fun l' h => hw l' (List.mem_cons_of_mem _ h)
    rw [frameWordQ, actQ_mul_smul, Native.frameWordAct, ← smul_dec_frameWordQ w hw',
      smul_dec_frameQ (by omega)]

theorem recordWordOK_spec {r : Native.GenRecord} (h : Native.recordWordOK r = true) :
    (r.kind = .pairStabilizer → ∀ l ∈ r.word, l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2) ∧
      (r.kind ≠ .pairStabilizer → ∀ l ∈ r.word, 0 ≤ l ∧ l ≤ 14) := by
  unfold Native.recordWordOK at h
  constructor
  · intro hk l hl
    rw [hk] at h
    have := List.all_eq_true.1 h l hl
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    omega
  · intro hk l hl
    rcases hr : r.kind with _ | _ | _
    · exact absurd hr hk
    · rw [hr] at h
      have := List.all_eq_true.1 h l hl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    · rw [hr] at h
      have := List.all_eq_true.1 h l hl
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this

@[expose] def vShort : L2 := dec 12288

theorem vShort_eq : vShort = classOf (Griess.vMinus 0 1) := CFSG.Monster.B.Short.dec_shortSeed

theorem xorHom_actGo {M : Type*} [AddCommMonoid M] (F : ℕ → M)
    (hF : ∀ a b, F (a ^^^ b) = F a + F b) (rows : Array ℕ) (v : ℕ) :
    ∀ m acc, F (VisCert.Native.actGo rows v m acc) =
      F acc + ∑ i ∈ Finset.range m, if v.testBit i then F rows[i]! else 0
  | 0, acc => by simp [VisCert.Native.actGo]
  | m + 1, acc => by
    rw [VisCert.Native.actGo, xorHom_actGo F hF rows v m, Finset.sum_range_succ]
    by_cases h : v.testBit m = true
    · rw [ite_eq_left h, ite_eq_left h, hF]
      abel
    · rw [ite_eq_right h, ite_eq_right h, add_zero]

theorem dec_actD (rows : Array ℕ) (c : ℕ) (d : ℕ) :
    dec (Native.actD d rows c) = ∑ i ∈ Finset.range d, if c.testBit i then dec rows[i]! else 0 := by
  rw [Native.actD, xorHom_actGo dec dec_xor, dec_zero, zero_add]

theorem bvec_actD (n : ℕ) (rows : Array ℕ) (c : ℕ) (d : ℕ) :
    bvec n (Native.actD d rows c) =
      ∑ i ∈ Finset.range d, if c.testBit i then bvec n rows[i]! else 0 := by
  rw [Native.actD, xorHom_actGo (bvec n) (bvec_xor n), bvec_zero, zero_add]

theorem vShort_eq_ellCls : vShort = ellCls 12 + ellCls 13 := by
  rw [vShort, show (12288 : ℕ) = (1 <<< ((12 : Fin 24) : ℕ)) ^^^ (1 <<< ((13 : Fin 24) : ℕ)) from
    rfl, dec_xor, dec_one_shiftLeft, dec_one_shiftLeft]

theorem bL_dec_vShort (x : ℕ) :
    QuadraticMap.polarBilin qL (dec x) vShort =
      (popc 24 (x &&& gramRow 12) : ZMod 2) + (popc 24 (x &&& gramRow 13) : ZMod 2) := by
  rw [vShort_eq_ellCls, map_add, bL_dec, bL_dec]
  rfl

theorem quotBasis_bL_check : ∀ t : Fin 22,
    (popc 24 (Native.quotientBasis[(t : ℕ)]! &&& gramRow 12) : ZMod 2) +
      (popc 24 (Native.quotientBasis[(t : ℕ)]! &&& gramRow 13) : ZMod 2) = 0 := by
  decide +kernel

theorem bL_quotBasis_vShort (t : Fin 22) :
    QuadraticMap.polarBilin qL (dec (quotBasis t)) vShort = 0 := by
  rw [quotBasis, bL_dec_vShort]
  exact quotBasis_bL_check t

@[expose] def coordDot (m : ℕ) : L2 →ₗ[ZMod 2] ZMod 2 :=
  ∑ k : Fin 24, bvec 24 m k • ellBasis.coord k

theorem coord_dec (k : Fin 24) (x : ℕ) : ellBasis.coord k (dec x) = bvec 24 x k := by
  rw [Module.Basis.coord_apply, dec_eq_ellBasis]
  have := congrFun (ellBasis.equivFun.apply_symm_apply (bvec 24 x)) k
  rwa [Module.Basis.equivFun_apply] at this

theorem coordDot_dec (m x : ℕ) : coordDot m (dec x) = (popc 24 (m &&& x) : ZMod 2) := by
  rw [← bvec_dotProduct, coordDot, LinearMap.sum_apply, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, coord_dec, smul_eq_mul]

@[expose] def qbDual : List ℕ :=
  [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 12288, 16384, 32768, 65536, 131072, 262144,
    524288, 1048576, 2097152, 4194304, 8388608, 8192]

theorem qbDual_check : ∀ s t : Fin 22,
    (popc 24 (qbDual.getD s 0 &&& Native.quotientBasis[(t : ℕ)]!) : ZMod 2) =
      if s = t then 1 else 0 := by
  decide +kernel

theorem qbDual_v : ∀ s : Fin 22, (popc 24 (qbDual.getD s 0 &&& 12288) : ZMod 2) = 0 := by
  decide +kernel

theorem qbDual_last : (∀ t : Fin 22,
    (popc 24 (qbDual.getD 22 0 &&& Native.quotientBasis[(t : ℕ)]!) : ZMod 2) = 0) ∧
    (popc 24 (qbDual.getD 22 0 &&& 12288) : ZMod 2) = 1 := by
  decide +kernel

@[expose] def qbFamily : Option (Fin 22) → L2
  | none => vShort
  | some t => dec (quotBasis t)

theorem linearIndependent_qbFamily : LinearIndependent (ZMod 2) qbFamily := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ m : ℕ, ∑ i, c i * coordDot m (qbFamily i) = 0 := by
    intro m
    have := congrArg (coordDot m) hc
    simpa [map_sum] using this
  have hsum : ∀ m : ℕ, ∑ i, c i * coordDot m (qbFamily i) =
      c none * coordDot m vShort + ∑ t : Fin 22, c (some t) * coordDot m (dec (quotBasis t)) := by
    intro m
    rw [Fintype.sum_option]
    rfl
  intro i
  cases i with
  | none =>
    have h := key (qbDual.getD 22 0)
    rw [hsum, vShort, coordDot_dec, qbDual_last.2] at h
    simp only [coordDot_dec, quotBasis, qbDual_last.1, mul_zero, Finset.sum_const_zero,
      add_zero, mul_one] at h
    exact h
  | some s =>
    have h := key (qbDual.getD s 0)
    rw [hsum, vShort, coordDot_dec, qbDual_v] at h
    simp only [coordDot_dec, quotBasis, qbDual_check, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, zero_add] at h
    exact h

theorem xor_eq_of_xor_eq {a b c : ℕ} (h : a ^^^ b = c) : a = b ^^^ c := by
  rw [← h, Nat.xor_comm a b, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

@[expose] def pLetter (l : ℤ) : Equiv.Perm Ω :=
  if 0 < l then pPermN (l.natAbs - 1) else (pPermN (l.natAbs - 1))⁻¹
where
  pPermN (i : ℕ) : Equiv.Perm Ω := if h : i < 24 then pPerm ⟨i, h⟩ else 1

@[expose] def pairWordPerm : List ℤ → Equiv.Perm Ω
  | [] => 1
  | l :: w => pairWordPerm w * pLetter l

theorem rep_permLetter {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 24) :
    Rep 2300 (Native.permLetter l) (pLetter l) := by
  have hi : l.natAbs - 1 < 24 := by omega
  have hP := rep_pPerm ⟨l.natAbs - 1, hi⟩
  unfold Native.permLetter pLetter pLetter.pPermN
  rw [dite_eq_left hi]
  by_cases hpos : 0 < l
  · rw [ite_eq_left hpos, ite_eq_left hpos]
    exact hP
  · rw [ite_eq_right hpos, ite_eq_right hpos]
    refine rep_inv_of_isInvA hP ?_
    have := dataCheck_parts.2.2.2.2.1 _ hi
    rw [Native.permInv, Native.deg]
    rw [getElem!_pos (Native.permutations.map (Native.invCand 2300)) (l.natAbs - 1) (by
      simpa [permutations_size] using hi), Array.getElem_map, ← getElem!_pos]
    exact this

theorem rep_wordPermA :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 24) →
    Rep 2300 (Native.wordPermA w) (pairWordPerm w)
  | [], _ => by simpa [Native.wordPermA, pairWordPerm, Native.deg] using (rep_idA (n := 2300))
  | l :: w, hw => by
    rw [Native.wordPermA, pairWordPerm, Native.deg]
    exact rep_compA (rep_wordPermA w fun l' h => hw l' (List.mem_cons_of_mem _ h))
      (rep_permLetter (hw l List.mem_cons_self))

theorem rep_powA {t : Array ℕ} {g : Equiv.Perm Ω} (ht : Rep 2300 t g) :
    ∀ e, Rep 2300 (Native.powA t e) (g ^ e)
  | 0 => by simpa [Native.powA, Native.deg] using (rep_idA (n := 2300))
  | e + 1 => by
    rw [Native.powA, pow_succ', Native.deg]
    exact rep_compA ht (rep_powA ht e)

theorem orderOf_eq_of_rep {t : Array ℕ} {g : Equiv.Perm Ω} (ht : Rep 2300 t g) {p : ℕ}
    [Fact p.Prime] (hp : Native.eqA 2300 (Native.powA t p) (Native.idA 2300) = true)
    (hne : Native.eqA 2300 t (Native.idA 2300) = false) : orderOf g = p := by
  refine orderOf_eq_prime ((eqA_iff (rep_powA ht p) rep_idA).1 hp) fun h1 => ?_
  have := (eqA_iff ht rep_idA).2 h1
  rw [hne] at this
  exact absurd this (by decide)

end CFSG.Monster.B.Co2
