module

public import CFSG.Sporadic.Schreier.ONVectorData
public import CFSG.Sporadic.Schreier.ONCheckVectors
public import CFSG.Sporadic.Th.OrbitSpec
public import CFSG.Sporadic.ON.Setup

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

abbrev posV : W → ℕ := posOf (indexOf vectorOrbit.keys) nPts

abbrev posU : W → ℕ := posOf (indexOf lineOrbit.keys) nL

abbrev sigT : Array W :=
  (F3.Native.transpose 154 (sigRows vectorOrbit (rowsOf 154 Data.formPayload) Data.baseList)).map
    ofV

structure VectorFacts : Prop where
  orbit : orbitOK nPts colsA colsB vectorOrbit posV 3 = true
  root : vectorOrbit.keys[0]! = digitsW Data.rootDigits
  root_ne : ¬ digitsW Data.rootDigits = W.zero
  disc : discOK nPts vectorOrbit.alpha vectorOrbit.beta
    (discPar nPts vectorOrbit.alpha vectorOrbit.beta) = true
  basis : basisOK vectorOrbit Data.spanIdx (rowsOf 154 Data.spanInvPayload) = true
  form : formOK (rowsOf 154 Data.formPayload) (invV 154 (rowsOf 154 Data.formPayload)) = true
  gram : gramConnOK (gram vectorOrbit Data.spanIdx (rowsOf 154 Data.formPayload))
    (gramTree (gram vectorOrbit Data.spanIdx (rowsOf 154 Data.formPayload))).1
    (gramTree (gram vectorOrbit Data.spanIdx (rowsOf 154 Data.formPayload))).2 = true
  base_len : Data.baseList.length ≤ 154
  base_lt : (Data.baseList.all (· < nPts)) = true
  sig : sigOK (sigsOf vectorOrbit sigT) (posOf (indexOf (sigsOf vectorOrbit sigT)) nPts) = true
  strong : strongOK nPts (natTab vectorOrbit.alpha) (natTab vectorOrbit.beta)
    (strongArrs nPts (natTab vectorOrbit.alpha) (natTab vectorOrbit.beta) Data.strongWords)
    Data.strongWords = true

theorem vectorFacts : VectorFacts := by
  have h := vector_cert
  unfold vectorCert at h
  rw [← vectorOrbit_def] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h1a⟩, h1b⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, beq_iff_eq.1 h1a, by simpa using h1b, h2, h3, h4, h5, h6, h7, h8, h9⟩

structure LineFacts : Prop where
  lines : linesOK nL vectorOrbit lineOrbit posU (piTab vectorOrbit posU)
    (sigmaTab vectorOrbit posV) (piPre nL (piTab vectorOrbit posU)) 3 = true
  root : lineOrbit.keys[0]! = nuW (digitsW Data.rootDigits)
  disc : discOK nL lineOrbit.alpha lineOrbit.beta
    (discPar nL lineOrbit.alpha lineOrbit.beta) = true

theorem lineFacts : LineFacts := by
  have h := line_cert
  unfold lineCert at h
  rw [← vectorOrbit_def, ← lineOrbit_def] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, beq_iff_eq.1 h2, h3⟩

theorem vparts :
    vectorOrbit.keys.size = N ∧ vectorOrbit.alpha.size = N ∧
    vectorOrbit.beta.size = N ∧
    ∀ i < N, canon154 vectorOrbit.keys[i]! = true ∧ posV vectorOrbit.keys[i]! = i ∧
      ap vectorOrbit.alpha i < N ∧
      vectorOrbit.keys[ap vectorOrbit.alpha i]! = mulVecT colsA vectorOrbit.keys[i]! ∧
      ap vectorOrbit.beta i < N ∧
      vectorOrbit.keys[ap vectorOrbit.beta i]! = mulVecT colsB vectorOrbit.keys[i]! := by
  have h := vectorFacts.orbit
  unfold CFSG.Sporadic.ON.Native.orbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_⟩
  have := CFSG.Sporadic.Th.parAll_eq_true h4 i hi
  simp only [CFSG.Sporadic.ON.Native.orbitCheckAt, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  obtain ⟨⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := this
  exact ⟨h5, h6, h7, h8, h9, h10⟩

theorem vkeys_wf
    {i : ℕ} (hi : i < N) : vectorOrbit.keys[i]!.toV.wf = true :=
  wf_of_canon154 (vparts.2.2.2 i hi).1

theorem vv_of_lt
    {i : ℕ} (hi : i < N) : vv i = vecOf vectorOrbit.keys[i]! := by
  rw [vv, ite_eq_left (by rw [vparts.1]; exact hi)]

theorem vv_injective
    {i j : ℕ} (hi : i < N) (hj : j < N) (h : vv i = vv j) : i = j := by
  rw [vv_of_lt hi, vv_of_lt hj] at h
  have hi' := vparts.2.2.2 i hi
  have hj' := vparts.2.2.2 j hj
  have e := vecOf_inj hi'.1 hj'.1 h
  rw [← hi'.2.1, ← hj'.2.1, e]

theorem mA_vv {i : ℕ} (hi : i < N) :
    ap vectorOrbit.alpha i < N ∧ mA *ᵥ vv i = vv (ap vectorOrbit.alpha i) := by
  obtain ⟨hc, -, hlt, he, -, -⟩ := vparts.2.2.2 i hi
  refine ⟨hlt, ?_⟩
  rw [vv_of_lt hi, vv_of_lt hlt, he, ← toMat_rowsA]
  unfold colsA
  exact (vecOf_mulVecT rowsA (wf_of_canon154 hc)).symm

theorem mB_vv {i : ℕ} (hi : i < N) :
    ap vectorOrbit.beta i < N ∧ mB *ᵥ vv i = vv (ap vectorOrbit.beta i) := by
  obtain ⟨hc, -, -, -, hlt, he⟩ := vparts.2.2.2 i hi
  refine ⟨hlt, ?_⟩
  rw [vv_of_lt hi, vv_of_lt hlt, he, ← toMat_rowsB]
  unfold colsB
  exact (vecOf_mulVecT rowsB (wf_of_canon154 hc)).symm

theorem lookup_eq {f : ℕ → Vec} {m : ℕ} (hf : ∀ i < m, ∀ j < m, f i = f j → i = j) {k : ℕ}
    (hk : k < m) : lookup f m (f k) = k := by
  classical
  have hex : ∃ j, j < m ∧ f j = f k := ⟨k, hk, rfl⟩
  rw [lookup, dite_eq_left hex]
  have hs := Nat.find_spec hex
  exact hf _ hs.1 k hk hs.2

theorem lookup_lt {f : ℕ → Vec} {m : ℕ} (hm : 0 < m) (w : Vec) : lookup f m w < m := by
  classical
  unfold lookup
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact hm

theorem f0_eq
    {i : ℕ} (hi : i < N) : f0 i = ap vectorOrbit.alpha i := by
  rw [f0, (mA_vv hi).2]
  exact lookup_eq (fun a ha b hb h => vv_injective ha hb h) (mA_vv hi).1

theorem f1_eq
    {i : ℕ} (hi : i < N) : f1 i = ap vectorOrbit.beta i := by
  rw [f1, (mB_vv hi).2]
  exact lookup_eq (fun a ha b hb h => vv_injective ha hb h) (mB_vv hi).1

theorem f0_lt
    {i : ℕ} (hi : i < N) : f0 i < N := by rw [f0_eq hi]; exact (mA_vv hi).1

theorem f1_lt
    {i : ℕ} (hi : i < N) : f1 i < N := by rw [f1_eq hi]; exact (mB_vv hi).1

theorem vv_f0 {i : ℕ} (hi : i < N) : vv (f0 i) = mA *ᵥ vv i := by
  rw [f0_eq hi]; exact (mA_vv hi).2.symm

theorem vv_f1 {i : ℕ} (hi : i < N) : vv (f1 i) = mB *ᵥ vv i := by
  rw [f1_eq hi]; exact (mB_vv hi).2.symm

theorem mA_mulVec_injective :
    Function.Injective (fun x : Vec => mA *ᵥ x) := by
  intro x y h
  have := congrArg (fun w => mA *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, mA_sq, Matrix.one_mulVec] at this
  exact this

theorem mB_mulVec_injective :
    Function.Injective (fun x : Vec => mB *ᵥ x) := by
  have h3 : mB ^ 3 * mB = 1 := by rw [← pow_succ, mB_pow]
  intro x y h
  have := congrArg (fun w => mB ^ 3 *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec] at this
  exact this

@[expose] def f0X (i : Fin N) : Fin N := ⟨f0 i % N, Nat.mod_lt _ (by norm_num)⟩

@[expose] def f1X (i : Fin N) : Fin N := ⟨f1 i % N, Nat.mod_lt _ (by norm_num)⟩

theorem f0X_val
    (i : Fin N) : (f0X i : ℕ) = f0 i := Nat.mod_eq_of_lt (f0_lt i.isLt)

theorem f1X_val
    (i : Fin N) : (f1X i : ℕ) = f1 i := Nat.mod_eq_of_lt (f1_lt i.isLt)

theorem f0X_injective :
    Function.Injective f0X := by
  intro i j h
  have h0 : f0 i = f0 j := by rw [← f0X_val, ← f0X_val, h]
  have h1 : vv (f0 i) = vv (f0 j) := by rw [h0]
  rw [vv_f0 i.isLt, vv_f0 j.isLt] at h1
  exact Fin.ext (vv_injective i.isLt j.isLt (mA_mulVec_injective h1))

theorem f1X_injective :
    Function.Injective f1X := by
  intro i j h
  have h0 : f1 i = f1 j := by rw [← f1X_val, ← f1X_val, h]
  have h1 : vv (f1 i) = vv (f1 j) := by rw [h0]
  rw [vv_f1 i.isLt, vv_f1 j.isLt] at h1
  exact Fin.ext (vv_injective i.isLt j.isLt (mB_mulVec_injective h1))

@[expose] def a0 :
    Equiv.Perm (Fin N) :=
  Equiv.ofBijective f0X (Finite.injective_iff_bijective.1 f0X_injective)

@[expose] def a1 :
    Equiv.Perm (Fin N) :=
  Equiv.ofBijective f1X (Finite.injective_iff_bijective.1 f1X_injective)

theorem a0_apply
    (i : Fin N) : (a0 i : ℕ) = f0 i := f0X_val i

theorem a1_apply
    (i : Fin N) : (a1 i : ℕ) = f1 i := f1X_val i

theorem vecOf_digitsW (s : String) :
    vecOf (digitsW s) = fun j => (((s.toList.getD j.val '0').toNat - '0'.toNat : ℕ) : ZMod 3) := by
  funext j
  obtain ⟨hp, hm⟩ := V.ofFn_lt 154 fun j => (s.toList.getD j '0').toNat - '0'.toNat
  rw [vecOf_apply, digitsW, W.toV_ofV (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num)
    (by norm_num))) (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by norm_num))),
    V.val_ofFn, ite_eq_left j.2]

theorem vecOf_root : vecOf (digitsW Data.rootDigits) = initialVector := by
  rw [vecOf_digitsW]
  rfl

theorem root_canon : canon154 (digitsW Data.rootDigits) = true := by
  have h := (vparts.2.2.2 0 (by norm_num)).1
  rwa [vectorFacts.root] at h

theorem vv_zero : vv 0 = initialVector := by
  rw [vv_of_lt (by norm_num), vectorFacts.root, vecOf_root]

theorem initialVector_ne_zero : initialVector ≠ 0 := by
  intro h
  apply vectorFacts.root_ne
  apply vecOf_inj root_canon (by decide)
  rw [vecOf_root, h]
  funext j
  simp [vecOf_apply, W.toV_zero, V.val_zero]

theorem vtree : ∀ k, 0 < k → k < N →
    (discPar nPts vectorOrbit.alpha vectorOrbit.beta)[k]! < k ∧
      (f0 (discPar nPts vectorOrbit.alpha vectorOrbit.beta)[k]! = k ∨
        f1 (discPar nPts vectorOrbit.alpha vectorOrbit.beta)[k]! = k) := by
  intro k hk0 hk
  have h := (CFSG.Sporadic.Th.allIn_eq_true.1 vectorFacts.disc) k hk0 hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hlt, hor⟩ := h
  refine ⟨hlt, ?_⟩
  rw [f0_eq (by omega), f1_eq (by omega)]
  exact hor

theorem vv_ne_zero :
    ∀ k < N, vv k ≠ 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [vv_zero]; exact initialVector_ne_zero
    · obtain ⟨hlt, hor⟩ := vtree k hpos hk
      set q := (discPar nPts vectorOrbit.alpha vectorOrbit.beta)[k]!
      have hq := ih q hlt (by omega)
      rcases hor with h | h
      · rw [← h, vv_f0 (by omega)]
        intro h0
        exact hq (mA_mulVec_injective (h0.trans (Matrix.mulVec_zero _).symm))
      · rw [← h, vv_f1 (by omega)]
        intro h0
        exact hq (mB_mulVec_injective (h0.trans (Matrix.mulVec_zero _).symm))

theorem nonzero_iff_bits {z : W} (hz : z.toV.wf = true) (j : Fin 154) :
    (vecOf z j != 0) = (z.toV.p.testBit j.val || z.toV.m.testBit j.val) := by
  have hn := V.not_both hz j.val
  rw [vecOf_apply, V.val_eq_bitVal]
  unfold bitVal
  cases hp : z.toV.p.testBit j.val <;> cases hm : z.toV.m.testBit j.val <;>
    simp_all [show (2 : ZMod 3) ≠ 0 by decide]

theorem leadIsTwo_iff {z : W} (hz : z.toV.wf = true) :
    leadIsTwo z = true ↔ leadCoord (vecOf z) = 2 := by
  have hfun : (fun j : Fin 154 => vecOf z j != 0) =
      (fun j : ℕ => z.toV.p.testBit j || z.toV.m.testBit j) ∘ Fin.val := by
    funext j
    exact nonzero_iff_bits hz j
  have hfind : (List.range 154).find? (fun j => z.toV.p.testBit j || z.toV.m.testBit j) =
      ((List.finRange 154).find? fun j => vecOf z j != 0).map Fin.val := by
    rw [hfun, ← List.find?_map, List.map_coe_finRange_eq_range]
  unfold leadIsTwo leadCoord
  simp only
  rw [hfind]
  cases hf : (List.finRange 154).find? (fun j => vecOf z j != 0) with
  | none => simp only [Option.map_none, Option.elim_none]; decide
  | some j =>
    have hj := List.find?_some hf
    rw [nonzero_iff_bits hz j] at hj
    have hn := V.not_both hz j.val
    simp only [Option.map_some, Option.elim_some]
    rw [vecOf_apply, V.val_eq_bitVal]
    unfold bitVal
    cases hp : z.toV.p.testBit j.val <;> cases hm : z.toV.m.testBit j.val <;>
      simp_all [show (1 : ZMod 3) ≠ 2 by decide]

theorem vecOf_nuW {z : W} (hz : z.toV.wf = true) : vecOf (nuW z) = normalize (vecOf z) := by
  unfold nuW normalize
  by_cases h : leadIsTwo z = true
  · rw [ite_eq_left h, ite_eq_left ((leadIsTwo_iff hz).1 h), vecOf_neg hz]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((leadIsTwo_iff hz).2 h'))]

abbrev piT : Array ℕ := piTab vectorOrbit posU

abbrev sigmaT : Array ℕ := sigmaTab vectorOrbit posV

abbrev preT : Array ℕ := piPre nL piT

theorem lparts :
    lineOrbit.keys.size = nL ∧ lineOrbit.alpha.size = nL ∧
    lineOrbit.beta.size = nL ∧
    ∀ j < nL, canon154 lineOrbit.keys[j]! = true ∧ posU lineOrbit.keys[j]! = j ∧
      nuW lineOrbit.keys[j]! = lineOrbit.keys[j]! ∧ ¬ lineOrbit.keys[j]! = W.zero ∧
      ap lineOrbit.alpha j < nL ∧
      lineOrbit.keys[ap lineOrbit.alpha j]! = nuW (mulVecT colsA lineOrbit.keys[j]!) ∧
      ap lineOrbit.beta j < nL ∧
      lineOrbit.keys[ap lineOrbit.beta j]! = nuW (mulVecT colsB lineOrbit.keys[j]!) := by
  have h := lineFacts.lines
  unfold linesOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := h
  refine ⟨h1, h2, h3, fun j hj => ?_⟩
  have := CFSG.Sporadic.Th.parAll_eq_true h4 j hj
  simp only [lineCheckAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := this
  exact ⟨h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem pparts :
    ∀ i < N, piT[i]! < nL ∧ lineOrbit.keys[piT[i]!]! = nuW vectorOrbit.keys[i]! ∧
    sigmaT[i]! < N ∧ vectorOrbit.keys[sigmaT[i]!]! = vectorOrbit.keys[i]!.neg ∧
    sigmaT[sigmaT[i]!]! = i ∧ sigmaT[i]! ≠ i ∧ piT[sigmaT[i]!]! = piT[i]! ∧
    piT[ap vectorOrbit.alpha i]! = ap lineOrbit.alpha piT[i]! ∧
    piT[ap vectorOrbit.beta i]! = ap lineOrbit.beta piT[i]! := by
  have h := lineFacts.lines
  unfold linesOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, h5⟩, -⟩ := h
  intro i hi
  have := (CFSG.Sporadic.Th.allIn_eq_true.1 h5) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := this
  exact ⟨h1, h2, h3, h4, h6, h7, h8, h9, h10⟩

theorem preparts : ∀ j < nL, preT[j]! < N ∧ piT[preT[j]!]! = j := by
  have h := lineFacts.lines
  unfold linesOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, h6⟩ := h
  intro j hj
  have := (CFSG.Sporadic.Th.allIn_eq_true.1 h6) j (Nat.zero_le _) hj
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this

theorem uu_of_lt
    {j : ℕ} (hj : j < nL) : uu j = vecOf lineOrbit.keys[j]! := by
  rw [uu, ite_eq_left (by rw [lparts.1]; exact hj)]

theorem uu_injective
    {j k : ℕ} (hj : j < nL) (hk : k < nL) (h : uu j = uu k) : j = k := by
  rw [uu_of_lt hj, uu_of_lt hk] at h
  have hj' := lparts.2.2.2 j hj
  have hk' := lparts.2.2.2 k hk
  have e := vecOf_inj hj'.1 hk'.1 h
  rw [← hj'.2.1, ← hk'.2.1, e]

theorem lkeys_wf
    {j : ℕ} (hj : j < nL) : lineOrbit.keys[j]!.toV.wf = true :=
  wf_of_canon154 (lparts.2.2.2 j hj).1

theorem uu_normalize
    {j : ℕ} (hj : j < nL) : normalize (uu j) = uu j := by
  rw [uu_of_lt hj, ← vecOf_nuW (lkeys_wf hj), (lparts.2.2.2 j hj).2.2.1]

theorem uu_ne_zero {j : ℕ} (hj : j < nL) : uu j ≠ 0 := by
  rw [uu_of_lt hj]
  intro h
  apply (lparts.2.2.2 j hj).2.2.2.1
  apply vecOf_inj (lparts.2.2.2 j hj).1 (by decide)
  rw [h]
  funext t
  simp [vecOf_apply, W.toV_zero, V.val_zero]

theorem nuA_uu {j : ℕ} (hj : j < nL) :
    ap lineOrbit.alpha j < nL ∧ normalize (mA *ᵥ uu j) = uu (ap lineOrbit.alpha j) := by
  obtain ⟨hc, -, -, -, hlt, he, -, -⟩ := lparts.2.2.2 j hj
  refine ⟨hlt, ?_⟩
  have hw : (mulVecT colsA lineOrbit.keys[j]!).toV.wf = true := by
    unfold mulVecT colsA
    exact wf_combW (by rw [toVM_transpose_map_ofV]; exact RowsWF.transpose 154 rowsA)
      (wf_of_canon154 hc)
  rw [uu_of_lt hj, uu_of_lt hlt, he, vecOf_nuW hw, ← toMat_rowsA]
  unfold colsA
  rw [vecOf_mulVecT rowsA (wf_of_canon154 hc)]

theorem nuB_uu {j : ℕ} (hj : j < nL) :
    ap lineOrbit.beta j < nL ∧ normalize (mB *ᵥ uu j) = uu (ap lineOrbit.beta j) := by
  obtain ⟨hc, -, -, -, -, -, hlt, he⟩ := lparts.2.2.2 j hj
  refine ⟨hlt, ?_⟩
  have hw : (mulVecT colsB lineOrbit.keys[j]!).toV.wf = true := by
    unfold mulVecT colsB
    exact wf_combW (by rw [toVM_transpose_map_ofV]; exact RowsWF.transpose 154 rowsB)
      (wf_of_canon154 hc)
  rw [uu_of_lt hj, uu_of_lt hlt, he, vecOf_nuW hw, ← toMat_rowsB]
  unfold colsB
  rw [vecOf_mulVecT rowsB (wf_of_canon154 hc)]

theorem l0_eq
    {j : ℕ} (hj : j < nL) : l0 j = ap lineOrbit.alpha j := by
  rw [l0, (nuA_uu hj).2]
  exact lookup_eq (fun a ha b hb h => uu_injective ha hb h) (nuA_uu hj).1

theorem l1_eq
    {j : ℕ} (hj : j < nL) : l1 j = ap lineOrbit.beta j := by
  rw [l1, (nuB_uu hj).2]
  exact lookup_eq (fun a ha b hb h => uu_injective ha hb h) (nuB_uu hj).1

theorem vv_wf
    {i : ℕ} (hi : i < N) : vectorOrbit.keys[i]!.toV.wf = true := vkeys_wf hi

theorem uu_piT
    {i : ℕ} (hi : i < N) : uu piT[i]! = normalize (vv i) := by
  rw [uu_of_lt (pparts i hi).1, (pparts i hi).2.1, vecOf_nuW (vkeys_wf hi), vv_of_lt hi]

theorem piMap_eq {i : ℕ} (hi : i < N) : piMap i = piT[i]! := by
  rw [piMap, ← uu_piT hi]
  exact lookup_eq (fun a ha b hb h => uu_injective ha hb h) (pparts i hi).1

theorem vv_sigmaT {i : ℕ} (hi : i < N) : vv sigmaT[i]! = -vv i := by
  rw [vv_of_lt (pparts i hi).2.2.1, (pparts i hi).2.2.2.1, vecOf_neg (vkeys_wf hi), vv_of_lt hi]

theorem sigmaMap_eq
    {i : ℕ} (hi : i < N) : sigmaMap i = sigmaT[i]! := by
  rw [sigmaMap, ← vv_sigmaT hi]
  exact lookup_eq (fun a ha b hb h => vv_injective ha hb h) (pparts i hi).2.2.1

theorem l0_lt
    {j : ℕ} (hj : j < nL) : l0 j < nL := by rw [l0_eq hj]; exact (nuA_uu hj).1

theorem l1_lt
    {j : ℕ} (hj : j < nL) : l1 j < nL := by rw [l1_eq hj]; exact (nuB_uu hj).1

theorem uu_l0
    {j : ℕ} (hj : j < nL) : uu (l0 j) = normalize (mA *ᵥ uu j) := by
  rw [l0_eq hj]; exact (nuA_uu hj).2.symm

theorem uu_l1
    {j : ℕ} (hj : j < nL) : uu (l1 j) = normalize (mB *ᵥ uu j) := by
  rw [l1_eq hj]; exact (nuB_uu hj).2.symm

theorem eq_of_normalize_eq {u w : Vec} (hw : w ≠ 0) (hu' : normalize u = u)
    (hw' : normalize w = w) {c : ZMod 3} (hc : c ≠ 0) (h : u = c • w) : u = w := by
  rw [← hu', ← hw', h, (normalize_spec hw).2.2 c hc]

theorem mulVec_ne_zero_of_injective {C : Matrix (Fin 154) (Fin 154) (ZMod 3)}
    (hC : Function.Injective (fun x : Vec => C *ᵥ x)) {x : Vec} (hx : x ≠ 0) : C *ᵥ x ≠ 0 :=
  fun h => hx (hC (h.trans (Matrix.mulVec_zero C).symm))

theorem normalize_mulVec_inj {C : Matrix (Fin 154) (Fin 154) (ZMod 3)}
    (hC : Function.Injective (fun x : Vec => C *ᵥ x)) {u w : Vec} (hu : u ≠ 0) (hw : w ≠ 0)
    (hu' : normalize u = u) (hw' : normalize w = w)
    (h : normalize (C *ᵥ u) = normalize (C *ᵥ w)) : u = w := by
  obtain ⟨c, hc, hcu⟩ := (normalize_spec (mulVec_ne_zero_of_injective hC hu)).1
  obtain ⟨d, hd, hdw⟩ := (normalize_spec (mulVec_ne_zero_of_injective hC hw)).1
  rw [hcu, hdw] at h
  have h2 : C *ᵥ u = C *ᵥ ((c⁻¹ * d) • w) := by
    rw [Matrix.mulVec_smul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact eq_of_normalize_eq hw hu' hw' (mul_ne_zero (inv_ne_zero hc) hd) (hC h2)

@[expose] def l0Y (j : Fin nL) : Fin nL := ⟨l0 j % nL, Nat.mod_lt _ (by norm_num)⟩

@[expose] def l1Y (j : Fin nL) : Fin nL := ⟨l1 j % nL, Nat.mod_lt _ (by norm_num)⟩

theorem l0Y_val
    (j : Fin nL) : (l0Y j : ℕ) = l0 j := Nat.mod_eq_of_lt (l0_lt j.isLt)

theorem l1Y_val
    (j : Fin nL) : (l1Y j : ℕ) = l1 j := Nat.mod_eq_of_lt (l1_lt j.isLt)

theorem l0Y_injective :
    Function.Injective l0Y := by
  intro j k h
  have h0 : l0 j = l0 k := by rw [← l0Y_val, ← l0Y_val, h]
  have h1 : uu (l0 j) = uu (l0 k) := by rw [h0]
  rw [uu_l0 j.isLt, uu_l0 k.isLt] at h1
  exact Fin.ext (uu_injective j.isLt k.isLt (normalize_mulVec_inj mA_mulVec_injective
    (uu_ne_zero j.isLt) (uu_ne_zero k.isLt) (uu_normalize j.isLt) (uu_normalize k.isLt) h1))

theorem l1Y_injective :
    Function.Injective l1Y := by
  intro j k h
  have h0 : l1 j = l1 k := by rw [← l1Y_val, ← l1Y_val, h]
  have h1 : uu (l1 j) = uu (l1 k) := by rw [h0]
  rw [uu_l1 j.isLt, uu_l1 k.isLt] at h1
  exact Fin.ext (uu_injective j.isLt k.isLt (normalize_mulVec_inj mB_mulVec_injective
    (uu_ne_zero j.isLt) (uu_ne_zero k.isLt) (uu_normalize j.isLt) (uu_normalize k.isLt) h1))

@[expose] def d0 :
    Equiv.Perm (Fin nL) :=
  Equiv.ofBijective l0Y (Finite.injective_iff_bijective.1 l0Y_injective)

@[expose] def d1 :
    Equiv.Perm (Fin nL) :=
  Equiv.ofBijective l1Y (Finite.injective_iff_bijective.1 l1Y_injective)

theorem d0_apply
    (j : Fin nL) : (d0 j : ℕ) = l0 j := l0Y_val j

theorem d1_apply
    (j : Fin nL) : (d1 j : ℕ) = l1 j := l1Y_val j

theorem piMap_lt
    {i : ℕ} (hi : i < N) : piMap i < nL := by rw [piMap_eq hi]; exact (pparts i hi).1

theorem sigmaMap_lt {i : ℕ} (hi : i < N) : sigmaMap i < N := by
  rw [sigmaMap_eq hi]; exact (pparts i hi).2.2.1

theorem uu_piMap
    {i : ℕ} (hi : i < N) : uu (piMap i) = normalize (vv i) := by
  rw [piMap_eq hi]; exact uu_piT hi

theorem vv_sigmaMap
    {i : ℕ} (hi : i < N) : vv (sigmaMap i) = -vv i := by
  rw [sigmaMap_eq hi]; exact vv_sigmaT hi

theorem sigmaMap_sigmaMap
    {i : ℕ} (hi : i < N) : sigmaMap (sigmaMap i) = i := by
  rw [sigmaMap_eq hi, sigmaMap_eq (pparts i hi).2.2.1]; exact (pparts i hi).2.2.2.2.1

theorem sigmaMap_ne {i : ℕ} (hi : i < N) : sigmaMap i ≠ i := by
  rw [sigmaMap_eq hi]; exact (pparts i hi).2.2.2.2.2.1

theorem piMap_sigmaMap
    {i : ℕ} (hi : i < N) : piMap (sigmaMap i) = piMap i := by
  rw [piMap_eq (sigmaMap_lt hi), sigmaMap_eq hi, piMap_eq hi]
  exact (pparts i hi).2.2.2.2.2.2.1

theorem piMap_f0
    {i : ℕ} (hi : i < N) : piMap (f0 i) = l0 (piMap i) := by
  rw [piMap_eq (f0_lt hi), f0_eq hi, piMap_eq hi, l0_eq (pparts i hi).1]
  exact (pparts i hi).2.2.2.2.2.2.2.1

theorem piMap_f1
    {i : ℕ} (hi : i < N) : piMap (f1 i) = l1 (piMap i) := by
  rw [piMap_eq (f1_lt hi), f1_eq hi, piMap_eq hi, l1_eq (pparts i hi).1]
  exact (pparts i hi).2.2.2.2.2.2.2.2

theorem piMap_zero : piMap 0 = 0 := by
  have h0 : uu 0 = normalize (vv 0) := by
    rw [uu_of_lt (by norm_num), lineFacts.root, vecOf_nuW (wf_of_canon154 root_canon),
      vecOf_root, vv_zero]
  rw [piMap, ← h0]
  exact lookup_eq (fun a ha b hb h => uu_injective ha hb h) (by norm_num)

theorem piMap_eq_iff
    {i k : ℕ} (hi : i < N) (hk : k < N) :
    piMap i = piMap k ↔ i = k ∨ i = sigmaMap k := by
  constructor
  · intro h
    have h1 : normalize (vv i) = normalize (vv k) := by rw [← uu_piMap hi, ← uu_piMap hk, h]
    obtain ⟨c, hc, hci⟩ := (normalize_spec (vv_ne_zero i hi)).1
    obtain ⟨d, hd, hdk⟩ := (normalize_spec (vv_ne_zero k hk)).1
    rw [hci, hdk] at h1
    have h2 : vv i = (c⁻¹ * d) • vv k := by
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rcases zmod3_ne_zero (mul_ne_zero (inv_ne_zero hc) hd) with h3 | h3
    · left
      rw [h3, one_smul] at h2
      exact vv_injective hi hk h2
    · right
      apply vv_injective hi (sigmaMap_lt hk)
      rw [vv_sigmaMap hk, h2, h3]
      funext t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      generalize vv k t = x
      revert x
      decide
  · rintro (h | h)
    · rw [h]
    · rw [h]
      exact piMap_sigmaMap hk

@[expose] def piX (i : Fin N) : Fin nL := ⟨piMap i % nL, Nat.mod_lt _ (by norm_num)⟩

theorem piX_val
    (i : Fin N) : (piX i : ℕ) = piMap i := Nat.mod_eq_of_lt (piMap_lt i.isLt)

theorem piX_surjective : Function.Surjective piX := by
  intro j
  obtain ⟨hlt, hpre⟩ := preparts j j.isLt
  refine ⟨⟨_, hlt⟩, Fin.ext ?_⟩
  rw [piX_val, piMap_eq hlt, hpre]

@[expose] def sigmaX (i : Fin N) : Fin N := ⟨sigmaMap i % N, Nat.mod_lt _ (by norm_num)⟩

theorem sigmaX_val (i : Fin N) : (sigmaX i : ℕ) = sigmaMap i :=
  Nat.mod_eq_of_lt (sigmaMap_lt i.isLt)

theorem piX_fiber_card (j : Fin nL) :
    (Finset.univ.filter fun i : Fin N => piX i = j).card = 2 := by
  obtain ⟨k, hk⟩ := piX_surjective j
  have hs : (Finset.univ.filter fun i : Fin N => piX i = j) = {k, sigmaX k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [← hk, Fin.ext_iff, piX_val, piX_val, piMap_eq_iff i.isLt k.isLt, Fin.ext_iff,
      Fin.ext_iff, sigmaX_val]
  rw [hs, Finset.card_pair]
  intro h
  have h1 := congrArg Fin.val h
  rw [sigmaX_val] at h1
  exact sigmaMap_ne k.isLt h1.symm

theorem spanIdx_size : Data.spanIdx.size = 154 := by
  have h := vectorFacts.basis
  unfold basisOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem spanIndex_lt (k : Fin 154) : spanIndex k < N := by
  have h := vectorFacts.basis
  unfold basisOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  have := h.1.2 k.val (by rw [spanIdx_size]; exact k.isLt)
  rw [spanIndex, getElem!_pos Data.spanIdx k.val (by rw [spanIdx_size]; exact k.isLt)]
  exact this

theorem toMat_spanInv : toMat 154 (rowsOf 154 Data.spanInvPayload) = spanningBasisInverse :=
  toMat_rowsOf 154 _

theorem spanRows_getElem (k : Fin 154) :
    (spanRows vectorOrbit Data.spanIdx)[k.val]! = vectorOrbit.keys[spanIndex k]! := by
  have hk : k.val < Data.spanIdx.size := by rw [spanIdx_size]; exact k.isLt
  rw [spanRows, getElem!_pos _ k.val (by rw [Array.size_map]; exact hk), Array.getElem_map,
    spanIndex, getElem!_pos Data.spanIdx k.val hk]

theorem toMat_spanRows :
    toMat 154 (toVM (spanRows vectorOrbit Data.spanIdx)) = basisMatrixᵀ := by
  ext t r
  rw [toMat_apply, toVM_getElem!, spanRows_getElem, Matrix.transpose_apply, basisMatrix,
    Matrix.of_apply, vv_of_lt (spanIndex_lt t)]
  rfl

theorem rowsWF_spanRows :
    RowsWF (toVM (spanRows vectorOrbit Data.spanIdx)) := by
  intro t
  rw [toVM_getElem!]
  by_cases ht : t < 154
  · have := spanRows_getElem ⟨t, ht⟩
    simp only at this
    rw [this]
    exact vkeys_wf (spanIndex_lt _)
  · rw [getElem!_neg _ t (by rw [spanRows, Array.size_map, spanIdx_size]; exact ht),
      W.toV_default]
    exact V.wf_zero

theorem mul_eq_one_symm {d K : Type*} [Fintype d] [DecidableEq d] [Field K]
    {A B : Matrix d d K} (h : A * B = 1) : B * A = 1 :=
  mul_eq_one_comm.1 h

theorem basis_mul : basisMatrix * spanningBasisInverse = 1 ∧
    spanningBasisInverse * basisMatrix = 1 := by
  have h := vectorFacts.basis
  unfold basisOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have e := congrArg (fun Y => toMat 154 (toVM Y)) h.2
  rw [toVM_mulW, toVM_idW (by norm_num), toMat_idM, toVM_transpose_map_ofV,
    toMat_mul (by simp [F3.Native.transpose]) (RowsWF.transpose 154 _) rowsWF_spanRows,
    toMat_transpose, toMat_spanInv, toMat_spanRows, ← Matrix.transpose_mul] at e
  have e1 : basisMatrix * spanningBasisInverse = 1 := by
    have := congrArg Matrix.transpose e
    rwa [Matrix.transpose_transpose, Matrix.transpose_one] at this
  exact ⟨e1, mul_eq_one_symm e1⟩

abbrev vset : Set Vec := vv '' Set.Iio N

theorem smul_vec' (g : J) (w : Vec) : g • w = mat g *ᵥ w := rfl

theorem smul_mem_vset
    (g : J) : ∀ w ∈ vset, g • w ∈ vset := by
  refine CFSG.Sporadic.Th.smul_mem_of_closure closure_gab ((Set.finite_Iio N).image _) ?_ ?_ g
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨f0 i, f0_lt hi, by rw [smul_vec', mat_ga, vv_f0 hi]⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨f1 i, f1_lt hi, by rw [smul_vec', mat_gb, vv_f1 hi]⟩

@[expose] def vsub :
    SubMulAction J Vec where
  carrier := vset
  smul_mem' g _ hw := smul_mem_vset g _ hw

@[expose] def vequiv : Fin N ≃ vsub :=
  Equiv.ofBijective (fun i => ⟨vv i, ⟨i, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (vv_injective i.isLt j.isLt (congrArg Subtype.val h)), by
      rintro ⟨w, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi⟩, rfl⟩⟩

@[expose, instance_reducible] def vAction :
    MulAction J (Fin N) := vequiv.mulAction J

@[expose] def phiV :
    J →* Equiv.Perm (Fin N) := @MulAction.toPermHom J (Fin N) _ vAction

theorem vequiv_val
    (i : Fin N) : (vequiv i : Vec) = vv i := rfl

theorem vequiv_phiV
    (g : J) (i : Fin N) : vequiv (phiV g i) = g • vequiv i := by
  show vequiv (vequiv.symm (g • vequiv i)) = g • vequiv i
  rw [Equiv.apply_symm_apply]

theorem vv_phiV
    (g : J) (i : Fin N) : vv (phiV g i) = mat g *ᵥ vv i := by
  have h1 := congrArg Subtype.val (vequiv_phiV g i)
  rwa [vequiv_val, SubMulAction.val_smul, vequiv_val, smul_vec'] at h1

theorem phiV_eq_of_vv
    {g : J} {i j : Fin N} (h : mat g *ᵥ vv i = vv j) : phiV g i = j :=
  Fin.ext (vv_injective (phiV g i).isLt j.isLt (by rw [vv_phiV, h]))

theorem phiV_ga : phiV ga = a0 := by
  ext i
  rw [phiV_eq_of_vv (j := a0 i) (by rw [mat_ga, a0_apply, vv_f0 i.isLt])]

theorem phiV_gb : phiV gb = a1 := by
  ext i
  rw [phiV_eq_of_vv (j := a1 i) (by rw [mat_gb, a1_apply, vv_f1 i.isLt])]

@[expose] def Pv :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.closure {a0, a1}

theorem range_phiV :
    phiV.range = Pv := by
  rw [MonoidHom.range_eq_map, ← closure_gab, MonoidHom.map_closure, Pv, Set.image_pair,
    phiV_ga, phiV_gb]

theorem phiV_injective :
    Function.Injective phiV := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply mat_injective
  rw [mat_one, ← one_smul (ZMod 3) (1 : Matrix (Fin 154) (Fin 154) (ZMod 3))]
  have hXU : spanningBasisInverseᵀ * basisMatrixᵀ = 1 := by
    rw [← Matrix.transpose_mul, basis_mul.1, Matrix.transpose_one]
  apply eq_smul_one_of_rows hXU
  intro t
  have hrow : basisMatrixᵀ t = vv (spanIndex t) := by
    funext r
    rfl
  rw [hrow, one_smul]
  have := vv_phiV g ⟨spanIndex t % N, Nat.mod_lt _ (by norm_num)⟩
  rw [hg, Equiv.Perm.coe_one, id_eq] at this
  simp only [Nat.mod_eq_of_lt (spanIndex_lt t)] at this
  exact this.symm

@[expose] def jEquivPv : J ≃* Pv :=
  (MonoidHom.ofInjective phiV_injective).trans (MulEquiv.subgroupCongr range_phiV)

theorem jEquivPv_apply
    (g : J) : (jEquivPv g : Equiv.Perm (Fin N)) = phiV g := rfl

@[expose] def onEquivPv :
    Blueprint.NativeSporadic.ON ≃* Pv := onEquivJ.trans jEquivPv

abbrev LineRep : Type := {w : Vec // w ≠ 0 ∧ normalize w = w}

theorem mat_mulVec_injective
    (g : J) : Function.Injective (fun x : Vec => mat g *ᵥ x) := by
  intro x y h
  have := congrArg (fun w => mat g⁻¹ *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec] at this
  exact this

theorem normalize_ne_zero {z : Vec} (hz : z ≠ 0) : normalize z ≠ 0 := by
  obtain ⟨c, hc, he⟩ := (normalize_spec hz).1
  rw [he]
  exact smul_ne_zero hc hz

theorem normalize_normalize (z : Vec) : normalize (normalize z) = normalize z := by
  by_cases hz : z = 0
  · rw [hz, normalize_zero, normalize_zero]
  · obtain ⟨c, hc, he⟩ := (normalize_spec hz).1
    conv_lhs => rw [he]
    exact (normalize_spec hz).2.2 c hc

@[expose] def lineSmul (g : J) (w : LineRep) : LineRep :=
  ⟨normalize (mat g *ᵥ w.1), normalize_ne_zero (mulVec_ne_zero_of_injective
    (mat_mulVec_injective g) w.2.1), normalize_normalize _⟩

theorem lineSmul_val'
    (g : J) (w : LineRep) : (lineSmul g w).1 = normalize (mat g *ᵥ w.1) :=
  rfl

theorem lineSmul_one (w : LineRep) : lineSmul 1 w = w := by
  apply Subtype.ext
  rw [lineSmul_val', mat_one, Matrix.one_mulVec, w.2.2]

theorem lineSmul_mul (g h : J) (w : LineRep) :
    lineSmul (g * h) w = lineSmul g (lineSmul h w) := by
  apply Subtype.ext
  rw [lineSmul_val', lineSmul_val', lineSmul_val']
  have hne := mulVec_ne_zero_of_injective (mat_mulVec_injective h) w.2.1
  obtain ⟨c, hc, he⟩ := (normalize_spec hne).1
  rw [he, Matrix.mulVec_smul, (normalize_spec (mulVec_ne_zero_of_injective
    (mat_mulVec_injective g) hne)).2.2 c hc, mat_mul, Matrix.mulVec_mulVec]

@[expose, instance_reducible] def lineAction :
    MulAction J LineRep where
  smul := lineSmul
  one_smul := lineSmul_one
  mul_smul := lineSmul_mul

attribute [local instance] lineAction

theorem lineSmul_val
    (g : J) (w : LineRep) : ((g • w : LineRep) : Vec) =
    normalize (mat g *ᵥ w.1) := rfl

@[expose] def uRep
    (j : Fin nL) : LineRep := ⟨uu j, uu_ne_zero j.isLt, uu_normalize j.isLt⟩

abbrev lset : Set LineRep := Set.range uRep

theorem uRep_l0
    (j : Fin nL) : ga • uRep j = uRep (d0 j) := by
  apply Subtype.ext
  rw [lineSmul_val, mat_ga]
  show normalize (mA *ᵥ uu j) = uu (d0 j)
  rw [d0_apply, uu_l0 j.isLt]

theorem uRep_l1
    (j : Fin nL) : gb • uRep j = uRep (d1 j) := by
  apply Subtype.ext
  rw [lineSmul_val, mat_gb]
  show normalize (mB *ᵥ uu j) = uu (d1 j)
  rw [d1_apply, uu_l1 j.isLt]

theorem smul_mem_lset
    (g : J) : ∀ w ∈ lset, g • w ∈ lset := by
  refine CFSG.Sporadic.Th.smul_mem_of_closure closure_gab (Set.finite_range _) ?_ ?_ g
  · rintro w ⟨j, rfl⟩
    exact ⟨d0 j, (uRep_l0 j).symm⟩
  · rintro w ⟨j, rfl⟩
    exact ⟨d1 j, (uRep_l1 j).symm⟩

@[expose] def lsub :
    SubMulAction J LineRep where
  carrier := lset
  smul_mem' g _ hw := smul_mem_lset g _ hw

@[expose] def lequiv :
    Fin nL ≃ lsub :=
  Equiv.ofBijective (fun j => ⟨uRep j, ⟨j, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (uu_injective i.isLt j.isLt
      (congrArg (fun w : lsub => (w : LineRep).1) h)), by
      rintro ⟨w, ⟨j, rfl⟩⟩
      exact ⟨j, rfl⟩⟩

@[expose, instance_reducible] def lAction :
    MulAction J (Fin nL) := lequiv.mulAction J

@[expose] def phiL :
    J →* Equiv.Perm (Fin nL) := @MulAction.toPermHom J (Fin nL) _ lAction

theorem lequiv_val
    (j : Fin nL) : ((lequiv j : LineRep) : Vec) = uu j := rfl

theorem lequiv_phiL
    (g : J) (j : Fin nL) : lequiv (phiL g j) = g • lequiv j := by
  show lequiv (lequiv.symm (g • lequiv j)) = g • lequiv j
  rw [Equiv.apply_symm_apply]

theorem uu_phiL
    (g : J) (j : Fin nL) : uu (phiL g j) = normalize (mat g *ᵥ uu j) := by
  have h1 := congrArg (fun w : lsub => (w : LineRep).1) (lequiv_phiL g j)
  rwa [lequiv_val, SubMulAction.val_smul, lineSmul_val, lequiv_val] at h1

theorem phiL_eq_of_uu
    {g : J} {i j : Fin nL} (h : normalize (mat g *ᵥ uu i) = uu j) :
    phiL g i = j :=
  Fin.ext (uu_injective (phiL g i).isLt j.isLt (by rw [uu_phiL, h]))

theorem phiL_ga : phiL ga = d0 := by
  ext j
  rw [phiL_eq_of_uu (j := d0 j) (by rw [mat_ga, d0_apply, uu_l0 j.isLt])]

theorem phiL_gb : phiL gb = d1 := by
  ext j
  rw [phiL_eq_of_uu (j := d1 j) (by rw [mat_gb, d1_apply, uu_l1 j.isLt])]

@[expose] def Pl :
    Subgroup (Equiv.Perm (Fin nL)) := Subgroup.closure {d0, d1}

theorem range_phiL :
    phiL.range = Pl := by
  rw [MonoidHom.range_eq_map, ← closure_gab, MonoidHom.map_closure, Pl, Set.image_pair,
    phiL_ga, phiL_gb]

theorem a0_mem :
    a0 ∈ Pv := Subgroup.subset_closure (Set.mem_insert _ _)

theorem a1_mem :
    a1 ∈ Pv := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem exists_pv_zero :
    ∀ k < N, ∃ g ∈ Pv, (g ⟨0, by norm_num⟩ : ℕ) = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, one_mem _, rfl⟩
    · obtain ⟨hlt, hor⟩ := vtree k hpos hk
      obtain ⟨g, hg, hgq⟩ := ih _ hlt (by omega)
      rcases hor with h | h
      · refine ⟨a0 * g, mul_mem a0_mem hg, ?_⟩
        rw [Equiv.Perm.mul_apply, a0_apply, hgq, h]
      · refine ⟨a1 * g, mul_mem a1_mem hg, ?_⟩
        rw [Equiv.Perm.mul_apply, a1_apply, hgq, h]

theorem pv_transitive
    (i j : Fin N) : ∃ g ∈ Pv, g i = j := by
  obtain ⟨g, hg, hgi⟩ := exists_pv_zero i i.isLt
  obtain ⟨h, hh, hhj⟩ := exists_pv_zero j j.isLt
  refine ⟨h * g⁻¹, mul_mem hh (inv_mem hg), ?_⟩
  have hgi' : g ⟨0, by norm_num⟩ = i := Fin.ext hgi
  rw [Equiv.Perm.mul_apply, ← hgi', Equiv.Perm.inv_def, Equiv.symm_apply_apply, Fin.ext_iff]
  exact hhj

theorem ltree : ∀ k, 0 < k → k < nL →
    (discPar nL lineOrbit.alpha lineOrbit.beta)[k]! < k ∧
      (l0 (discPar nL lineOrbit.alpha lineOrbit.beta)[k]! = k ∨
        l1 (discPar nL lineOrbit.alpha lineOrbit.beta)[k]! = k) := by
  intro k hk0 hk
  have h := (CFSG.Sporadic.Th.allIn_eq_true.1 lineFacts.disc) k hk0 hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨hlt, hor⟩ := h
  refine ⟨hlt, ?_⟩
  rw [l0_eq (by omega), l1_eq (by omega)]
  exact hor

theorem d0_mem :
    d0 ∈ Pl := Subgroup.subset_closure (Set.mem_insert _ _)

theorem d1_mem :
    d1 ∈ Pl := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem exists_pl_zero :
    ∀ k < nL, ∃ g ∈ Pl, (g ⟨0, by norm_num⟩ : ℕ) = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, one_mem _, rfl⟩
    · obtain ⟨hlt, hor⟩ := ltree k hpos hk
      obtain ⟨g, hg, hgq⟩ := ih _ hlt (by omega)
      rcases hor with h | h
      · refine ⟨d0 * g, mul_mem d0_mem hg, ?_⟩
        rw [Equiv.Perm.mul_apply, d0_apply, hgq, h]
      · refine ⟨d1 * g, mul_mem d1_mem hg, ?_⟩
        rw [Equiv.Perm.mul_apply, d1_apply, hgq, h]

theorem pl_transitive
    (i j : Fin nL) : ∃ g ∈ Pl, g i = j := by
  obtain ⟨g, hg, hgi⟩ := exists_pl_zero i i.isLt
  obtain ⟨h, hh, hhj⟩ := exists_pl_zero j j.isLt
  refine ⟨h * g⁻¹, mul_mem hh (inv_mem hg), ?_⟩
  have hgi' : g ⟨0, by norm_num⟩ = i := Fin.ext hgi
  rw [Equiv.Perm.mul_apply, ← hgi', Equiv.Perm.inv_def, Equiv.symm_apply_apply, Fin.ext_iff]
  exact hhj

theorem fam_on_vector_and_projective_orbit_actions :
    initialVector ≠ 0 ∧
    (vectorOrbit.keys.size = N ∧ (∀ i < N, ∀ j < N, vv i = vv j → i = j) ∧
      ∀ i < N, vv i ≠ 0) ∧
    (lineOrbit.keys.size = nL ∧ (∀ i < nL, ∀ j < nL, uu i = uu j → i = j) ∧
      ∀ j < nL, uu j ≠ 0 ∧ normalize (uu j) = uu j) ∧
    (∀ i < N, mA *ᵥ vv i = vv (f0 i) ∧ mB *ᵥ vv i = vv (f1 i)) ∧
    (∀ j < nL, normalize (mA *ᵥ uu j) = uu (l0 j) ∧ normalize (mB *ᵥ uu j) = uu (l1 j)) ∧
    (∀ i : Fin N, (a0 i : ℕ) = f0 i ∧ (a1 i : ℕ) = f1 i) ∧
    (∀ j : Fin nL, (d0 j : ℕ) = l0 j ∧ (d1 j : ℕ) = l1 j) ∧
    (basisMatrix * spanningBasisInverse = 1 ∧ spanningBasisInverse * basisMatrix = 1) ∧
    ((∀ i : Fin N, (piX i : ℕ) = piMap i) ∧ Function.Surjective piX ∧
      (∀ j : Fin nL, (Finset.univ.filter fun i : Fin N => piX i = j).card = 2) ∧
      piMap 0 = 0 ∧ (∀ i < N, uu (piMap i) = normalize (vv i)) ∧
      ∀ i < N, piMap (f0 i) = l0 (piMap i) ∧ piMap (f1 i) = l1 (piMap i)) ∧
    (∀ i < N, sigmaMap i < N ∧ sigmaMap (sigmaMap i) = i ∧ sigmaMap i ≠ i ∧
      vv (sigmaMap i) = -vv i) ∧
    (phiV ga = a0 ∧ phiV gb = a1 ∧ phiV.range = Pv ∧ ∀ g i, vv (phiV g i) = mat g *ᵥ vv i) ∧
    (phiL ga = d0 ∧ phiL gb = d1 ∧ phiL.range = Pl ∧
      ∀ g j, uu (phiL g j) = normalize (mat g *ᵥ uu j)) ∧
    (∀ i j : Fin N, ∃ g ∈ Pv, g i = j) ∧ (∀ i j : Fin nL, ∃ g ∈ Pl, g i = j) ∧
    Function.Injective phiV ∧
    ∃ e : Blueprint.NativeSporadic.ON ≃* Pv,
      ∀ u, (e u : Equiv.Perm (Fin N)) = phiV (onEquivJ u) :=
  ⟨initialVector_ne_zero,
    ⟨vparts.1, fun _ hi _ hj h => vv_injective hi hj h, vv_ne_zero⟩,
    ⟨lparts.1, fun _ hi _ hj h => uu_injective hi hj h,
      fun _ hj => ⟨uu_ne_zero hj, uu_normalize hj⟩⟩,
    fun _ hi => ⟨(vv_f0 hi).symm, (vv_f1 hi).symm⟩,
    fun _ hj => ⟨(uu_l0 hj).symm, (uu_l1 hj).symm⟩,
    fun i => ⟨a0_apply i, a1_apply i⟩, fun j => ⟨d0_apply j, d1_apply j⟩, basis_mul,
    ⟨piX_val, piX_surjective, piX_fiber_card, piMap_zero, fun _ hi => uu_piMap hi,
      fun _ hi => ⟨piMap_f0 hi, piMap_f1 hi⟩⟩,
    fun _ hi => ⟨sigmaMap_lt hi, sigmaMap_sigmaMap hi, sigmaMap_ne hi, vv_sigmaMap hi⟩,
    ⟨phiV_ga, phiV_gb, range_phiV, vv_phiV⟩, ⟨phiL_ga, phiL_gb, range_phiL, uu_phiL⟩,
    pv_transitive, pl_transitive, phiV_injective, ⟨onEquivPv, fun _ => rfl⟩⟩

end CFSG.ONSchreier
