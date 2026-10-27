module

public import CFSG.Sporadic.HNSchreier.PointStab
public import CFSG.Sporadic.HNSchreier.InvolCheck
public import CFSG.Sporadic.HNSchreier.Seeds
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.ONSchreier CFSG.ONSchreier.Native Matrix

theorem matJ_mul (g h : JH) : matJ (g * h) = matJ g * matJ h := rfl

theorem matJ_one : matJ 1 = 1 := rfl

theorem matJ_inv_mul (g : JH) : matJ g⁻¹ * matJ g = 1 := by
  rw [← matJ_mul, inv_mul_cancel, matJ_one]

theorem matJ_mul_inv (g : JH) : matJ g * matJ g⁻¹ = 1 := by
  rw [← matJ_mul, mul_inv_cancel, matJ_one]

abbrev matJHom : JH →* Matrix (Fin 133) (Fin 133) (ZMod 5) where
  toFun := matJ
  map_one' := matJ_one
  map_mul' := matJ_mul

theorem matJ_list_prod (l : List JH) : matJ l.prod = (l.map matJ).prod :=
  map_list_prod matJHom l

theorem toMat_inv_of_mulM {X Y : Array (Array ℕ)} {g : JH} (hX : toMat 5 133 X = matJ g)
    (h : mulM 5 133 X Y = idM 133) : toMat 5 133 Y = matJ g⁻¹ := by
  have e := congrArg (toMat 5 133) h
  rw [toMat_mulM, toMat_idM, hX] at e
  calc toMat 5 133 Y = (matJ g⁻¹ * matJ g) * toMat 5 133 Y := by rw [matJ_inv_mul, one_mul]
    _ = matJ g⁻¹ * (matJ g * toMat 5 133 Y) := by rw [mul_assoc]
    _ = matJ g⁻¹ := by rw [e, mul_one]

@[expose] def RegsRepM (arr : Array (Array (Array ℕ))) (g : ℕ → JH) : Prop :=
  arr.size = 11 ∧ ∀ r < 11, toMat 5 133 arr[r]! = matJ (g r)

theorem regsRepM_step {arr : Array (Array (Array ℕ))} {g : ℕ → JH} (h : RegsRepM arr g)
    {a b c : ℕ} (ha : a < 11) (hb : b < 11) (hc : c < 11) :
    RegsRepM (arr.set! c (mulM 5 133 arr[a]! arr[b]!)) (Function.update g c (g a * g b)) := by
  obtain ⟨hs, hr⟩ := h
  refine ⟨by simp [hs], fun r hr' => ?_⟩
  by_cases hrc : r = c
  · subst hrc
    rw [Function.update_self, Array.getElem!_set!_self _ _ _ (by omega), toMat_mulM, hr a ha,
      hr b hb, matJ_mul]
  · rw [Function.update_of_ne hrc, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hrc)]
    exact hr r hr'

theorem regsRepM_prog : ∀ (prog : List (ℕ × ℕ × ℕ)) (arr : Array (Array (Array ℕ)))
    (g : ℕ → JH), (∀ t ∈ prog, t.1 < 11 ∧ t.2.1 < 11 ∧ t.2.2 < 11) →
    RegsRepM arr g → RegsRepM (progRegsM arr prog) (runProg g prog)
  | [], _, _, _, h => h
  | (a, b, c) :: rest, arr, g, hp, h => by
    have ht := hp (a, b, c) (List.mem_cons_self ..)
    exact regsRepM_prog rest _ _ (fun t ht' => hp t (List.mem_cons_of_mem _ ht'))
      (regsRepM_step h ht.1 ht.2.1 ht.2.2)

theorem getElem!_triple_zero {α : Type*} [Inhabited α] (x y z : α) : #[x, y, z][0]! = x := rfl

theorem getElem!_triple_one {α : Type*} [Inhabited α] (x y z : α) : #[x, y, z][1]! = y := rfl

theorem getElem!_triple_two {α : Type*} [Inhabited α] (x y z : α) : #[x, y, z][2]! = z := rfl

theorem initRegsM_facts (A B : Array (Array ℕ)) :
    (initRegsM A B).size = 11 ∧ (initRegsM A B)[0]! = idM 133 ∧ (initRegsM A B)[1]! = A ∧
      (initRegsM A B)[2]! = B ∧ ∀ r, 3 ≤ r → r < 11 → (initRegsM A B)[r]! = idM 133 := by
  have hget : ∀ r < 3, (initRegsM A B)[r]! = #[idM 133, A, B][r]! := by
    intro r hr
    rw [initRegsM, getElem!_pos _ r (by simp; omega), Array.getElem_append_left (by simp; omega),
      getElem!_pos _ r (by simp; omega)]
  refine ⟨by simp [initRegsM], (hget 0 (by norm_num)).trans (getElem!_triple_zero _ _ _),
    (hget 1 (by norm_num)).trans (getElem!_triple_one _ _ _),
    (hget 2 (by norm_num)).trans (getElem!_triple_two _ _ _), fun r h3 h11 => ?_⟩
  rw [initRegsM, getElem!_pos _ r (by simp; omega), Array.getElem_append_right (by simp; omega)]
  simp

theorem regsRepM_init : RegsRepM (initRegsM rowsA rowsB) jRegs0 := by
  obtain ⟨hs, h0, h1, h2, h3⟩ := initRegsM_facts rowsA rowsB
  refine ⟨hs, fun r hr => ?_⟩
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · interval_cases r
    · rw [h0, toMat_idM]; rfl
    · rw [h1, toMat_rowsA, ← mat_aJ]; rfl
    · rw [h2, toMat_rowsB, ← mat_bJ]; rfl
  · rw [h3 r hr3 hr, toMat_idM]
    show 1 = matJ (if r = 1 then aJ else if r = 2 then bJ else 1)
    rw [ite_eq_right (by omega), ite_eq_right (by omega), matJ_one]

@[irreducible] def mRegs : Array (Array (Array ℕ)) :=
  progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram

theorem mRegs_eq : mRegs = progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram := by
  unfold mRegs; rfl

theorem regsM_rep : RegsRepM mRegs jRegs := by
  rw [mRegs_eq]
  exact regsRepM_prog _ _ _ prog_bounds regsRepM_init

theorem toMat_mword {S Si : Array (Array (Array ℕ))} {gs : ℕ → JH} {j : ℕ}
    (hS : ∀ h < j, toMat 5 133 S[h]! = matJ (gs h))
    (hSi : ∀ h < j, toMat 5 133 Si[h]! = matJ (gs h)⁻¹) :
    ∀ w : List ℤ, plettersOK j w = true →
      toMat 5 133 (mword S Si w) =
        matJ (Quiver.SchreierGraph.evalWord (fun h : Fin j => gs h) (ptoLetters j w))
  | [], _ => by
    rw [mword, toMat_idM]
    rfl
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    have ih := toMat_mword hS hSi w hw'
    have hcons : ptoLetters j (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        ptoLetters j w := by
      simp [ptoLetters, hl0, hlj]
    rw [mword, hcons, toMat_mulM, ih]
    by_cases hpos : 0 < l
    · rw [decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true, matJ_mul, mletter,
        ite_eq_left hpos]
      have e : l.toNat - 1 = l.natAbs - 1 := by omega
      rw [e, hS _ (by omega)]
    · rw [show decide (0 < l) = false by simpa using hpos,
        Quiver.SchreierGraph.evalWord_cons_false, matJ_mul, mletter, ite_eq_right hpos]
      have e : (-l).toNat - 1 = l.natAbs - 1 := by omega
      rw [e, hSi _ (by omega)]

theorem toMat_of_strongOKM {A0 A1 : Array (Array ℕ)} {S Si : Array (Array (Array ℕ))}
    {W : Array (List ℤ)} {g0 g1 : JH} (h : strongOKM A0 A1 S Si W = true)
    (h0 : toMat 5 133 A0 = matJ g0) (h1 : toMat 5 133 A1 = matJ g1) :
    S.size = W.size ∧ Si.size = W.size ∧ ∀ j < S.size,
      toMat 5 133 S[j]! = matJ (gStrong [g0, g1] W j) ∧
        toMat 5 133 Si[j]! = matJ (gStrong [g0, g1] W j)⁻¹ := by
  unfold strongOKM at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hW, hS⟩, hSi⟩, hS0⟩, hS1⟩, hinv⟩, hwords⟩ := h
  refine ⟨hS, hSi, ?_⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hval : toMat 5 133 S[j]! = matJ (gStrong [g0, g1] W j) := by
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · interval_cases j
        · rw [gStrong_of_lt [g0, g1] W (show 0 < [g0, g1].length by simp), hS0, h0]
          rfl
        · rw [gStrong_of_lt [g0, g1] W (show 1 < [g0, g1].length by simp), hS1, h1]
          rfl
      · have hw := allBelowN_spec hwords hj
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hw
        rcases hw with hw | ⟨hlet, hpeq⟩
        · omega
        · rw [gStrong_of_ge [g0, g1] W (show [g0, g1].length ≤ j by simp; omega), hpeq]
          exact toMat_mword (fun i hi => (ih i hi (by omega)).1)
            (fun i hi => (ih i hi (by omega)).2) _ hlet
    refine ⟨hval, toMat_inv_of_mulM hval ?_⟩
    have := allBelowN_spec hinv hj
    simpa only [beq_iff_eq] using this

@[irreducible] def mH : Array (Array (Array ℕ)) :=
  (extendStrongM #[mRegs[1]!, mRegs[2]!] LocalData.strongWords).1

theorem mH_eq : mH = (extendStrongM #[mRegs[1]!, mRegs[2]!] LocalData.strongWords).1 := by
  unfold mH; rfl

@[irreducible] def mHi : Array (Array (Array ℕ)) :=
  (extendStrongM #[mRegs[1]!, mRegs[2]!] LocalData.strongWords).2

theorem mHi_eq : mHi = (extendStrongM #[mRegs[1]!, mRegs[2]!] LocalData.strongWords).2 := by
  unfold mHi; rfl

abbrev mD : Array (Array ℕ) := mword mH mHi LocalData.innerWord

abbrev mU : Array (Array ℕ) := wordM (seedSel rowsA rowsB) LocalData.outerWord

abbrev mUi : Array (Array ℕ) := invM 5 133 mU

abbrev mW : Array (Array ℕ) := powM 5 133 (mulM 5 133 rowsA (mulM 5 133 rowsB rowsB)) 8

abbrev rowsS : Array (Array ℕ) := rowsOf 5 133 LocalData.normalizerPayload

abbrev rowsC : Array (Array ℕ) := rowsOf 5 133 LocalData.involutionPayload

@[irreducible] def mXs : Array (Array ℕ) :=
  xVecs mH (seedWordVec rowsA rowsB LocalData.rootWord CFSG.Sporadic.HNSchreier.Native.rootVec) LocalData.parents

theorem mXs_eq : mXs =
    xVecs mH (seedWordVec rowsA rowsB LocalData.rootWord CFSG.Sporadic.HNSchreier.Native.rootVec) LocalData.parents := by
  unfold mXs; rfl

theorem invol_parts :
    mRegs.size = 11 ∧ strongOKM mRegs[1]! mRegs[2]! mH mHi LocalData.strongWords = true ∧
    mulM 5 133 mU mUi = idM 133 ∧ mulM 5 133 (mulM 5 133 mD mUi) rowsS = rowsC ∧
    mulM 5 133 rowsC rowsC = idM 133 ∧ notIdM 133 rowsC = true ∧
    mulVec 5 133 rowsC CFSG.Sporadic.HNSchreier.Native.rootVec = CFSG.Sporadic.HNSchreier.Native.rootVec ∧
    mulM 5 133 rowsS rowsA = mulM 5 133 rowsA rowsS ∧
    mulM 5 133 mW (mulM 5 133 rowsS rowsB) = mulM 5 133 rowsB (mulM 5 133 mW rowsS) ∧
    mXs.size = 462 ∧ mXs[0]! = seedWordVec rowsA rowsB LocalData.rootWord CFSG.Sporadic.HNSchreier.Native.rootVec ∧
    (∀ i < 462, i ≠ 0 → mXs[i]! =
      mulVec 5 133 mH[LocalData.parents[i]!.2 - 1]! mXs[LocalData.parents[i]!.1]!) ∧
    tauIdx.size = 462 ∧
    (∀ i < 462, tauIdx[i]! < 462 ∧
      labMasks[tauIdx[i]!]! = canonMask (permMask tauArr labMasks[i]!) ∧
      mulVec 5 133 rowsC mXs[i]! = mXs[tauIdx[i]!]!) := by
  have h := invol_cert
  unfold involChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← mRegs_eq, ← mH_eq, ← mHi_eq, ← mXs_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩,
    c14⟩ := h
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, fun i hi hi0 => ?_, c13,
    fun i hi => ?_⟩
  · have := allBelowN_spec c12 hi
    simp only [Bool.or_eq_true, beq_iff_eq, hi0, false_or] at this
    exact this
  · have := allBelowN_spec c14 hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

theorem mRegs_get
    {r : ℕ} (hr : r < 11) : toMat 5 133 mRegs[r]! = matJ (jRegs r) :=
  regsM_rep.2 r hr

theorem mH_facts :
    mH.size = 17 ∧ mHi.size = 17 ∧ ∀ j < 17,
    toMat 5 133 mH[j]! = matJ (hJ j) ∧ toMat 5 133 mHi[j]! = matJ (hJ j)⁻¹ := by
  obtain ⟨-, h2, -⟩ := invol_parts
  obtain ⟨hs, hsi, h⟩ := toMat_of_strongOKM h2 (mRegs_get (r := 1) (by norm_num))
    (mRegs_get (r := 2) (by norm_num))
  rw [strongWords_size] at hs hsi
  exact ⟨hs, hsi, fun j hj => h j (by rw [hs]; exact hj)⟩

theorem hWordJ_cons (l : ℤ) (w : List ℤ) :
    hWordJ (l :: w) = (if 0 < l then hJ (l.natAbs - 1) else (hJ (l.natAbs - 1))⁻¹) * hWordJ w := by
  simp only [hWordJ, List.map_cons, List.prod_cons]

theorem toMat_mword_hWord
    (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) :
    toMat 5 133 (mword mH mHi w) = matJ (hWordJ w) := by
  induction w with
  | nil =>
    rw [mword, toMat_idM]
    rfl
  | cons l w ih =>
    obtain ⟨hl0, hl17⟩ := hw l (List.mem_cons_self ..)
    rw [mword, toMat_mulM, ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'), hWordJ_cons,
      matJ_mul]
    congr 1
    rw [mletter]
    by_cases hpos : 0 < l
    · rw [ite_eq_left hpos, ite_eq_left hpos, show l.toNat - 1 = l.natAbs - 1 by omega]
      exact (mH_facts.2.2 _ (by omega)).1
    · rw [ite_eq_right hpos, ite_eq_right hpos, show (-l).toNat - 1 = l.natAbs - 1 by omega]
      exact (mH_facts.2.2 _ (by omega)).2

theorem toMat_mD :
    toMat 5 133 mD = matJ (hWordJ LocalData.innerWord) :=
  toMat_mword_hWord _ local_parts_data.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem matJ_seedWordJ (w : List ℕ) :
    matJ (seedWordJ w) = (w.map fun l => if l = 1 then matA else matB).prod := by
  rw [seedWordJ, matJ_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  split_ifs
  · exact mat_aJ
  · exact mat_bJ

theorem toMat_mU :
    toMat 5 133 mU = matJ (seedWordJ LocalData.outerWord) := by
  rw [toMat_wordM_seed _ local_parts_data.2.1, matJ_seedWordJ]

theorem toMat_mUi :
    toMat 5 133 mUi = matJ (seedWordJ LocalData.outerWord)⁻¹ :=
  toMat_inv_of_mulM toMat_mU invol_parts.2.2.1

theorem toMat_rowsS : toMat 5 133 rowsS = matS := by rw [toMat_rowsOf, matS_eq]

@[expose, irreducible] def matCpin : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  decode 5 133 1 LocalData.involutionPayload

theorem matCpin_eq : matCpin = decode 5 133 1 LocalData.involutionPayload := by
  unfold matCpin; rfl

theorem toMat_rowsC : toMat 5 133 rowsC = matCpin := by rw [toMat_rowsOf, matCpin_eq]

theorem matCx_eq_matC :
    matCx = matCpin := by
  have e := congrArg (toMat 5 133) invol_parts.2.2.2.1
  rw [toMat_mulM, toMat_mulM, toMat_mD, toMat_mUi, toMat_rowsS, toMat_rowsC] at e
  exact e

theorem matCx_sq :
    matCx * matCx = 1 := by
  have e := congrArg (toMat 5 133) invol_parts.2.2.2.2.1
  rw [toMat_mulM, toMat_rowsC, toMat_idM, ← matCx_eq_matC] at e
  exact e

theorem matCx_ne_one : matCx ≠ 1 := by
  rw [matCx_eq_matC, ← toMat_rowsC]
  exact toMat_ne_one_of_notIdM invol_parts.2.2.2.2.2.1

theorem toVec_rootVec : toVec 5 133 CFSG.Sporadic.HNSchreier.Native.rootVec = fixedVector := by
  funext j
  rw [toVec_apply, CFSG.Sporadic.HNSchreier.Native.rootVec, getElem!_ofFn _ j.isLt]
  rfl

theorem matCx_fix :
    matCx *ᵥ fixedVector = fixedVector := by
  have e := congrArg (toVec 5 133) invol_parts.2.2.2.2.2.2.1
  rw [toVec_mulVec, toMat_rowsC, toVec_rootVec, ← matCx_eq_matC] at e
  exact e

theorem matS_comm_A : matS * matA = matA * matS := by
  have e := congrArg (toMat 5 133) invol_parts.2.2.2.2.2.2.2.1
  rw [toMat_mulM, toMat_mulM, toMat_rowsS, toMat_rowsA] at e
  exact e

theorem toMat_mW : toMat 5 133 mW = (matA * (matB * matB)) ^ 8 := by
  rw [toMat_powM, toMat_mulM, toMat_mulM, toMat_rowsA, toMat_rowsB]

theorem matS_conj_B : (matA * (matB * matB)) ^ 8 * (matS * matB) =
    matB * ((matA * (matB * matB)) ^ 8 * matS) := by
  have e := congrArg (toMat 5 133) invol_parts.2.2.2.2.2.2.2.2.1
  rw [toMat_mulM, toMat_mulM, toMat_mulM, toMat_mulM, toMat_mW, toMat_rowsS, toMat_rowsB] at e
  exact e

theorem seedWordVec_cons (A B : Array (Array ℕ)) (l : ℕ) (w : List ℕ) (v : Array ℕ) :
    seedWordVec A B (l :: w) v = mulVec 5 133 (seedSel A B l) (seedWordVec A B w v) := by
  unfold seedWordVec
  exact List.foldr_cons ..

theorem toVec_seedWordVec
    (w : List ℕ) (hw : ∀ l ∈ w, l = 1 ∨ l = 2) (v : Array ℕ) :
    toVec 5 133 (seedWordVec rowsA rowsB w v) = matJ (seedWordJ w) *ᵥ toVec 5 133 v := by
  induction w with
  | nil =>
    rw [show seedWordVec rowsA rowsB [] v = v from rfl, seedWordJ, List.map_nil, List.prod_nil,
      matJ_one, Matrix.one_mulVec]
  | cons l w ih =>
    rw [seedWordVec_cons, toVec_mulVec, ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'),
      seedWordJ_cons, matJ_mul, Matrix.mulVec_mulVec]
    congr 2
    rw [toMat_seedSel l (hw l (List.mem_cons_self ..))]
    split_ifs
    · exact mat_aJ.symm
    · exact mat_bJ.symm

theorem toVec_mXs :
    ∀ i < 462, toVec 5 133 mXs[i]! = xVec i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h0, hpar, -⟩ := invol_parts
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [h0, toVec_seedWordVec _ local_parts_data.1, toVec_rootVec,
        ctuc_hn_local_alternating_outer_data.2.2.2.2.2.1]
    · obtain ⟨hj, he⟩ := local_parts_data.2.2.2.1 i hi0 hi
      rw [hpar i hi (by omega), toVec_mulVec, ih _ hj (by omega),
        (mH_facts.2.2 _ (by omega)).1,
        (ctuc_hn_local_alternating_outer_data).2.2.2.2.2.2.1 i hi0 hi]

theorem tau_facts (k : Fin 462) : tauIdx[k.val]! < 462 ∧
    labMasks[tauIdx[k.val]!]! = canonMask (permMask tauArr labMasks[k.val]!) ∧
    mulVec 5 133 rowsC mXs[k.val]! = mXs[tauIdx[k.val]!]! :=
  invol_parts.2.2.2.2.2.2.2.2.2.2.2.2.2 k k.isLt

@[expose] def tauF
    (k : Fin 462) : Fin 462 := ⟨tauIdx[k.val]!, (tau_facts k).1⟩

theorem tauF_val (k : Fin 462) : (tauF k).val = tauIdx[k.val]! := rfl

theorem matCx_xVec
    (k : Fin 462) : matCx *ᵥ xVec k = xVec (tauF k) := by
  rw [← toVec_mXs k k.isLt, ← toVec_mXs _ (tauF k).isLt, tauF_val, matCx_eq_matC,
    ← toMat_rowsC, ← toVec_mulVec, (tau_facts k).2.2]

theorem tauArr_spec : ∀ i : Fin 12, tauArr[i.val]! = (Equiv.swap (0 : Fin 12) 1 i).val := by
  decide

theorem labPart_tauF (k : Fin 462) :
    labPart (tauF k) = Equiv.swap (0 : Fin 12) 1 • labPart k := by
  apply Subtype.ext
  rw [CFSG.Sporadic.HN.Local.smul_part_val]
  show maskSet12 labMasks[tauIdx[k.val]!]! = _
  rw [(tau_facts k).2.1, maskSet12_canonMask, maskSet12_permMask tauArr_spec]
  rfl

end CFSG.Sporadic.HNSchreier
