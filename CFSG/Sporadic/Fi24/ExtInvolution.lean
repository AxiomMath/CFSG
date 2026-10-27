module

public import CFSG.Sporadic.Fi24.ExtSpec
public import CFSG.Sporadic.Fi24.Faithful

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mE_mul_mRT :
    mE * mRᵀ = mRᵀ := by
  calc mE * mRᵀ = mRᵀ * (mS * mK) := by simp only [mE, mK, Matrix.mul_assoc]
    _ = mRᵀ := by rw [mS_mul_mK, Matrix.mul_one]

theorem mE_mul_mE : mE * mE = mE := by
  calc mE * mE = (mE * mRᵀ) * (mS * (mR * mF)) := by simp only [mE, Matrix.mul_assoc]
    _ = mE := by rw [mE_mul_mRT]

private theorem zmod3_three (x : ZMod 3) : x + (x + x) = 0 := by revert x; decide

private theorem zmod3_neg (x : ZMod 3) : -x = x + x := by revert x; decide

private theorem matrix_three (X : Matrix (Fin 781) (Fin 781) (ZMod 3)) : X + (X + X) = 0 := by
  ext i j; simp only [Matrix.add_apply, Matrix.zero_apply]; exact zmod3_three _

theorem mT_mul_mT : mT * mT = 1 := by
  show (1 + mE) * (1 + mE) = 1
  rw [add_mul, mul_add, mul_add, Matrix.one_mul 1, Matrix.one_mul mE, Matrix.mul_one mE,
    mE_mul_mE, add_assoc, matrix_three, add_zero]

@[expose] noncomputable def tT :
    GL (Fin 781) (ZMod 3) := ⟨mT, mT, mT_mul_mT, mT_mul_mT⟩

theorem coe_tT :
    ((tT : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) = mT := rfl

theorem tT_mul_tT :
    tT * tT = 1 := Units.ext mT_mul_mT

theorem tT_inv :
    tT⁻¹ = tT := inv_eq_of_mul_eq_one_right tT_mul_tT

private theorem two_pow_253 : (2 : ZMod 3) ^ 253 = -1 := by decide

theorem det_mT : mT.det = -1 := by
  have h : mS * (mR * mF) * mRᵀ = 1 := by
    rw [← mS_mul_mK]; simp only [mK, Matrix.mul_assoc]
  rw [mT, mE, Matrix.det_one_add_mul_comm, h, ← two_smul (ZMod 3), Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin, two_pow_253]

theorem det_tT :
    (tT : Matrix (Fin 781) (Fin 781) (ZMod 3)).det = -1 := det_mT

theorem tT_not_mem : tT ∉ J := by
  intro h
  have := det_eq_one ⟨tT, h⟩
  rw [show mat ⟨tT, h⟩ = mT from rfl, det_mT] at this
  exact absurd this (by decide)

theorem tT_ne_one :
    tT ≠ 1 := fun h => tT_not_mem (h ▸ J.one_mem)

theorem pt_zero_sp : (pt 0).sp = LinearMap.range (mRᵀ).mulVecLin := by
  rw [Matrix.range_mulVecLin]
  show rowSpan 253 (form 0).rows = _
  rw [form_zero, rowSpan, matW_rows_eq]
  rfl

theorem mE_mulVec_of_mem
    {v : Fin 781 → ZMod 3} (hv : v ∈ (pt 0).sp) : mE *ᵥ v = v := by
  rw [pt_zero_sp] at hv
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hv
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, mE_mul_mRT]

theorem mem_pt_zero_iff
    (v : Fin 781 → ZMod 3) : v ∈ (pt 0).sp ↔ mT *ᵥ v = -v := by
  constructor
  · intro hv
    rw [mT, Matrix.add_mulVec, Matrix.one_mulVec, mE_mulVec_of_mem hv]
    funext i
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [zmod3_neg]
  · intro hv
    have h1 : mE *ᵥ v = v := by
      rw [mT, Matrix.add_mulVec, Matrix.one_mulVec] at hv
      funext i
      have := congrFun hv i
      simp only [Pi.add_apply, Pi.neg_apply] at this
      rw [zmod3_neg] at this
      have h := congrArg (· - v i) this
      simp only [add_sub_cancel_left] at h
      exact h
    rw [pt_zero_sp, ← h1, mE, ← Matrix.mulVec_mulVec]
    exact LinearMap.mem_range.2 ⟨_, rfl⟩

theorem mT_mulVec_of_mem
    {v : Fin 781 → ZMod 3} (hv : v ∈ (pt 0).sp) : mT *ᵥ v = -v :=
  (mem_pt_zero_iff v).1 hv

theorem mat_mul_mE_of_fix
    {g : J} (hg : g • pt 0 = pt 0) : mat g * mE = mE * mat g := by
  have hg' : g⁻¹ • pt 0 = pt 0 := by
    conv_lhs => rw [← hg]
    rw [inv_smul_smul]
  obtain ⟨M, hM⟩ := exists_mul_eq mR (mat g) (fun j => by
    have := mulVec_mem_of_fix hg j; rwa [form_zero] at this)
  obtain ⟨M', hM'⟩ := exists_mul_eq mR (mat g⁻¹) (fun j => by
    have := mulVec_mem_of_fix hg' j; rwa [form_zero] at this)
  exact commute_proj mR mF mS mS_mul_mK mK_mul_mS (mat_mul_inv g) (mat_inv_mul g) (form_inv g)
    hM hM'

theorem mat_mul_mT_of_fix
    {g : J} (hg : g • pt 0 = pt 0) : mat g * mT = mT * mat g := by
  rw [mT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mat_mul_mE_of_fix hg]

theorem fix_of_mat_mul_mT
    {g : J} (h : mat g * mT = mT * mat g) : g • pt 0 = pt 0 := by
  have hinv : mat g⁻¹ * mT = mT * mat g⁻¹ := by
    calc mat g⁻¹ * mT = mat g⁻¹ * (mT * mat g) * mat g⁻¹ := by
          rw [Matrix.mul_assoc (mat g⁻¹) (mT * mat g), Matrix.mul_assoc mT, mat_mul_inv,
            Matrix.mul_one]
      _ = mat g⁻¹ * (mat g * mT) * mat g⁻¹ := by rw [h]
      _ = mT * mat g⁻¹ := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  have key : ∀ {k : J}, mat k * mT = mT * mat k →
      ∀ v ∈ (pt 0).sp, mat k *ᵥ v ∈ (pt 0).sp := by
    intro k hk v hv
    rw [mem_pt_zero_iff, Matrix.mulVec_mulVec, ← hk, ← Matrix.mulVec_mulVec,
      mT_mulVec_of_mem hv, Matrix.mulVec_neg]
  apply Sub781.ext'
  rw [smul_sp]
  apply le_antisymm
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    rw [Matrix.mulVecLin_apply]
    exact key (k := g) h v hv
  · intro v hv
    refine Submodule.mem_map.2 ⟨mat g⁻¹ *ᵥ v, key (k := g⁻¹) hinv v hv, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec]

theorem commute_tT_iff
    (g : J) : (g : GL (Fin 781) (ZMod 3)) * tT = tT * g ↔ g • root = root := by
  rw [smul_eq_iff]
  constructor
  · intro h
    have h' := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, coe_tT] at h'
    exact fix_of_mat_mul_mT h'
  · intro h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_tT]
    exact mat_mul_mT_of_fix h

theorem mem_stabilizer_iff_commute
    (g : J) :
    g ∈ MulAction.stabilizer J root ↔ (g : GL (Fin 781) (ZMod 3)) * tT = tT * g := by
  rw [MulAction.mem_stabilizer_iff, commute_tT_iff]

theorem commute_tT_of_mem_lvl_one
    {g : J} (hg : g ∈ lvl 1) :
    (g : GL (Fin 781) (ZMod 3)) * tT = tT * g :=
  (mem_stabilizer_iff_commute g).1 (by rw [stabilizer_root]; exact hg)

structure NormFacts : Prop where
  size : normWords.size = 2
  letters : normWords.all (·.all fun z => z != 0 && z.natAbs ≤ 13) = true
  nA : eqRows 781 (mulW (mulW matTW matA) matTW) (wordW (genLetterW sgW sgiW) normWords[0]!) =
    true
  nB : eqRows 781 (mulW (mulW matTW matB) matTW) (wordW (genLetterW sgW sgiW) normWords[1]!) =
    true
  comm : (List.range 11).all (fun i => eqRows 781 (mulW matTW sgW[i + 2]!)
    (mulW sgW[i + 2]! matTW)) = true
  P1_sq : eqRows 781 (mulW (mulW matTW (mulW (mulW matA matTW) matA))
    (mulW matTW (mulW (mulW matA matTW) matA))) (idW 781) = true
  P1_ne : eqRows 781 (mulW matTW (mulW (mulW matA matTW) matA)) (idW 781) = false
  P2_cube : eqRows 781 (mulW (mulW matTW (mulW (mulW matB matTW) (mulW matB matB)))
    (mulW (mulW matTW (mulW (mulW matB matTW) (mulW matB matB)))
      (mulW matTW (mulW (mulW matB matTW) (mulW matB matB))))) (idW 781) = true
  P2_ne : eqRows 781 (mulW matTW (mulW (mulW matB matTW) (mulW matB matB))) (idW 781) = false

theorem normFacts : NormFacts := by
  have h := extFacts.norm
  unfold normChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem normWords_letters
    {i : ℕ} (hi : i < 2) : ∀ z ∈ normWords[i]!, z ≠ 0 ∧ z.natAbs ≤ 13 := by
  intro z hz
  have h := normFacts.letters
  rw [Array.all_eq_true] at h
  have hi' : i < normWords.size := by rw [normFacts.size]; exact hi
  have := h i hi'
  rw [getElem!_pos normWords i hi'] at hz
  rw [List.all_eq_true] at this
  have := this z hz
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

@[expose] noncomputable def nA : J := extWord normWords[0]!

@[expose] noncomputable def nB : J := extWord normWords[1]!

theorem letterOK_TAT :
    LetterOK (mulW (mulW matTW matA) matTW) (mT * mA * mT) :=
  (letterOK_matT.mulW letterOK_matA).mulW letterOK_matT

theorem letterOK_TBT :
    LetterOK (mulW (mulW matTW matB) matTW) (mT * mB * mT) :=
  (letterOK_matT.mulW letterOK_matB).mulW letterOK_matT

theorem letterOK_normWord
    {i : ℕ} (hi : i < 2) :
    LetterOK (wordW (genLetterW sgW sgiW) normWords[i]!) (mat (extWord normWords[i]!)) :=
  letterOK_extWord fun z hz => (normWords_letters hi z hz).2

theorem mat_nA :
    mat nA = mT * mA * mT := by
  have := congrArg (matW 781 781) (eq_of_eqRows normFacts.nA).2
  rw [letterOK_TAT.mat, (letterOK_normWord (by norm_num)).mat] at this
  exact this.symm

theorem mat_nB :
    mat nB = mT * mB * mT := by
  have := congrArg (matW 781 781) (eq_of_eqRows normFacts.nB).2
  rw [letterOK_TBT.mat, (letterOK_normWord (by norm_num)).mat] at this
  exact this.symm

theorem tT_mul_gA_mul_tT :
    tT * gA * tT = nA := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_tT]
  exact mat_nA.symm

theorem tT_mul_gB_mul_tT :
    tT * gB * tT = nB := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_tT]
  exact mat_nB.symm

theorem conj_mem
    {g : GL (Fin 781) (ZMod 3)} (hg : g ∈ J) : tT * g * tT ∈ J := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [tT_mul_gA_mul_tT]; exact nA.2
    · rw [tT_mul_gB_mul_tT]; exact nB.2
  | one => rw [mul_one, tT_mul_tT]; exact J.one_mem
  | mul x y _ _ hx hy =>
    have e : tT * (x * y) * tT = (tT * x * tT) * (tT * y * tT) := by
      calc tT * (x * y) * tT = tT * x * (tT * tT) * y * tT := by
            rw [tT_mul_tT, mul_one]; simp only [mul_assoc]
        _ = (tT * x * tT) * (tT * y * tT) := by simp only [mul_assoc]
    rw [e]; exact J.mul_mem hx hy
  | inv x _ hx =>
    have e : tT * x⁻¹ * tT = (tT * x * tT)⁻¹ := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, tT_inv, mul_assoc]
    rw [e]; exact J.inv_mem hx

@[expose] noncomputable def tAut :
    MulAut J where
  toFun g := ⟨tT * g * tT, conj_mem g.2⟩
  invFun g := ⟨tT * g * tT, conj_mem g.2⟩
  left_inv g := Subtype.ext (by
    show tT * (tT * g * tT) * tT = g
    calc tT * (tT * g * tT) * tT = (tT * tT) * g * (tT * tT) := by simp only [mul_assoc]
      _ = g := by rw [tT_mul_tT, one_mul, mul_one])
  right_inv g := Subtype.ext (by
    show tT * (tT * g * tT) * tT = g
    calc tT * (tT * g * tT) * tT = (tT * tT) * g * (tT * tT) := by simp only [mul_assoc]
      _ = g := by rw [tT_mul_tT, one_mul, mul_one])
  map_mul' g h := Subtype.ext (by
    show tT * (g * h) * tT = tT * g * tT * (tT * h * tT)
    calc tT * (g * h) * tT = tT * g * (tT * tT) * h * tT := by
          rw [tT_mul_tT, mul_one]; simp only [mul_assoc]
      _ = tT * g * tT * (tT * h * tT) := by simp only [mul_assoc])

theorem coe_tAut
    (g : J) : ((tAut g : J) : GL (Fin 781) (ZMod 3)) = tT * g * tT := rfl

theorem mat_tAut
    (g : J) : mat (tAut g) = mT * mat g * mT := rfl

theorem tAut_tAut
    (g : J) : tAut (tAut g) = g := tAut.left_inv g

theorem tAut_a :
    tAut a = nA := Subtype.ext tT_mul_gA_mul_tT

theorem tAut_b :
    tAut b = nB := Subtype.ext tT_mul_gB_mul_tT

theorem tAut_of_mem_stabilizer
    {g : J} (hg : g ∈ MulAction.stabilizer J root) : tAut g = g := by
  apply Subtype.ext
  rw [coe_tAut, ← (mem_stabilizer_iff_commute g).1 hg, mul_assoc, tT_mul_tT, mul_one]

theorem commute_tT_gs
    {j : ℕ} (h2 : 2 ≤ j) (h13 : j < 13) :
    (gs j : GL (Fin 781) (ZMod 3)) * tT = tT * gs j := by
  have h := normFacts.comm
  rw [List.all_eq_true] at h
  have := h (j - 2) (List.mem_range.2 (by omega))
  rw [show j - 2 + 2 = j by omega] at this
  obtain ⟨hc, -, -⟩ := genFacts j h13
  have e := congrArg (matW 781 781) (eq_of_eqRows this).2
  rw [(letterOK_matT.mulW (LetterOK.of_canonRows hc)).mat,
    ((LetterOK.of_canonRows hc).mulW letterOK_matT).mat, (matW_sg j h13).1] at e
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_tT]
  exact e.symm

theorem gs_mem_stabilizer
    {j : ℕ} (h2 : 2 ≤ j) (h13 : j < 13) :
    gs j ∈ MulAction.stabilizer J root :=
  (mem_stabilizer_iff_commute _).2 (commute_tT_gs h2 h13)

end CFSG.Sporadic.Fi24
