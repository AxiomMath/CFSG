module

public import CFSG.Monster.Existence.ELevelCheck
public import CFSG.Monster.B.TwoA.Census.CosetEnum
public import Certificates.Certificate16006

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

@[expose] def ebCodeA : ℕ := packP (false, 0, 191)

@[expose] def ebCodeB : ℕ := packP (false, 0, 127)

theorem packP_lt (y : Model.Pauli) : packP y < 2 ^ 24 := by
  unfold packP
  have h1 := Nat.mod_lt y.2.1 (show 0 < 4096 by norm_num)
  have h2 := Nat.mod_lt y.2.2 (show 0 < 4096 by norm_num)
  have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  omega

theorem eb_deltaPair_zero_one : deltaPair 0 1 = toD 191 := by
  have h : (Pi.single 0 1 + Pi.single 1 1 : Fin 24 → ZMod 2) = bvec 24 3 := by decide
  have h2 : Model.dualN 3 = 191 := Certificates.certificate16006.1
  rw [deltaPair, h, mk_bvec_eq_toD, h2]

theorem eb_deltaPair_zero_two : deltaPair 0 2 = toD 127 := by
  have h : (Pi.single 0 1 + Pi.single 2 1 : Fin 24 → ZMod 2) = bvec 24 5 := by decide
  have h2 : Model.dualN 5 = 127 := Certificates.certificate16006.2
  rw [deltaPair, h, mk_bvec_eq_toD, h2]

theorem vecX_ebCodeA : vecX ebCodeA = phi0 (coordOf rStar) := by
  rw [ebCodeA, vecX_packP, coordOf_rStar, eb_deltaPair_zero_one, toC_zero]

theorem vecX_ebCodeB : vecX ebCodeB = phi0 (coordOf rTwo) := by
  rw [ebCodeB, vecX_packP, show coordOf rTwo = (0, deltaPair 0 2) from coordOf_DQ _,
    eb_deltaPair_zero_two, toC_zero]

theorem ebCodeA_lt : ebCodeA < 2 ^ 24 := packP_lt _

theorem ebCodeB_lt : ebCodeB < 2 ^ 24 := packP_lt _

@[expose] def case1OK : Bool :=
  shortPacked.all fun v =>
    bX v ebCodeA || bX v ebCodeB || !isShortX (v ^^^ ebCodeA) || !isShortX (v ^^^ ebCodeB) ||
      !isShortX (v ^^^ ebCodeA ^^^ ebCodeB)

theorem bX_eq_false_of_bL {x y : ℕ} (h : bL (vecX x) (vecX y) = 0) : bX x y = false := by
  rw [bL_vecX, boolZ_eq_zero_iff] at h
  exact h

theorem case1_sound (h : case1OK = true) {v : L2} (hv : v ∈ shortSet)
    (ha : bL v (vecX ebCodeA) = 0) (hb : bL v (vecX ebCodeB) = 0)
    (h1 : v + vecX ebCodeA ∈ shortSet) (h2 : v + vecX ebCodeB ∈ shortSet)
    (h3 : v + (vecX ebCodeA + vecX ebCodeB) ∈ shortSet) : False := by
  obtain ⟨x, hx, hx24, rfl⟩ := mem_shortPacked hv
  have hall := List.all_eq_true.1 h x hx
  have e1 : bX x ebCodeA = false := bX_eq_false_of_bL ha
  have e2 : bX x ebCodeB = false := bX_eq_false_of_bL hb
  have s1 : isShortX (x ^^^ ebCodeA) = true := by
    rw [isShortX_iff (Nat.xor_lt_two_pow (n := 24) hx24 ebCodeA_lt), vecX_xor]
    exact h1
  have s2 : isShortX (x ^^^ ebCodeB) = true := by
    rw [isShortX_iff (Nat.xor_lt_two_pow (n := 24) hx24 ebCodeB_lt), vecX_xor]
    exact h2
  have s3 : isShortX (x ^^^ ebCodeA ^^^ ebCodeB) = true := by
    rw [isShortX_iff (Nat.xor_lt_two_pow (n := 24) (Nat.xor_lt_two_pow (n := 24) hx24 ebCodeA_lt)
      ebCodeB_lt), vecX_xor, vecX_xor, add_assoc]
    exact h3
  simp only [e1, e2, s1, s2, s3, Bool.not_true, Bool.or_false, Bool.false_eq_true] at hall


@[expose] def qX (x : ℕ) : Bool := Model.pairN x (x >>> 12)

theorem qL_vecX (x : ℕ) : qL (vecX x) = boolZ (qX x) := by
  rw [vecX, qL_phi0, pair_toC_toD, qX]

theorem rhoEquiv_mem_frameInv_of_packed
    {q : Q} {x : ℕ} (hx : x < 2 ^ 24)
    (hq : phi0 (coordOf q) = vecX x) (h0 : x ≠ 0) (hqL : qX x = false)
    (hs : isShortX x = false) : rhoEquiv q ∈ frameInv := by
  have hmem : phi0 (coordOf q) ∈ frameDelta := by
    rw [hq]
    refine ⟨fun h => h0 (vecX_injective_lt hx (by norm_num) (h.trans vecX_zero.symm)), ?_, ?_⟩
    · rw [qL_vecX, hqL, boolZ_false]
    · intro hmem
      have h := (isShortX_iff hx).2 hmem
      rw [hs] at h
      exact Bool.false_ne_true h
  rw [frameInv_eq_image]
  exact ⟨q, hmem, rfl⟩

@[expose] def shortEnc (n : ℕ) : Bool := isShortX (packP (pauliDec n))

@[expose] def mulEnc (n m : ℕ) : ℕ :=
  Native.CosetEnum.enc (Model.Pauli.mul (pauliDec n) (pauliDec m))

@[expose] def cls0 : List ℕ := (classCert 1 (classEnc 0)).pts.toList

@[expose] def class0OK : Bool :=
  let sh := cls0.filter shortEnc
  sh.all fun n => sh.all fun m => let p := mulEnc n m; sh.all fun k => k != p

theorem shortEnc_iff (n : ℕ) :
    shortEnc n = true ↔ IsShortCoord (coordOf (qOfEnc n)) := by
  have h1 : IsShortCoord (coordOf (qOfEnc n)) ↔
      phi0 (toC (pauliDec n).2.1, toD (pauliDec n).2.2) ∈ shortSet := by
    rw [qOfEnc, coordOf_pauliQ]
    exact Iff.rfl
  rw [h1, ← vecX_packP, ← isShortX_iff (packP_lt _), shortEnc]

theorem mulEnc_lt (n m : ℕ) : mulEnc n m < 2 ^ 25 := by
  rw [mulEnc, enc_eq_pauliEnc]
  exact pauliEnc_lt (by split_ifs <;> norm_num) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))

theorem qOfEnc_mul (n m : ℕ) : qOfEnc (mulEnc n m) = qOfEnc n * qOfEnc m := by
  rw [mulEnc, qOfEnc_enc, pauliQ_mul]
  rfl

theorem mem_cls0
    {q : Q} (h : cosetRep 1 * rhoGvis q ∈ qmatClass (classRep 0)) :
    ∃ n ∈ cls0, n < 2 ^ 25 ∧ qOfEnc n = q := by
  have hc := classCheck_spec (k := 0) (by norm_num)
  have h' : cosetRep 1 * rhoGvis q ∈ qmatClass (cosetElt 1 (classEnc 0)) := h
  rw [qmatClass_eq_of_natCertOK 1 hc.1] at h'
  obtain ⟨j, hj, e⟩ := h'
  have hj' : j < (classCert 1 (classEnc 0)).pts.size := hj
  refine ⟨(classCert 1 (classEnc 0)).pts[j]!, ?_, of_decide_eq_true (natCertOK_valid hc.1 hj'),
    rhoGvis_injective (mul_left_cancel e)⟩
  rw [cls0, Array.mem_toList_iff]
  simp [hj']

theorem class0_sound
    (h : class0OK = true) {a b : Q} (ha : IsShortCoord (coordOf a))
    (hb : IsShortCoord (coordOf b)) (hab : IsShortCoord (coordOf (a * b)))
    (h1 : cosetRep 1 * rhoGvis a ∈ qmatClass (classRep 0))
    (h2 : cosetRep 1 * rhoGvis b ∈ qmatClass (classRep 0))
    (h3 : cosetRep 1 * rhoGvis (a * b) ∈ qmatClass (classRep 0)) : False := by
  obtain ⟨n, hn, hn25, rfl⟩ := mem_cls0 h1
  obtain ⟨m, hm, hm25, rfl⟩ := mem_cls0 h2
  obtain ⟨k, hk, hk25, hkab⟩ := mem_cls0 h3
  have hkp : k = mulEnc n m :=
    qOfEnc_injective hk25 (mulEnc_lt n m) (hkab.trans (qOfEnc_mul n m).symm)
  have sn : shortEnc n = true := (shortEnc_iff n).2 ha
  have sm : shortEnc m = true := (shortEnc_iff m).2 hb
  have sk : shortEnc k = true := (shortEnc_iff k).2 (hkab ▸ hab)
  have hsh : ∀ x, x ∈ cls0 → shortEnc x = true → x ∈ cls0.filter shortEnc := fun x hx hs =>
    List.mem_filter.2 ⟨hx, hs⟩
  unfold class0OK at h
  simp only [List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact h n (hsh n hn sn) m (hsh m hm sm) k (hsh k hk sk) hkp

end CFSG.Monster.Existence
