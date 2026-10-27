module

public import CFSG.Monster.B.TwoA.Census.CosetEnumGroup
public import Certificates.Data.CFSGNative.MonsterB.CosetEnum

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.Spin
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371

theorem toC_eq_zero_iff (a : ℕ) : toC a = 0 ↔ a % 2 ^ 12 = 0 := by
  have h1 : toC a = toC (a % 2 ^ 12) :=
    toC_ext fun j => by rw [Nat.testBit_mod_two_pow, decide_eq_true j.2, Bool.true_and]
  rw [h1, ← toC_zero]
  exact ⟨fun h => toC_injective (Nat.mod_lt _ (by norm_num)) (by norm_num) h,
    fun h => by rw [h]⟩

theorem toD_eq_zero_iff (d : ℕ) : toD d = 0 ↔ d % 2 ^ 12 = 0 := by
  have h1 : toD d = toD (d % 2 ^ 12) :=
    toD_ext fun j => by rw [Nat.testBit_mod_two_pow, decide_eq_true j.2, Bool.true_and]
  rw [h1, ← toD_zero]
  exact ⟨fun h => toD_injective (Nat.mod_lt _ (by norm_num)) (by norm_num) h,
    fun h => by rw [h]⟩

theorem pauliQ_eq_one_iff (x : Model.Pauli) : pauliQ x = 1 ↔ Native.CosetEnum.isOne x = true := by
  rw [pauliQ, MulEquiv.map_eq_one_iff, SpinCoord.ext_iff]
  simp only [toSC_s, toSC_a, toSC_δ, SpinCoord.one_s, SpinCoord.one_a, SpinCoord.one_δ,
    boolZ_eq_zero_iff, toC_eq_zero_iff, toD_eq_zero_iff, Native.CosetEnum.isOne,
    Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc]

theorem pauliQ_inj {x y : Model.Pauli} (hxa : x.2.1 < 2 ^ 12) (hxd : x.2.2 < 2 ^ 12)
    (hya : y.2.1 < 2 ^ 12) (hyd : y.2.2 < 2 ^ 12) (h : pauliQ x = pauliQ y) : x = y := by
  have h' : spinEquiv (toSC x) = spinEquiv (toSC y) := h
  have h1 := spinEquiv.injective h'
  have hs := congrArg SpinCoord.s h1
  have ha := congrArg SpinCoord.a h1
  have hd := congrArg SpinCoord.δ h1
  simp only [toSC_s, toSC_a, toSC_δ] at hs ha hd
  exact Prod.ext (boolZ_injective hs) (Prod.ext (toC_injective hxa hya ha)
    (toD_injective hxd hyd hd))

theorem native_dec : Native.CosetEnum.dec = pauliDec := rfl

theorem native_dec_apply (n : ℕ) : Native.CosetEnum.dec n = pauliDec n := rfl

theorem native_gen_apply (k : ℕ) : Native.CosetEnum.gen k = genPauli k := rfl

theorem native_mul_apply (x y : Model.Pauli) : Native.Pauli.mul x y = Model.Pauli.mul x y := by
  rw [native_Pauli_mul]

theorem enc_dec {n : ℕ} (hn : n < 2 ^ 25) : Native.CosetEnum.enc (pauliDec n) = n := by
  have key : ∀ m : ℕ, m < 33554432 → m % 4096 % 4096 + 4096 * (m / 4096 % 4096 % 4096) +
      (if decide (m / 16777216 % 2 = 1) = true then 16777216 else 0) = m := by
    intro m hm
    split_ifs with h
    · rw [decide_eq_true_eq] at h
      omega
    · rw [decide_eq_true_eq] at h
      omega
  have e : Native.CosetEnum.enc (pauliDec n) = n % 4096 % 4096 + 4096 * (n / 4096 % 4096 % 4096) +
      (if decide (n / 16777216 % 2 = 1) = true then 16777216 else 0) := by
    rw [Native.CosetEnum.enc, pauliDec, Nat.testBit_eq_decide_div_mod_eq]
    norm_num
  rw [e]
  exact key n (by norm_num at hn; exact hn)

theorem pauliDec_lt (n : ℕ) : (pauliDec n).2.1 < 2 ^ 12 ∧ (pauliDec n).2.2 < 2 ^ 12 :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem qOfEnc_injective {n n' : ℕ} (hn : n < 2 ^ 25) (hn' : n' < 2 ^ 25)
    (h : qOfEnc n = qOfEnc n') : n = n' := by
  have e := pauliQ_inj (pauliDec_lt n).1 (pauliDec_lt n).2 (pauliDec_lt n').1 (pauliDec_lt n').2 h
  rw [← enc_dec hn, ← enc_dec hn', e]

theorem enc_eq_pauliEnc (x : Model.Pauli) :
    Native.CosetEnum.enc x = pauliEnc (if x.1 then 1 else 0) (x.2.1 % 2 ^ 12) (x.2.2 % 2 ^ 12) := by
  rcases x with ⟨s, a, d⟩
  cases s <;> simp [Native.CosetEnum.enc, pauliEnc]

theorem qOfEnc_enc (x : Model.Pauli) : qOfEnc (Native.CosetEnum.enc x) = pauliQ x := by
  rcases x with ⟨s, a, d⟩
  rw [enc_eq_pauliEnc, qOfEnc_pauliEnc (by split_ifs <;> norm_num) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)), qP, pauliQ_mod_a, pauliQ_mod_d]
  cases s <;> rfl

theorem pauliQ_inv (x : Model.Pauli) : pauliQ (Native.CosetEnum.inv x) = (pauliQ x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← pauliQ_mul, pauliQ_eq_one_iff]
  rcases x with ⟨s, a, d⟩
  simp only [Native.CosetEnum.isOne, Native.CosetEnum.inv, Model.Pauli.mul, native_pairN,
    Nat.xor_self, Nat.zero_mod, beq_self_eq_true, Bool.and_true, pauli_s, pauli_a, pauli_d]
  cases s <;> cases Model.pairN a d <;> rfl

theorem getElem!_map_range {α : Type*} [Inhabited α] (f : ℕ → α) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).toArray[k]! = f k := by
  simp [hk]

@[expose] def tT (i : ℕ) : Array Model.Pauli := Native.CosetEnum.tabT (cosetA i) (cosetArr i)

@[expose] def tD (i : ℕ) : Array Model.Pauli := Native.CosetEnum.tabD (cosetA i) (cosetArr i)

@[expose] def imgs (i : ℕ) : Array Model.Pauli := Native.CosetEnum.gensImg (cosetA i) (cosetArr i)

@[expose] def wP (i : ℕ) : Model.Pauli := if i = 6 then (true, 0, 0) else sqPauli i

theorem tT_get (i : ℕ) {A : ℕ} (hA : A < 2 ^ 12) : (tT i)[A]! = alphaN i (false, A, 0) := by
  rw [tT, Native.CosetEnum.tabT, getElem!_map_range (n := 4096) _ (by simpa using hA),
    native_conjPermN, native_conjYN]
  rfl

theorem tD_get (i : ℕ) {D : ℕ} (hD : D < 2 ^ 12) : (tD i)[D]! = alphaN i (false, 0, D) := by
  rw [tD, Native.CosetEnum.tabD, getElem!_map_range (n := 4096) _ (by simpa using hD),
    native_conjPermN, native_conjYN]
  rfl

theorem imgs_get (i : ℕ) {k : ℕ} (hk : k < 24) : (imgs i)[k]! = alphaN i (genPauli k) := by
  rw [imgs, Native.CosetEnum.gensImg, getElem!_map_range _ hk, native_conjPermN, native_conjYN]
  rfl

theorem pauliQ_wP (i : ℕ) : pauliQ (wP i) = cosetW i := by
  unfold wP cosetW
  split_ifs
  · exact pauliQ_z
  · rfl

theorem conjQ_pauliQ_s (p : Pvis) (s : Bool) : conjQ p (pauliQ (s, 0, 0)) = pauliQ (s, 0, 0) := by
  cases s
  · rw [pauliQ_false_zero]
    exact map_one (conjQ p)
  · rw [pauliQ_z]
    exact conjQ_zQ p

theorem sqTest_eq_isOne (tA tB : Array Model.Pauli) (w : Model.Pauli) (n : ℕ) :
    Native.CosetEnum.sqTest tA tB w n =
      Native.CosetEnum.isOne (Native.CosetEnum.sqProd tA tB w (Native.CosetEnum.dec n)) := by
  have key : ∀ a b c : Bool, (a && b && (c && a && b)) = (c && a && b) := by decide
  exact key _ _ _

theorem sqProd_eq
    (i : ℕ) (s : Bool) {A D : ℕ} (hA : A < 2 ^ 12) (hD : D < 2 ^ 12) :
    pauliQ (Native.CosetEnum.sqProd (tT i) (tD i) (wP i) (s, A, D)) =
      pauliQ (s, A, D) * cosetW i * conjQ (cosetPair i) (pauliQ (s, A, D)) := by
  have e1 : Native.CosetEnum.sqProd (tT i) (tD i) (wP i) (s, A, D) =
      Model.Pauli.mul (s, A, D) (Model.Pauli.mul (wP i) (Model.Pauli.mul (s, 0, 0)
        (Model.Pauli.mul (alphaN i (false, A, 0)) (alphaN i (false, 0, D))))) := by
    rw [Native.CosetEnum.sqProd, native_Pauli_mul]
    exact congrArg (fun t => Model.Pauli.mul (s, A, D) (Model.Pauli.mul (wP i)
      (Model.Pauli.mul (s, 0, 0) t))) (congrArg₂ Model.Pauli.mul (tT_get i hA) (tD_get i hD))
  have e2 : conjQ (cosetPair i) (pauliQ (s, A, D)) = pauliQ (s, 0, 0) *
      conjQ (cosetPair i) (pauliQ (false, A, 0)) * conjQ (cosetPair i) (pauliQ (false, 0, D)) := by
    simp only [pauliQ_split s A D, map_mul, conjQ_pauliQ_s]
  rw [e1, e2]
  simp only [pauliQ_mul, pauliQ_wP, ← conjQ_cosetPair, mul_assoc]

theorem sqTest_iff
    (i n : ℕ) :
    Native.CosetEnum.sqTest (tT i) (tD i) (wP i) n = true ↔
      qOfEnc n * cosetW i * conjQ (cosetPair i) (qOfEnc n) = 1 := by
  rw [sqTest_eq_isOne, ← pauliQ_eq_one_iff, native_dec]
  exact Iff.of_eq (congrArg (· = 1) (sqProd_eq i (n.testBit 24) (pauliDec_lt n).1
    (pauliDec_lt n).2))

theorem countBelow_eq (p : ℕ → Bool) : ∀ m acc, Native.CosetEnum.countBelow p m acc =
    acc + ((Finset.range m).filter fun n => p n = true).card
  | 0, acc => by simp [Native.CosetEnum.countBelow]
  | m + 1, acc => by
    rw [Native.CosetEnum.countBelow, countBelow_eq p m, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : p m = true
    · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
      omega
    · simp [h]

theorem countSq_eq (tA tB : Array Model.Pauli) (w : Model.Pauli) :
    Native.CosetEnum.countSq tA tB w =
      ((Finset.range (2 ^ 25)).filter fun n => Native.CosetEnum.sqTest tA tB w n = true).card := by
  rw [Native.CosetEnum.countSq, countBelow_eq, zero_add]

@[expose] def cosetInv
    (i : ℕ) : Set Gvis := {f | f ∈ cosetR i ∧ f * f = 1}

@[expose] def cosetElt
    (i n : ℕ) : Gvis := cosetRep i * rhoGvis (qOfEnc n)

theorem cosetElt_injective
    (i : ℕ) {n n' : ℕ} (hn : n < 2 ^ 25) (hn' : n' < 2 ^ 25)
    (h : cosetElt i n = cosetElt i n') : n = n' :=
  qOfEnc_injective hn hn' (rhoGvis_injective (mul_left_cancel h))

theorem mem_cosetR_iff_enc
    (i : ℕ) (f : Gvis) : f ∈ cosetR i ↔ ∃ n < 2 ^ 25, f = cosetElt i n := by
  rw [mem_cosetR_iff_exists]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨s, hs, A, hA, D, hD, rfl⟩ := exists_qP r
    refine ⟨pauliEnc s A D, pauliEnc_lt hs hA hD, Subtype.ext ?_⟩
    rw [hr, cosetElt, qOfEnc_pauliEnc hs hA hD]
    rfl
  · rintro ⟨n, -, rfl⟩
    exact ⟨qOfEnc n, rfl⟩

theorem cosetInv_eq
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) :
    cosetInv i = cosetElt i '' {n | n < 2 ^ 25 ∧
      Native.CosetEnum.sqTest (tT i) (tD i) (wP i) n = true} := by
  ext f
  constructor
  · rintro ⟨hf, hsq⟩
    obtain ⟨n, hn, rfl⟩ := (mem_cosetR_iff_enc i f).1 hf
    refine ⟨n, ⟨hn, (sqTest_iff i n).2 ?_⟩, rfl⟩
    have h := (mul_rho_sq hi (qOfEnc n)).symm.trans hsq
    exact rhoGvis_injective (h.trans rhoGvis_one.symm)
  · rintro ⟨n, ⟨hn, ht⟩, rfl⟩
    refine ⟨(mem_cosetR_iff_enc i _).2 ⟨n, hn, rfl⟩, ?_⟩
    rw [cosetElt, mul_rho_sq hi, (sqTest_iff i n).1 ht, rhoGvis_one]

theorem ncard_cosetInv
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) :
    (cosetInv i).ncard = Native.CosetEnum.countSq (tT i) (tD i) (wP i) := by
  rw [cosetInv_eq hi, Set.InjOn.ncard_image fun n hn n' hn' h =>
    cosetElt_injective i hn.1 hn'.1 h, countSq_eq, ← Set.ncard_coe_finset]
  congr 1
  ext n
  simp

theorem qOfEnc_act
    (i : ℕ) {k : ℕ} (hk : k < 24) (n : ℕ) :
    qOfEnc (Native.CosetEnum.act (imgs i) k n) =
      (conjQ (cosetPair i) (gQ k))⁻¹ * qOfEnc n * gQ k := by
  rw [Native.CosetEnum.act, qOfEnc_enc]
  simp only [native_mul_apply, native_dec_apply, native_gen_apply, pauliQ_mul, pauliQ_inv,
    imgs_get i hk, ← conjQ_cosetPair, mul_assoc]
  rfl

theorem cosetElt_act
    (i : ℕ) {k : ℕ} (hk : k < 24) (n : ℕ) :
    cosetElt i (Native.CosetEnum.act (imgs i) k n) =
      ConjAct.toConjAct (rhoGvis (conjQ (cosetPair i) (gQ k))) • cosetElt i n := by
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, cosetElt, cosetElt, conj_mul_rho,
    qOfEnc_act i hk]

theorem qmatClass_eq_of_natCertOK
    (i : ℕ) {root : ℕ} {c : NatCert}
    (h : natCertOK (Native.CosetEnum.act (imgs i)) 24 (fun n => decide (n < 2 ^ 25)) root c =
      true) :
    qmatClass (cosetElt i root) = (fun j => cosetElt i c.pts[j]!) '' {j | j < c.pts.size} := by
  rw [← orbit_closure_conjAct (cosetPair i)]
  exact orbit_of_natCertOK h fun k hk a _ => cosetElt_act i hk a

theorem ncard_qmatClass_of_natCertOK
    (i : ℕ) {root : ℕ} {c : NatCert}
    (h : natCertOK (Native.CosetEnum.act (imgs i)) 24 (fun n => decide (n < 2 ^ 25)) root c =
      true) :
    (qmatClass (cosetElt i root)).ncard = c.pts.size := by
  rw [← orbit_closure_conjAct (cosetPair i)]
  exact ncard_orbit_of_natCertOK h (fun k hk a _ => cosetElt_act i hk a)
    fun a b ha hb e => cosetElt_injective i (of_decide_eq_true ha) (of_decide_eq_true hb) e

theorem mem_pts_of_natCertOK
    (i : ℕ) {root : ℕ} {c : NatCert}
    (h : natCertOK (Native.CosetEnum.act (imgs i)) 24 (fun n => decide (n < 2 ^ 25)) root c =
      true) {n : ℕ} (hn : n < 2 ^ 25) (hmem : cosetElt i n ∈ qmatClass (cosetElt i root)) :
    ∃ j < c.pts.size, c.pts[j]! = n := by
  rw [qmatClass_eq_of_natCertOK i h] at hmem
  obtain ⟨j, hj, e⟩ := hmem
  exact ⟨j, hj, cosetElt_injective i (of_decide_eq_true (natCertOK_valid h hj)) hn e⟩

end CFSG.Monster.B.TwoA.Census
