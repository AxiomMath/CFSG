module

public import CFSG.Monster.B.Rep4371.RawOrder
public import CFSG.Monster.B.Rep4371.Records

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B

theorem combN_xor (m : ℕ → ℕ) (n a b : ℕ) :
    Model.combN m n (a ^^^ b) = Model.combN m n a ^^^ Model.combN m n b := by
  induction n with
  | zero => simp [Model.combN]
  | succ n ih =>
    rw [Model.combN, Model.combN, Model.combN, ih, Nat.testBit_xor]
    apply Nat.eq_of_testBit_eq
    intro i
    cases a.testBit n <;> cases b.testBit n <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, Nat.testBit_xor, Nat.zero_testBit] <;>
      cases (Model.combN m n a).testBit i <;> cases (Model.combN m n b).testBit i <;>
      cases (m n).testBit i <;> rfl

theorem wordN_xor (a b : ℕ) : Model.wordN (a ^^^ b) = Model.wordN a ^^^ Model.wordN b :=
  combN_xor _ _ _ _

theorem toD_191 : toD 191 = deltaPair 0 1 := by
  have hd : Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((1 : Fin 24) : ℕ)) = 191 := by decide
  rw [deltaPair_eq_toD (by decide), hd]

theorem pair_deltaPair_01 (a : C) :
    pair a (deltaPair 0 1) = (a : Fin 24 → ZMod 2) 0 + (a : Fin 24 → ZMod 2) 1 := by
  rw [deltaPair, pair_mk, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]

theorem pairN_191 (x : ℕ) :
    Model.pairN x 191 = ((Model.wordN x).testBit 0 ^^ (Model.wordN x).testBit 1) := by
  apply boolZ_injective
  rw [← pair_toC_toD, toD_191, pair_deltaPair_01, coe_toC, bvec_eq_boolZ, bvec_eq_boolZ,
    boolZ_xor]
  rfl

theorem testBit_wordN_63 (i : Fin 24) : (Model.wordN 63).testBit i = true := by
  revert i
  decide

theorem Xlift_labelElt (l : ShortLabel) : Xlift (labelElt l) = Pi.single (labelIdx l) 1 := by
  rw [Xlift_eq (isShortCoord_labelElt l), centralCoord_labelElt, sgn_zero, one_smul]
  rfl

@[expose] def pairLab (e : Bool) (n : ℕ) : LtPair :=
  if h : 2 ≤ n ∧ n ≤ 23 then
    ⟨(if e then 1 else 0, fin24 n), by
      rw [Fin.lt_def]
      cases e <;> simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_zero, Fin.val_one, fin24] <;>
        rw [Nat.mod_eq_of_lt (by omega)] <;> omega⟩
  else ⟨(0, 1), by decide⟩

theorem pairLab_val {e : Bool} {n : ℕ} (h : 2 ≤ n ∧ n ≤ 23) :
    (pairLab e n).1 = (if e then 1 else 0, fin24 n) := by
  rw [pairLab, dite_eq_left h]

@[expose] noncomputable def xLab (hoct : Model.octDataOK = true) (k : ℕ) (e : Bool) : ShortLabel :=
  if k ≤ 66 then
    if (k - 23) % 2 = 0 then .inl (pairLab e ((k - 23) / 2 + 2))
    else .inr (.inl (pairLab e ((k - 23) / 2 + 2)))
  else if k ≤ 1090 then .inr (.inr (.inl (oddC (k - 67), if e then 1 else 0)))
  else if hb : (k - 1091) / 16 < 77 then
    .inr (.inr (.inr ⟨octadW hoct hb, Octad.cls _ (octSet ((k - 1091) / 16)
      (if e then (Model.localPairs[(k - 1091) % 16]!).2
        else (Model.localPairs[(k - 1091) % 16]!).1))⟩))
  else .inl (pairLab e 2)

theorem val_fin24 {n : ℕ} (h : n < 24) : (fin24 n : ℕ) = n := Nat.mod_eq_of_lt h

theorem localPair_even {i : ℕ} (hi : i < 16) (e : Bool) :
    (if e then (Model.localPairs[i]!).2 else (Model.localPairs[i]!).1) < 256 ∧
      Model.popcN 8 (if e then (Model.localPairs[i]!).2 else (Model.localPairs[i]!).1) % 2 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := localPairs_facts i hi
  cases e
  · exact ⟨h1, h3⟩
  · exact ⟨h2, h4⟩

theorem labelElt_xLab_oct (hoct : Model.octDataOK = true) {k : ℕ} (h4 : 1091 ≤ k) (h2 : k ≤ 2322)
    (e : Bool) :
    labelElt (xLab hoct k e) = rOct (octC ((k - 1091) / 16)) (octSet ((k - 1091) / 16)
      (if e then (Model.localPairs[(k - 1091) % 16]!).2
        else (Model.localPairs[(k - 1091) % 16]!).1)) := by
  have hb : (k - 1091) / 16 < 77 := by omega
  have hi : (k - 1091) % 16 < 16 := Nat.mod_lt _ (by norm_num)
  obtain ⟨hx, hxe⟩ := localPair_even hi e
  rw [xLab, ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_right (by omega : ¬ k ≤ 1090),
    dite_eq_left hb]
  exact rOctQ_cls (octSet_subset hoct hb hx)
    (by rw [card_octSet' hoct hb hx]; exact even_of_popcN hxe)

theorem Rraw_xLab (hoct : Model.octDataOK = true) {k : ℕ} (h1 : 23 ≤ k) (h2 : k ≤ 2322) :
    Rraw k = inX (Xlift (labelElt (xLab hoct k false)) - Xlift (labelElt (xLab hoct k true))) := by
  rcases Nat.lt_or_ge k 67 with h3 | h3
  · have hn : 2 ≤ (k - 23) / 2 + 2 ∧ (k - 23) / 2 + 2 ≤ 23 := by omega
    by_cases hp : (k - 23) % 2 = 0
    · rw [Rraw_D_eq h1 (by omega) hp, xLab, xLab, ite_eq_left (by omega : k ≤ 66), ite_eq_left hp,
        ite_eq_left (by omega : k ≤ 66), ite_eq_left hp]
      simp only [labelElt, pairLab_val hn, Bool.false_eq_true, ↓reduceIte]
      rfl
    · rw [Rraw_P_eq h1 (by omega) hp, xLab, xLab, ite_eq_left (by omega : k ≤ 66), ite_eq_right hp,
        ite_eq_left (by omega : k ≤ 66), ite_eq_right hp]
      simp only [labelElt, pairLab_val hn, Bool.false_eq_true, ↓reduceIte]
      rfl
  rcases Nat.lt_or_ge k 1091 with h4 | h4
  · rw [Rraw_odd_eq h3 (by omega), xLab, xLab, ite_eq_right (by omega : ¬ k ≤ 66),
      ite_eq_left (by omega : k ≤ 1090), ite_eq_right (by omega : ¬ k ≤ 66),
      ite_eq_left (by omega : k ≤ 1090)]
    rfl
  · rw [Rraw_oct_eq h4 h2, labelElt_xLab_oct hoct h4 h2, labelElt_xLab_oct hoct h4 h2]
    rfl

theorem pauliQ_congr {x y : Model.Pauli} (hs : x.1 = y.1) (ha : x.2.1 = y.2.1)
    (hd : toD x.2.2 = toD y.2.2) : pauliQ x = pauliQ y := by
  unfold pauliQ
  exact congrArg spinEquiv (SpinCoord.ext (congrArg boolZ hs) (congrArg toC ha) hd)

theorem rStar_mul_pauliQ (a d : ℕ) :
    Short.rStar * pauliQ (false, a, d) = pauliQ (Model.pairN a 191, a, 191 ^^^ d) := by
  rw [rStar_eq, ← pauliQ_mul]
  congr 1
  simp only [Model.Pauli.mul, pauli_s, pauli_a, pauli_d, Bool.false_xor, Nat.zero_xor]

theorem dualN_pair01 : ∀ n < 24, 2 ≤ n →
    191 ^^^ Model.dualN (2 ^ 0 ||| 2 ^ n) = Model.dualN (2 ^ 1 ||| 2 ^ n) := by
  decide

theorem testBit_01_of_mod_four {n : ℕ} (h : n % 4 = 3) : n.testBit 0 = true ∧ n.testBit 1 = true := by
  rw [Nat.testBit_zero, Nat.testBit_succ, Nat.testBit_zero]
  exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩

theorem wordN_zero : Model.wordN 0 = 0 := by decide

theorem testBit_wordN_63_zero : (Model.wordN 63).testBit 0 = true := by decide

theorem testBit_wordN_63_one : (Model.wordN 63).testBit 1 = true := by decide

theorem pairN_xor_63 {a : ℕ} (b : Bool) (h : (Model.wordN a).testBit 0 = (Model.wordN a).testBit 1) :
    Model.pairN (a ^^^ (if b then 63 else 0)) 191 = false := by
  rw [pairN_191, wordN_xor, Nat.testBit_xor, Nat.testBit_xor, h]
  cases b
  · rw [ite_eq_right (by decide), wordN_zero, Nat.zero_testBit, Nat.zero_testBit]
    cases (Model.wordN a).testBit 1 <;> rfl
  · rw [ite_eq_left rfl, testBit_wordN_63_zero, testBit_wordN_63_one]
    cases (Model.wordN a).testBit 1 <;> rfl

theorem spreadN_three (d : ℕ) : Model.spreadN d 3 = 3 := by
  simp only [Model.spreadN, Model.combN, show (3 : ℕ).testBit 2 = false from rfl,
    show (3 : ℕ).testBit 3 = false from rfl, show (3 : ℕ).testBit 4 = false from rfl,
    show (3 : ℕ).testBit 5 = false from rfl, show (3 : ℕ).testBit 6 = false from rfl,
    show (3 : ℕ).testBit 7 = false from rfl, show (3 : ℕ).testBit 0 = true from rfl,
    show (3 : ℕ).testBit 1 = true from rfl, Model.localOrder]
  simp

theorem spreadN_xor_three (d x : ℕ) : Model.spreadN d (x ^^^ 3) = Model.spreadN d x ^^^ 3 := by
  have h := spreadN_three d
  unfold Model.spreadN at h ⊢
  rw [combN_xor, h]

theorem localPairs_popc : ∀ i < 16,
    Model.popcN 8 (Model.localPairs[i]!).1 = Model.popcN 8 (Model.localPairs[i]!).2 := by
  decide

theorem localPairs_xor : ∀ i < 16, (Model.localPairs[i]!).2 = (Model.localPairs[i]!).1 ^^^ 3 := by
  decide

theorem xLab_minus (hoct : Model.octDataOK = true) {k : ℕ} (h3 : k ≤ 66) (hp : (k - 23) % 2 = 0)
    (e : Bool) : xLab hoct k e = .inl (pairLab e ((k - 23) / 2 + 2)) := by
  rw [xLab, ite_eq_left h3, ite_eq_left hp]

theorem xLab_plus (hoct : Model.octDataOK = true) {k : ℕ} (h3 : k ≤ 66) (hp : ¬ (k - 23) % 2 = 0)
    (e : Bool) : xLab hoct k e = .inr (.inl (pairLab e ((k - 23) / 2 + 2))) := by
  rw [xLab, ite_eq_left h3, ite_eq_right hp]

theorem xLab_odd (hoct : Model.octDataOK = true) {k : ℕ} (h3 : 67 ≤ k) (h4 : k ≤ 1090) (e : Bool) :
    xLab hoct k e = .inr (.inr (.inl (oddC (k - 67), if e then 1 else 0))) := by
  rw [xLab, ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_left h4]

theorem getElem!_mem_toList {A : Array ℕ} {t : ℕ} (h : t < A.size) : A[t]! ∈ A.toList := by
  rw [getElem!_pos A t h]
  exact Array.mem_toList_iff.2 (Array.getElem_mem h)

theorem oddCodes_mem {t : ℕ} (ht : t < 1024) : Model.oddCodes[t]! ∈ Model.oddCodes.toList :=
  getElem!_mem_toList (oddCodes_size.symm ▸ ht)

theorem oddCode_zero_one {t : ℕ} (ht : t < 1024) :
    Model.oddCode Model.oddCodes[t]! 0 = Model.oddCode Model.oddCodes[t]! 1 := by
  have hbits := ((mem_oddCodes_iff _).1 (oddCodes_mem ht)).2.2
  unfold Model.oddCode
  rw [hbits]

theorem rStar_mul_rOct (hoct : Model.octDataOK = true) {b : ℕ} (hb : b < 77) {i : ℕ}
    (hi : i < 16) :
    Short.rStar * rOct (octC b) (octSet b (Model.localPairs[i]!).1) =
      rOct (octC b) (octSet b (Model.localPairs[i]!).2) := by
  obtain ⟨hx, hx', -, -⟩ := localPairs_facts i hi
  have hxx := localPairs_xor i hi
  have hpop := localPairs_popc i hi
  generalize (Model.localPairs[i]!).1 = x at hx hxx hpop ⊢
  generalize (Model.localPairs[i]!).2 = x' at hx' hxx hpop ⊢
  have hcode : Model.octCode Model.octCoeffs[b]! x = Model.octCode Model.octCoeffs[b]! x' := by
    rw [Model.octCode, Model.octCode, (oct_facts hoct hb hx hx).2.1,
      (oct_facts hoct hb hx' hx').2.1, hpop]
  have hbits := testBit_01_of_mod_four (octCoeffs_mem hoct hb).2
  rw [← pauliQ_oct b x, ← pauliQ_oct b x', rStar_mul_pauliQ]
  refine pauliQ_congr ?_ hcode ?_
  · show Model.pairN (Model.octCode Model.octCoeffs[b]! x) 191 = false
    unfold Model.octCode
    exact pairN_xor_63 _ (hbits.1.trans hbits.2.symm)
  · show toD (191 ^^^ (Model.thetaN (Model.octCode Model.octCoeffs[b]! x) ^^^
        Model.dualN (Model.spreadN (Model.wordN Model.octCoeffs[b]!) x))) =
      toD (Model.thetaN (Model.octCode Model.octCoeffs[b]! x') ^^^
        Model.dualN (Model.spreadN (Model.wordN Model.octCoeffs[b]!) x'))
    have h3' : (Submodule.Quotient.mk (bvec 24 3) : Cocode) = deltaPair 0 1 := by
      rw [deltaPair, ← bvec_two_pow_or (by decide : (0 : Fin 24) ≠ 1)]
      rfl
    rw [← hcode, toD_xor, toD_xor, toD_xor, ← mk_bvec_eq_toD, ← mk_bvec_eq_toD, hxx,
      spreadN_xor_three, bvec_xor, Submodule.Quotient.mk_add, toD_191, h3']
    abel

theorem rStar_mul_xLab (hoct : Model.octDataOK = true) {k : ℕ} (h1 : 23 ≤ k) (h2 : k ≤ 2322) :
    Short.rStar * labelElt (xLab hoct k false) = labelElt (xLab hoct k true) := by
  rcases Nat.lt_or_ge k 67 with h3 | h3
  · have hn : 2 ≤ (k - 23) / 2 + 2 ∧ (k - 23) / 2 + 2 ≤ 23 := by omega
    have hv : (fin24 ((k - 23) / 2 + 2) : ℕ) = (k - 23) / 2 + 2 := val_fin24 (by omega)
    have h0 : (0 : Fin 24) ≠ fin24 ((k - 23) / 2 + 2) := fun h => by
      have := congrArg Fin.val h
      rw [hv, Fin.val_zero] at this
      omega
    have h1' : (1 : Fin 24) ≠ fin24 ((k - 23) / 2 + 2) := fun h => by
      have := congrArg Fin.val h
      rw [hv, Fin.val_one] at this
      omega
    have hd := dualN_pair01 ((k - 23) / 2 + 2) (by omega) (by omega)
    by_cases hp : (k - 23) % 2 = 0
    · rw [xLab_minus hoct (by omega) hp, xLab_minus hoct (by omega) hp]
      simp only [labelElt, pairLab_val hn, Bool.false_eq_true, ↓reduceIte]
      rw [← pauliQ_minus h0, ← pauliQ_minus h1', rStar_mul_pauliQ, hv, Fin.val_zero, Fin.val_one,
        hd]
      rfl
    · rw [xLab_plus hoct (by omega) hp, xLab_plus hoct (by omega) hp]
      simp only [labelElt, pairLab_val hn, Bool.false_eq_true, ↓reduceIte]
      rw [← pauliQ_plus h0, ← pauliQ_plus h1', rStar_mul_pauliQ, hv, Fin.val_zero, Fin.val_one,
        hd]
      rfl
  rcases Nat.lt_or_ge k 1091 with h4 | h4
  · rw [xLab_odd hoct h3 (by omega), xLab_odd hoct h3 (by omega)]
    simp only [labelElt, Bool.false_eq_true, ↓reduceIte]
    have ht : k - 67 < 1024 := by omega
    have hbits := ((mem_oddCodes_iff _).1 (oddCodes_mem ht)).2.2
    have hc := oddCode_zero_one ht
    rw [← pauliQ_odd (k - 67) 0, ← pauliQ_odd (k - 67) 1, Fin.val_zero, Fin.val_one,
      rStar_mul_pauliQ]
    refine pauliQ_congr ?_ hc ?_
    · show Model.pairN (Model.oddCode Model.oddCodes[k - 67]! 0) 191 = false
      unfold Model.oddCode
      exact pairN_xor_63 _ hbits
    · show toD (191 ^^^ (Model.thetaN (Model.oddCode Model.oddCodes[k - 67]! 0) ^^^
        Model.dualN (2 ^ 0))) = toD (Model.thetaN (Model.oddCode Model.oddCodes[k - 67]! 1) ^^^
        Model.dualN (2 ^ 1))
      have h191 : 191 ^^^ Model.dualN (2 ^ 0) = Model.dualN (2 ^ 1) := by decide
      rw [← hc, ← Nat.xor_assoc, Nat.xor_comm 191, Nat.xor_assoc, h191]
  · have hb : (k - 1091) / 16 < 77 := by omega
    have hi : (k - 1091) % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have e1 := labelElt_xLab_oct hoct h4 h2 false
    have e2 := labelElt_xLab_oct hoct h4 h2 true
    simp only [Bool.false_eq_true, ↓reduceIte] at e1 e2
    exact (congrArg (Short.rStar * ·) e1).trans ((rStar_mul_rOct hoct hb hi).trans e2.symm)

theorem toC_inj {a b : ℕ} (ha : a < 4096) (hb : b < 4096) (h : toC a = toC b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have := congrArg (fun x => basisC.repr x ⟨i, hi⟩) h
    simp only [repr_toC_apply] at this
    exact boolZ_injective this
  · have h2 : 4096 ≤ 2 ^ i :=
      le_trans (by norm_num : 4096 ≤ 2 ^ 12) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem getElem!_inj_of_nodup {A : Array ℕ} (hA : A.toList.Nodup) {t t' : ℕ} (ht : t < A.size)
    (ht' : t' < A.size) (h : A[t]! = A[t']!) : t = t' := by
  rw [getElem!_pos A t ht, getElem!_pos A t' ht',
    ← Array.getElem_toList (by simpa using ht), ← Array.getElem_toList (by simpa using ht')] at h
  exact hA.getElem_inj_iff.1 h

theorem oddCodes_lt {t : ℕ} (ht : t < 1024) : Model.oddCodes[t]! < 4096 :=
  ((mem_oddCodes_iff _).1 (oddCodes_mem ht)).1

theorem oddC_inj {t t' : ℕ} (ht : t < 1024) (ht' : t' < 1024) (h : oddC t = oddC t') : t = t' := by
  have h1 : toC Model.oddCodes[t]! = toC Model.oddCodes[t']! := by rw [← coe_oddC, ← coe_oddC, h]
  exact getElem!_inj_of_nodup oddCodes_sorted.nodup (oddCodes_size.symm ▸ ht)
    (oddCodes_size.symm ▸ ht') (toC_inj (oddCodes_lt ht) (oddCodes_lt ht') h1)

theorem octCoeffs_nodup : Model.octCoeffs.toList.Nodup := by
  rw [Model.octCoeffs, Model.octCoeffsOf, List.toList_toArray]
  exact (List.mergeSort_perm _ _).nodup_iff.2 (List.nodup_range.filter _)

theorem octCoeffs_lt (hoct : Model.octDataOK = true) {b : ℕ} (hb : b < 77) :
    Model.octCoeffs[b]! < 4096 :=
  ((mem_octCoeffs_iff _).1 (getElem!_mem_toList ((octCoeffs_size hoct).symm ▸ hb))).1

theorem octadW_inj (hoct : Model.octDataOK = true) {b b' : ℕ} (hb : b < 77) (hb' : b' < 77)
    (h : octadW hoct hb = octadW hoct hb') : b = b' := by
  have h1 : toC Model.octCoeffs[b]! = toC Model.octCoeffs[b']! := congrArg Subtype.val h
  exact getElem!_inj_of_nodup octCoeffs_nodup ((octCoeffs_size hoct).symm ▸ hb)
    ((octCoeffs_size hoct).symm ▸ hb') (toC_inj (octCoeffs_lt hoct hb) (octCoeffs_lt hoct hb') h1)

theorem localPairs_masks : ∀ i < 16, ∀ j < 16, ∀ e e' : Bool,
    ((if e then (Model.localPairs[i]!).2 else (Model.localPairs[i]!).1) =
        (if e' then (Model.localPairs[j]!).2 else (Model.localPairs[j]!).1) ∨
      (if e then (Model.localPairs[i]!).2 else (Model.localPairs[i]!).1) =
        (if e' then (Model.localPairs[j]!).2 else (Model.localPairs[j]!).1) ^^^ 255) →
    i = j ∧ e = e' := by
  decide

theorem octLab_inj (hoct : Model.octDataOK = true) {b b' : ℕ} (hb : b < 77) (hb' : b' < 77)
    {x x' : ℕ} (hx : x < 256) (hxe : Model.popcN 8 x % 2 = 0) (hx' : x' < 256)
    (hxe' : Model.popcN 8 x' % 2 = 0)
    (h : (⟨octadW hoct hb, Octad.cls _ (octSet b x)⟩ : OctIdx) =
      ⟨octadW hoct hb', Octad.cls _ (octSet b' x')⟩) :
    b = b' ∧ (x = x' ∨ x = x' ^^^ 255) := by
  have hbb := octadW_inj hoct hb hb' (congrArg Sigma.fst h)
  subst hbb
  refine ⟨rfl, ?_⟩
  have h2 := eq_of_heq (Sigma.mk.inj_iff.1 h).2
  exact (cls_octSet_eq_iff hoct hb hx hxe hx' hxe').1 h2

theorem pairLab_inj {e e' : Bool} {n n' : ℕ} (hn : 2 ≤ n ∧ n ≤ 23) (hn' : 2 ≤ n' ∧ n' ≤ 23)
    (h : pairLab e n = pairLab e' n') : e = e' ∧ n = n' := by
  have h1 := congrArg Subtype.val h
  rw [pairLab_val hn, pairLab_val hn'] at h1
  have h2 := congrArg (fun p => (p.2 : ℕ)) h1
  have h3 := congrArg (fun p => (p.1 : ℕ)) h1
  simp only [val_fin24 (by omega : n < 24), val_fin24 (by omega : n' < 24)] at h2
  refine ⟨?_, h2⟩
  cases e <;> cases e' <;> simp_all

theorem xLab_injective (hoct : Model.octDataOK = true) {k k' : ℕ} (h1 : 23 ≤ k) (h2 : k ≤ 2322)
    (h1' : 23 ≤ k') (h2' : k' ≤ 2322) {e e' : Bool} (h : xLab hoct k e = xLab hoct k' e') :
    k = k' ∧ e = e' := by
  have hn : ∀ k, 23 ≤ k → k ≤ 66 → 2 ≤ (k - 23) / 2 + 2 ∧ (k - 23) / 2 + 2 ≤ 23 := fun k h h' =>
    ⟨by omega, by omega⟩
  have ho : ∀ k (h4 : 1091 ≤ k) (h2 : k ≤ 2322) (e : Bool), xLab hoct k e = .inr (.inr (.inr
      ⟨octadW hoct (by omega : (k - 1091) / 16 < 77), Octad.cls _ (octSet ((k - 1091) / 16)
        (if e then (Model.localPairs[(k - 1091) % 16]!).2
          else (Model.localPairs[(k - 1091) % 16]!).1))⟩)) := fun k h4 h2 e => by
    rw [xLab, ite_eq_right (by omega : ¬ k ≤ 66), ite_eq_right (by omega : ¬ k ≤ 1090),
      dite_eq_left (by omega : (k - 1091) / 16 < 77)]
  rcases Nat.lt_or_ge k 67 with h3 | h3 <;> rcases Nat.lt_or_ge k' 67 with h3' | h3'
  · by_cases hp : (k - 23) % 2 = 0 <;> by_cases hp' : (k' - 23) % 2 = 0
    · rw [xLab_minus hoct (by omega) hp, xLab_minus hoct (by omega) hp'] at h
      obtain ⟨he, hk⟩ := pairLab_inj (hn k h1 (by omega)) (hn k' h1' (by omega)) (Sum.inl_injective h)
      exact ⟨by omega, he⟩
    · rw [xLab_minus hoct (by omega) hp, xLab_plus hoct (by omega) hp'] at h
      exact absurd h Sum.inl_ne_inr
    · rw [xLab_plus hoct (by omega) hp, xLab_minus hoct (by omega) hp'] at h
      exact absurd h.symm Sum.inl_ne_inr
    · rw [xLab_plus hoct (by omega) hp, xLab_plus hoct (by omega) hp'] at h
      obtain ⟨he, hk⟩ := pairLab_inj (hn k h1 (by omega)) (hn k' h1' (by omega))
        (Sum.inl_injective (Sum.inr_injective h))
      exact ⟨by omega, he⟩
  · exfalso
    have hl : ∃ q, xLab hoct k e = .inl q ∨ xLab hoct k e = .inr (.inl q) := by
      by_cases hp : (k - 23) % 2 = 0
      · exact ⟨_, Or.inl (xLab_minus hoct (by omega) hp e)⟩
      · exact ⟨_, Or.inr (xLab_plus hoct (by omega) hp e)⟩
    have hr : ∃ q, xLab hoct k' e' = .inr (.inr q) := by
      rcases Nat.lt_or_ge k' 1091 with h4' | h4'
      · exact ⟨_, xLab_odd hoct h3' (by omega) e'⟩
      · exact ⟨_, ho k' h4' h2' e'⟩
    obtain ⟨q, hq | hq⟩ := hl <;> obtain ⟨q', hq'⟩ := hr <;> rw [hq, hq'] at h
    · exact Sum.inl_ne_inr h
    · exact Sum.inl_ne_inr (Sum.inr_injective h)
  · exfalso
    have hl : ∃ q, xLab hoct k' e' = .inl q ∨ xLab hoct k' e' = .inr (.inl q) := by
      by_cases hp : (k' - 23) % 2 = 0
      · exact ⟨_, Or.inl (xLab_minus hoct (by omega) hp e')⟩
      · exact ⟨_, Or.inr (xLab_plus hoct (by omega) hp e')⟩
    have hr : ∃ q, xLab hoct k e = .inr (.inr q) := by
      rcases Nat.lt_or_ge k 1091 with h4 | h4
      · exact ⟨_, xLab_odd hoct h3 (by omega) e⟩
      · exact ⟨_, ho k h4 h2 e⟩
    obtain ⟨q, hq | hq⟩ := hl <;> obtain ⟨q', hq'⟩ := hr <;> rw [hq, hq'] at h
    · exact Sum.inl_ne_inr h.symm
    · exact Sum.inl_ne_inr (Sum.inr_injective h).symm
  · rcases Nat.lt_or_ge k 1091 with h4 | h4 <;> rcases Nat.lt_or_ge k' 1091 with h4' | h4'
    · rw [xLab_odd hoct h3 (by omega), xLab_odd hoct h3' (by omega)] at h
      have h' := Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))
      have ht := oddC_inj (by omega) (by omega) (congrArg Prod.fst h')
      have he := congrArg Prod.snd h'
      refine ⟨by omega, ?_⟩
      cases e <;> cases e' <;> simp_all
    · rw [xLab_odd hoct h3 (by omega), ho k' h4' h2' e'] at h
      exact absurd (Sum.inr_injective (Sum.inr_injective h)) Sum.inl_ne_inr
    · rw [ho k h4 h2 e, xLab_odd hoct h3' (by omega)] at h
      exact absurd (Sum.inr_injective (Sum.inr_injective h)).symm Sum.inl_ne_inr
    · rw [ho k h4 h2 e, ho k' h4' h2' e'] at h
      have hi : (k - 1091) % 16 < 16 := Nat.mod_lt _ (by norm_num)
      have hi' : (k' - 1091) % 16 < 16 := Nat.mod_lt _ (by norm_num)
      obtain ⟨hx, hxe⟩ := localPair_even hi e
      obtain ⟨hx', hxe'⟩ := localPair_even hi' e'
      obtain ⟨hb, hm⟩ := octLab_inj hoct _ _ hx hxe hx' hxe'
        (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h)))
      obtain ⟨hii, hee⟩ := localPairs_masks _ hi _ hi' e e' hm
      exact ⟨by omega, hee⟩

end CFSG.Monster.B.Rep4371
