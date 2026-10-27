module

public import CFSG.Monster.B.CTIB.Defs
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3027
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native Matrix
  CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.Griess

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

abbrev WS : Type := Wv (phi0 (coordOf rStar))

theorem gArr_getD (i : ℕ) : gArr.getD i 0 = Bin.gramRows.getD i 0 := by
  rw [gArr, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem gram_bits_symm :
    ∀ i < 22, ∀ j < 22, (Bin.gramRows.getD i 0).testBit j = (Bin.gramRows.getD j 0).testBit i := by
  decide

theorem decMat_gram (i j : Fin 22) :
    Max2.decMat CFSG.Monster.B.gramRows i j = if (gArr.getD j 0).testBit i then 1 else 0 := by
  rw [Max2.decMat, Matrix.of_apply, gramRows_eq i i.2, Code.bvec_apply, gArr_getD,
    gram_bits_symm i i.2 j j.2]

theorem es_mem (i : ℕ) : es i ∈ Qs := eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar i

theorem xs_mem : xs ∈ Qs := xbar_mem_Ebar

theorem xs_mul_self : xs * xs = 1 := by
  rw [xs, ← op_mul, xbar_mul_self, op_one]

theorem xs_comm {s : Sbp} (hs : s ∈ Qs) : xs * s = s * xs := by
  have h := xbar_comm_of_mem_Ebar (y := s.unop) hs
  apply unop_injective
  rw [unop_mul, unop_mul, xs, unop_op, h]

theorem es_mul_self (i : ℕ) : es i * es i = 1 := by
  have he : op (gSeq 0) * op (gSeq 0) = 1 := by rw [← op_mul, gSeq_zero_mul_self, op_one]
  rw [es, eS]
  calc (wordS gSeq (basisWord.take (basisLens.getD i 0)))⁻¹ * op (gSeq 0) *
        wordS gSeq (basisWord.take (basisLens.getD i 0)) *
        ((wordS gSeq (basisWord.take (basisLens.getD i 0)))⁻¹ * op (gSeq 0) *
          wordS gSeq (basisWord.take (basisLens.getD i 0)))
      = (wordS gSeq (basisWord.take (basisLens.getD i 0)))⁻¹ * (op (gSeq 0) * op (gSeq 0)) *
        wordS gSeq (basisWord.take (basisLens.getD i 0)) := by group
    _ = 1 := by rw [he, mul_one, inv_mul_cancel]

theorem es_comm
    (i j : Fin 22) :
    es i * es j = es j * es i * xpow xs ((gArr.getD j 0).testBit i) := by
  have hc := commutator_eS betaS_explicit i j
  rw [decMat_gram] at hc
  have hx : xpow xs ((gArr.getD j 0).testBit i) =
      op xbar ^ (if (gArr.getD j 0).testBit i then (1 : ZMod 2) else 0).val := by
    by_cases h : (gArr.getD j 0).testBit i
    · rw [ite_eq_left h, xpow, ite_eq_left h, ZMod.val_one, pow_one]; rfl
    · rw [ite_eq_right h, xpow, ite_eq_right h, ZMod.val_zero, pow_zero]
  rw [hx, ← hc, es, es]
  group

theorem extraRel :
    ExtraRel es xs gArr where
  e_sq i _ := es_mul_self i
  x_sq := xs_mul_self
  x_comm i _ := xs_comm (es_mem i)
  comm i hi j hj := es_comm ⟨i, hi⟩ ⟨j, hj⟩

theorem qS_mul
    (a b : ℕ) : qS a * qS b = qS (qmul gArr a b) := qOf_mul extraRel a b

theorem qS_zero : qS 0 = 1 := qOf_zero

theorem qS_two_pow {i : ℕ} (hi : i < 22) : qS (2 ^ i) = es i := qOf_two_pow hi

theorem qS_two_pow_22 : qS (2 ^ 22) = xs := qOf_two_pow_22

theorem xpow_mem (b : Bool) : xpow xs b ∈ Qs := by
  cases b
  · exact Qs.one_mem
  · exact xs_mem

theorem ordProd_mem (v n : ℕ) : ordProd es v n ∈ Qs := by
  induction n with
  | zero => exact Qs.one_mem
  | succ n ih =>
    rw [ordProd_succ]
    refine Qs.mul_mem ih ?_
    split_ifs
    · exact es_mem n
    · exact Qs.one_mem

theorem qS_mem (n : ℕ) : qS n ∈ Qs := Qs.mul_mem (xpow_mem _) (ordProd_mem n 22)

open scoped _root_.Classical in
@[expose] noncomputable def psiS (s : Sbp) : WS :=
  if h : s.unop ∈ Ebar then Multiplicative.toAdd (psiBar ⟨s.unop, h⟩) else 0

theorem psiS_of_mem {s : Sbp} (h : s ∈ Qs) :
    psiS s = Multiplicative.toAdd (psiBar ⟨s.unop, h⟩) := by
  unfold psiS
  exact dite_eq_left (show s.unop ∈ Ebar from h)

theorem psiS_mul {a b : Sbp} (ha : a ∈ Qs) (hb : b ∈ Qs) : psiS (a * b) = psiS a + psiS b := by
  rw [psiS_of_mem (Qs.mul_mem ha hb), psiS_of_mem ha, psiS_of_mem hb]
  have e : (⟨(a * b).unop, Qs.mul_mem ha hb⟩ : Ebar) = ⟨b.unop, hb⟩ * ⟨a.unop, ha⟩ :=
    Subtype.ext (unop_mul a b)
  rw [e, map_mul, toAdd_mul, add_comm]

theorem psiS_xs : psiS xs = 0 := by
  rw [psiS_of_mem xs_mem]
  have h : psiBar ⟨xs.unop, xs_mem⟩ = 1 :=
    (psiBar_eq_one_iff _).2 (Or.inr (Subtype.ext rfl))
  rw [h, toAdd_one]

theorem psiS_one : psiS 1 = 0 := by
  rw [psiS_of_mem Qs.one_mem]
  have h : psiBar ⟨(1 : Sbp).unop, Qs.one_mem⟩ = 1 := by
    rw [show (⟨(1 : Sbp).unop, Qs.one_mem⟩ : Ebar) = 1 from Subtype.ext rfl, map_one]
  rw [h, toAdd_one]

theorem psiS_xpow (b : Bool) : psiS (xpow xs b) = 0 := by
  cases b
  · exact psiS_one
  · exact psiS_xs

theorem psiS_ordProd (v n : ℕ) :
    psiS (ordProd es v n) = ∑ i ∈ Finset.range n, if v.testBit i then psiS (es i) else 0 := by
  induction n with
  | zero => rw [Finset.range_zero, Finset.sum_empty]; exact psiS_one
  | succ n ih =>
    rw [ordProd_succ, Finset.sum_range_succ, ← ih]
    split_ifs
    · exact psiS_mul (ordProd_mem v n) (es_mem n)
    · rw [mul_one, add_zero]

theorem psiS_qS (n : ℕ) :
    psiS (qS n) = ∑ i ∈ Finset.range 22, if n.testBit i then psiS (es i) else 0 := by
  rw [qS, qOf, psiS_mul (xpow_mem _) (ordProd_mem n 22), psiS_xpow, zero_add, psiS_ordProd]

theorem eq_of_psiS_eq {a b : Sbp} (ha : a ∈ Qs) (hb : b ∈ Qs) (h : psiS a = psiS b) :
    a = b ∨ a = xs * b := by
  have hab : a.unop * b.unop⁻¹ ∈ Ebar := Ebar.mul_mem ha (Ebar.inv_mem hb)
  have h1 : psiBar ⟨a.unop * b.unop⁻¹, hab⟩ = 1 := by
    have e : (⟨a.unop * b.unop⁻¹, hab⟩ : Ebar) = ⟨a.unop, ha⟩ * (⟨b.unop, hb⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv]
    rw [psiS_of_mem ha, psiS_of_mem hb] at h
    rw [← ofAdd_toAdd (psiBar ⟨a.unop, ha⟩), h, ofAdd_toAdd, mul_inv_cancel]
  rcases (psiBar_eq_one_iff _).1 h1 with h2 | h2
  · left
    have h3 : a.unop * b.unop⁻¹ = 1 := congrArg Subtype.val h2
    exact unop_injective (mul_inv_eq_one.1 h3)
  · right
    have h3 : a.unop * b.unop⁻¹ = xbar := congrArg Subtype.val h2
    have h4 : a = b * xs := by
      apply unop_injective
      rw [unop_mul, xs, unop_op, ← mul_inv_eq_iff_eq_mul.1 h3]
    rw [h4, xs_comm hb]

theorem psiS_es (i : Fin 22) : psiS (es i) = Multiplicative.toAdd (psiBar (eE i)) :=
  psiS_of_mem (es_mem i)

theorem psiS_qS_fin (n : ℕ) :
    psiS (qS n) = ∑ i : Fin 22, (if n.testBit i then (1 : ZMod 2) else 0) •
      Multiplicative.toAdd (psiBar (eE i)) := by
  rw [psiS_qS, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [psiS_es]
  split_ifs <;> simp

theorem testBit_eq_of_psiS
    {n m : ℕ} (h : psiS (qS n) = psiS (qS m)) {i : ℕ} (hi : i < 22) :
    n.testBit i = m.testBit i := by
  rw [psiS_qS_fin, psiS_qS_fin] at h
  have hind := linearIndependent_eE betaS_explicit
  have h0 : ∑ i : Fin 22, ((if n.testBit i then (1 : ZMod 2) else 0) -
      (if m.testBit i then (1 : ZMod 2) else 0)) • Multiplicative.toAdd (psiBar (eE i)) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have hc := Fintype.linearIndependent_iff.1 hind _ h0 ⟨i, hi⟩
  rw [sub_eq_zero] at hc
  cases hn : n.testBit i <;> cases hm : m.testBit i <;> simp_all

theorem xpow_inj {b c : Bool} (h : xpow xs b = xpow xs c) : b = c := by
  have hx : xs ≠ 1 := fun h' => xbar_ne_one (op_injective h')
  cases b <;> cases c <;> simp_all [xpow, eq_comm]

theorem qS_injOn :
    Set.InjOn qS (Set.Iio (2 ^ 23)) := by
  intro n hn m hm h
  have hlow : ∀ i < 22, n.testBit i = m.testBit i := fun i hi =>
    testBit_eq_of_psiS (congrArg psiS h) hi
  have hP : ordProd es n 22 = ordProd es m 22 := ordProd_congr es hlow
  have h22 : n.testBit 22 = m.testBit 22 := by
    rw [qS, qS, qOf, qOf, hP] at h
    exact xpow_inj (mul_right_cancel h)
  apply Nat.eq_of_testBit_eq
  intro i
  rcases lt_trichotomy i 22 with hi | rfl | hi
  · exact hlow i hi
  · exact h22
  · have hn' : n < 2 ^ i := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hm' : m < 2 ^ i := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hn', Nat.testBit_eq_false_of_lt hm']

instance finite_Sbp :
    Finite Sbp :=
  haveI : Finite Cbar := Dyadic.finite_Cbar
  Finite.of_equiv _ MulOpposite.opEquiv

theorem natCard_Qs :
    Nat.card Qs = 2 ^ 23 := by
  rw [← short_centralizer_quotient_local_structure.2.2.2.2.2.2.2.2.1]
  exact Nat.card_congr (MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl).symm

theorem exists_qS
    {g : Sbp} (hg : g ∈ Qs) : ∃ n < 2 ^ 23, qS n = g := by
  have hfin : (Qs : Set Sbp).Finite := Set.toFinite _
  have himg : qS '' Set.Iio (2 ^ 23) ⊆ (Qs : Set Sbp) := by
    rintro _ ⟨n, -, rfl⟩
    exact qS_mem n
  have hcard : (qS '' Set.Iio (2 ^ 23)).ncard = (Qs : Set Sbp).ncard := by
    rw [Set.InjOn.ncard_image qS_injOn, Set.ncard_Iio_nat, ← Nat.card_coe_set_eq]
    exact natCard_Qs.symm
  have heq := Set.eq_of_subset_of_ncard_le himg hcard.ge hfin
  rw [← SetLike.mem_coe, ← heq] at hg
  obtain ⟨n, hn, rfl⟩ := hg
  exact ⟨n, hn, rfl⟩

@[expose] def gBit (i j : ℕ) : ℕ := if (Bin.gramRows.getD i 0).testBit j then 1 else 0

@[expose] def nbit (n i : ℕ) : ℕ := if n.testBit i then 1 else 0

@[expose] def prodCode (n m : ℕ) : ℕ :=
  (n ^^^ m) % 2 ^ 22 + 2 ^ 22 * ((nbit n 22 + nbit m 22 +
    ∑ i ∈ Finset.range 22, ∑ j ∈ Finset.range 22,
      if j < i then nbit n i * nbit m j * gBit i j else 0) % 2)

theorem xor_decide_mod (S T : ℕ) :
    (decide (S % 2 = 1) ^^ decide (T % 2 = 1)) = decide ((S + T) % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one S with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one T with h' | h' <;> simp [h, h', Nat.add_mod]

theorem bool_eq_decide (b : Bool) : b = decide ((if b then 1 else 0) % 2 = 1) := by
  cases b <;> rfl

theorem cAtN_eq_decide (gj u j n : ℕ) :
    cAtN gj u j n = decide ((∑ i ∈ Finset.range n,
      if j < i ∧ u.testBit i ∧ gj.testBit i then 1 else 0) % 2 = 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cAtN_succ, ih, Finset.sum_range_succ, bool_eq_decide (decide (j < n) && _ && _),
      xor_decide_mod]
    congr 3
    by_cases h1 : j < n <;> by_cases h2 : u.testBit n <;> by_cases h3 : gj.testBit n <;>
      simp [h1, h2, h3]

theorem corrN_eq_decide (a b m : ℕ) :
    corrN gArr a b m = decide ((∑ j ∈ Finset.range m, if b.testBit j then
      ∑ i ∈ Finset.range 22, (if j < i ∧ a.testBit i ∧ (gArr.getD j 0).testBit i then 1 else 0)
      else 0) % 2 = 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [corrN_succ, Finset.sum_range_succ]
    by_cases hb : b.testBit m
    · rw [ite_eq_left hb, ite_eq_left hb, ih, cAt, cAtN_eq_decide, xor_decide_mod]
    · rw [ite_eq_right hb, ite_eq_right hb, ih, add_zero]

theorem corr_sum (a b : ℕ) :
    (∑ j ∈ Finset.range 22, if b.testBit j then
      ∑ i ∈ Finset.range 22, (if j < i ∧ a.testBit i ∧ (gArr.getD j 0).testBit i then 1 else 0)
      else 0) =
    ∑ i ∈ Finset.range 22, ∑ j ∈ Finset.range 22,
      if j < i then nbit a i * nbit b j * gBit i j else 0 := by
  have hl : (∑ j ∈ Finset.range 22, if b.testBit j then
      ∑ i ∈ Finset.range 22, (if j < i ∧ a.testBit i ∧ (gArr.getD j 0).testBit i then 1 else 0)
      else 0) = ∑ j ∈ Finset.range 22, ∑ i ∈ Finset.range 22,
        (if b.testBit j ∧ j < i ∧ a.testBit i ∧ (gArr.getD j 0).testBit i then 1 else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hb : b.testBit j
    · simp [hb]
    · simp [hb]
  rw [hl, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hsym : (gArr.getD j 0).testBit i = (Bin.gramRows.getD i 0).testBit j := by
    rw [gArr_getD, gram_bits_symm j (Finset.mem_range.1 hj) i (Finset.mem_range.1 hi)]
  rw [hsym]
  unfold nbit gBit
  by_cases h1 : j < i <;> by_cases h2 : a.testBit i <;> by_cases h3 : b.testBit j <;>
    by_cases h4 : (Bin.gramRows.getD i 0).testBit j <;> simp [h1, h2, h3]

theorem qmul_eq (n m : ℕ) : qmul gArr n m = prodCode n m := by
  set T := ∑ i ∈ Finset.range 22, ∑ j ∈ Finset.range 22,
    if j < i then nbit n i * nbit m j * gBit i j else 0 with hT
  have hc : corr gArr n m = decide (T % 2 = 1) := by rw [corr, corrN_eq_decide, corr_sum]
  have hs : ((n.testBit 22 ^^ m.testBit 22) ^^ corr gArr n m) =
      decide ((nbit n 22 + nbit m 22 + T) % 2 = 1) := by
    rw [hc, bool_eq_decide (n.testBit 22), bool_eq_decide (m.testBit 22), xor_decide_mod,
      xor_decide_mod]
    rfl
  have hlt : (n ^^^ m) % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (by norm_num)
  rw [qmul, hs, prodCode, ← hT]
  by_cases h : (nbit n 22 + nbit m 22 + T) % 2 = 1
  · rw [decide_eq_true h, ite_eq_left rfl, h, mul_one, Nat.or_two_pow_eq_add_of_lt hlt]
  · have h0 : (nbit n 22 + nbit m 22 + T) % 2 = 0 := by omega
    rw [decide_eq_false h, h0, mul_zero, add_zero]
    simp

theorem qS_mul_prodCode
    (n m : ℕ) : qS n * qS m = qS (prodCode n m) := by
  rw [qS_mul, qmul_eq]

local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem beta_xs :
    (βr xs) = Xm Qn :=
  betaRow_xbar Dyadic.betaS gSeq betaS_explicit.gen gSeq_zero_mem gSeq_mem_Jbar

theorem beta_es
    (i : ℕ) : (βr (es i)) = Em Qn i := betaRow_eS Dyadic.betaS gSeq betaS_explicit.gen i

theorem beta_g0 :
    (βr (gs 0)) = G1m Qn Tmat cMat dMat := by
  have h : gs 0 = etaS gSeq iotaS cB := by
    rw [gs, if_pos rfl]
  rw [h]
  exact betaRow_eta_cB Dyadic.betaS gSeq betaS_explicit.gen gSeq_zero_mem gSeq_mem_Jbar iotaS
    iotaS_beta

theorem beta_g1 :
    (βr (gs 1)) = G2m Qn Tmat cMat dMat := by
  have h : gs 1 = etaS gSeq iotaS dB := by
    rw [gs, if_neg one_ne_zero, if_pos rfl]
  rw [h]
  exact betaRow_eta_dB Dyadic.betaS gSeq betaS_explicit.gen gSeq_zero_mem gSeq_mem_Jbar iotaS
    iotaS_beta

theorem qn_isUnit :
    ∀ j < 26, IsUnit (Qn j) :=
  Qn_isUnit _ _ betaS_explicit.gen

theorem beta_xsK :
    (βr xs) = Dyadic.XK := by
  rw [beta_xs, Xm_eq qn_isUnit]

theorem beta_esK
    {i : ℕ} (hi : i < 22) : (βr (es i)) = Dyadic.EK i := by
  rw [beta_es, Em_eq qn_isUnit hi]

theorem beta_g0K :
    (βr (gs 0)) = Dyadic.G1K := by
  rw [beta_g0, G1m_eq qn_isUnit]

theorem beta_g1K :
    (βr (gs 1)) = Dyadic.G2K := by
  rw [beta_g1, G2m_eq qn_isUnit]

theorem beta_g1iK :
    (βr ((gs 1)⁻¹)) = Dyadic.Gi2K := by
  rw [map_inv, Matrix.coe_units_inv, beta_g1K, G2K_inv]

theorem gs0_mem_Jbar :
    (gs 0).unop ∈ Jbar :=
  eta_cB_mem_Jbar Dyadic.betaS betaS_explicit.injective gSeq betaS_explicit.gen gSeq_zero_mem
    gSeq_mem_Jbar iotaS iotaS_beta

theorem gs1_mem_Jbar :
    (gs 1).unop ∈ Jbar :=
  eta_dB_mem_Jbar Dyadic.betaS betaS_explicit.injective gSeq betaS_explicit.gen gSeq_zero_mem
    gSeq_mem_Jbar iotaS iotaS_beta

theorem beta_qS
    (m : ℕ) : (βr (qS m)) = (if m.testBit 22 then (βr xs) else 1) *
    ((List.range 22).map fun j => if m.testBit j then (βr (es j)) else 1).prod := by
  have key := map_list_prod ((Units.coeHom MatB).comp (betaRow Dyadic.betaS))
    ((List.range 22).map fun i => if m.testBit i then es i else 1)
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, List.map_map] at key
  have h1 : (βr (xpow xs (m.testBit 22))) = if m.testBit 22 then (βr xs) else 1 := by
    cases m.testBit 22
    · simp [xpow]
    · simp [xpow]
  have h2 : ((List.range 22).map ((⇑(Units.coeHom MatB) ∘ ⇑(betaRow Dyadic.betaS)) ∘
      fun i => if m.testBit i then es i else 1)).prod
      = ((List.range 22).map fun j => if m.testBit j then (βr (es j)) else 1).prod := by
    refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply]
    split_ifs
    · rfl
    · simp
  rw [qS, qOf, map_mul, Units.val_mul, ordProd, key, h1, h2]

theorem prodK_eq (l : List MatB) : Dyadic.prodK l = l.prod := by
  induction l with
  | nil => rfl
  | cons M l ih => rw [Dyadic.prodK, ih, List.prod_cons]

theorem beta_qSK
    (m : ℕ) : (βr (qS m)) = Dyadic.qK m := by
  have h : ((List.range 22).map fun j => if m.testBit j then (βr (es j)) else 1) =
      (List.range 22).map fun j => if m.testBit j then Dyadic.EK j else 1 :=
    List.map_congr_left fun j hj => by rw [beta_esK (List.mem_range.1 hj)]
  rw [beta_qS, h, beta_xsK, Dyadic.qK, prodK_eq]

theorem eq_of_row0
    {a b : Sbp} (hab : a = b ∨ a = xs * b)
    (hrow : CFSG.KC.BM.e0 ᵥ* (βr a) = CFSG.KC.BM.e0 ᵥ* (βr b)) : a = b := by
  rcases hab with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, -, -, -, -, -, -, -, hvx, -⟩ := max2K.1
    apply hvx
    have hinj := Matrix.vecMul_injective_iff_isUnit.2 (Units.isUnit (betaRow Dyadic.betaS b))
    apply hinj
    have e : (CFSG.KC.BM.e0 ᵥ* (βr xs)) ᵥ* (βr b) = CFSG.KC.BM.e0 ᵥ* (βr b) := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, ← h]
      exact hrow
    rwa [beta_xsK] at e

theorem psiS_signedImg {rows : Array ℕ} {rows' : List ℕ}
    (hrows : ∀ i < 22, rows[i]! = rows'.getD i 0) (signs : ℕ) (i : Fin 22) :
    psiS (qS (signedImg rows' signs i)) =
      ∑ j : Fin 22, Max2.decMat rows i j • Multiplicative.toAdd (psiBar (eE j)) := by
  rw [psiS_qS_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb : (signedImg rows' signs i).testBit j = (rows'.getD i 0).testBit j := by
    rw [signedImg, Nat.testBit_or]
    split_ifs
    · rw [Nat.testBit_two_pow]
      have : ¬ 22 = (j : ℕ) := by omega
      simp [this]
    · simp
  rw [hb, Max2.decMat, Matrix.of_apply, hrows i i.2, Code.bvec_apply]

theorem quotRows1_lt : ∀ i < 22, quotRows1.getD i 0 < 2 ^ 22 := by decide

theorem quotRows2_lt : ∀ i < 22, quotRows2.getD i 0 < 2 ^ 22 := by decide

theorem conj_mem_Qs {g s : Sbp} (hg : g.unop ∈ Jbar) (hs : s ∈ Qs) : g⁻¹ * s * g ∈ Qs := by
  have h := conj_mem_Ebar (Jbar.inv_mem hg) hs
  show (g⁻¹ * s * g).unop ∈ Ebar
  rw [unop_mul, unop_mul, unop_inv, ← mul_assoc]
  rwa [inv_inv] at h

theorem conj_g0
    {i : ℕ} (hi : i < 22) :
    (gs 0)⁻¹ * es i * gs 0 = qS (signedImg quotRows1 3711077 i) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hR1, -⟩ :=
    pinned_B_max2_native_centralizer_and_quotient_action betaS_explicit iotaS iotaS_beta
  obtain ⟨hmem, hpsi⟩ := hR1 ⟨i, hi⟩
  have hq : psiS ((gs 0)⁻¹ * es i * gs 0) = psiS (qS (signedImg quotRows1 3711077 i)) := by
    rw [show (gs 0)⁻¹ * es i * gs 0 = (etaS gSeq iotaS cB)⁻¹ * eS gSeq i * etaS gSeq iotaS cB
      from rfl, psiS_of_mem hmem, hpsi, toAdd_ofAdd,
      psiS_signedImg r1Rows_eq 3711077 ⟨i, hi⟩]
  have hinv : (gs 0)⁻¹ = gs 0 := etaS_cB_inv gSeq iotaS
  refine eq_of_row0 (eq_of_psiS_eq hmem (qS_mem _) hq) ?_
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hinv, beta_g0K, beta_esK hi, beta_qSK]
  exact Certificates.certificate3098.1 i hi

theorem conj_g1
    {i : ℕ} (hi : i < 22) :
    (gs 1)⁻¹ * es i * gs 1 = qS (signedImg quotRows2 3015616 i) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hR2, -⟩ :=
    pinned_B_max2_native_centralizer_and_quotient_action betaS_explicit iotaS iotaS_beta
  obtain ⟨hmem, hpsi⟩ := hR2 ⟨i, hi⟩
  have hq : psiS ((gs 1)⁻¹ * es i * gs 1) = psiS (qS (signedImg quotRows2 3015616 i)) := by
    rw [show (gs 1)⁻¹ * es i * gs 1 = (etaS gSeq iotaS dB)⁻¹ * eS gSeq i * etaS gSeq iotaS dB
      from rfl, psiS_of_mem hmem, hpsi, toAdd_ofAdd,
      psiS_signedImg r2Rows_eq 3015616 ⟨i, hi⟩]
  refine eq_of_row0 (eq_of_psiS_eq hmem (qS_mem _) hq) ?_
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, beta_g1iK, beta_g1K, beta_esK hi, beta_qSK]
  exact Certificates.certificate3098.2.1 i hi

@[expose] noncomputable def conjS (g : Sbp) : Sbp →* Sbp := (MulAut.conj g⁻¹).toMonoidHom

theorem conjS_apply (g y : Sbp) : conjS g y = g⁻¹ * y * g := by
  rw [conjS, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem conj_xs
    {g : Sbp} (hg : g.unop ∈ Jbar) : g⁻¹ * xs * g = xs := by
  have h := (mem_Jbar_iff_comm.1 hg)
  have h' : xs * g = g * xs := by
    apply unop_injective
    rw [unop_mul, unop_mul, xs, unop_op, h]
  rw [mul_assoc, h', ← mul_assoc, inv_mul_cancel, one_mul]

theorem conj_qS
    {g : Sbp} (hg : g.unop ∈ Jbar) {A : Array ℕ}
    (hA : ∀ i < 22, g⁻¹ * es i * g = qS (A.getD i 0)) (n : ℕ) :
    g⁻¹ * qS n * g = qS (autApply gArr A n) := by
  have h := map_qOf extraRel (conjS g) (by rw [conjS_apply, conj_xs hg]) A
    (fun i hi => by rw [conjS_apply, hA i hi]; rfl) n
  rw [conjS_apply] at h
  exact h

theorem genImgs_getD {l i : ℕ} (hi : i < 22) : (genImgs l).getD i 0 =
    signedImg (if l = 0 then quotRows1 else quotRows2) (if l = 0 then 3711077 else 3015616) i := by
  rw [genImgs, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem genImgs_size (l : ℕ) : (genImgs l).size = 22 := by simp [genImgs]

theorem gs_mem_Jbar
    {l : ℕ} (hl : l < 2) : (gs l).unop ∈ Jbar := by
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · exact gs0_mem_Jbar
  · exact gs1_mem_Jbar

theorem conj_gs
    {l : ℕ} (hl : l < 2) {i : ℕ} (hi : i < 22) :
    (gs l)⁻¹ * es i * gs l = qS ((genImgs l).getD i 0) := by
  rw [genImgs_getD hi]
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · exact conj_g0 hi
  · exact conj_g1 hi

theorem autComp_getD {A B : Array ℕ} {i : ℕ} (hi : i < A.size) :
    (autComp gArr A B).getD i 0 = autApply gArr B (A.getD i 0) := by
  rw [autComp, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
    Option.getD_some]

theorem autComp_size (A B : Array ℕ) : (autComp gArr A B).size = A.size := by
  rw [autComp, Array.size_map]

theorem conj_liftWord :

    ∀ (w : List ℕ) (P : Sbp) (A : Array ℕ), P.unop ∈ Jbar → A.size = 22 →
    (∀ i < 22, P⁻¹ * es i * P = qS (A.getD i 0)) → (∀ l ∈ w, l < 2) →
    (∀ i < 22, (P * liftWordS w)⁻¹ * es i * (P * liftWordS w) =
      qS ((w.foldl (fun A l => autComp gArr A (genImgs l)) A).getD i 0)) ∧
    (w.foldl (fun A l => autComp gArr A (genImgs l)) A).size = 22 ∧
    (P * liftWordS w).unop ∈ Jbar
  | [], P, A, hP, hA, hPA, _ => by
    simp only [liftWordS, List.map_nil, List.prod_nil, mul_one, List.foldl_nil]
    exact ⟨hPA, hA, hP⟩
  | l :: w, P, A, hP, hA, hPA, hw => by
    have hl := hw l (List.mem_cons_self ..)
    have hP' : (P * gs l).unop ∈ Jbar := by
      rw [unop_mul]; exact Jbar.mul_mem (gs_mem_Jbar hl) hP
    have hA' : (autComp gArr A (genImgs l)).size = 22 := by rw [autComp_size, hA]
    have hPA' : ∀ i < 22, (P * gs l)⁻¹ * es i * (P * gs l) =
        qS ((autComp gArr A (genImgs l)).getD i 0) := by
      intro i hi
      rw [autComp_getD (by rw [hA]; exact hi), ← conj_qS (gs_mem_Jbar hl)
        (fun j hj => conj_gs hl hj), ← hPA i hi]
      group
    have ih := conj_liftWord w (P * gs l) _ hP' hA' hPA'
      fun l' h => hw l' (List.mem_cons_of_mem _ h)
    have e : P * liftWordS (l :: w) = P * gs l * liftWordS w := by
      rw [liftWordS, List.map_cons, List.prod_cons, ← liftWordS, mul_assoc]
    rw [e, List.foldl_cons]
    exact ih

theorem id23_getD {i : ℕ} (hi : i < 22) : id23.getD i 0 = 2 ^ i := by
  rw [id23, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem conj_liftWordS
    {w : List ℕ} (hw : ∀ l ∈ w, l < 2) {i : ℕ} (hi : i < 22) :
    (liftWordS w)⁻¹ * es i * liftWordS w = qS ((autWord gArr genImgs w).getD i 0) := by
  have h := (conj_liftWord w 1 id23 (by simp) (by simp [id23])
    (fun j hj => by rw [inv_one, one_mul, mul_one, id23_getD hj, qS_two_pow hj]) hw).1 i hi
  rwa [one_mul] at h

@[expose] def liftWordK (k : ℕ) : List ℕ :=
  if k = 6 then liftWord6 else if k = 8 then liftWord8 else liftWord10

theorem liftWord10_eq : liftWord10 = (List.replicate 10 seed10).flatten := by decide

theorem hs_eq_liftWordS
    {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) : hs k = liftWordS (liftWordK k) := by
  rcases hk with rfl | rfl | rfl
  · rw [hs, ite_eq_left rfl, liftWordK, ite_eq_left rfl,
      show liftWord6 = List.replicate 12 1 by decide, liftWordS, List.map_replicate,
      List.prod_replicate]
  · rw [hs, ite_eq_right (by decide), ite_eq_left rfl, liftWordK, ite_eq_right (by decide),
      ite_eq_left rfl, show liftWord8 = [0] by decide, liftWordS, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  · rw [hs, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, liftWordK,
      ite_eq_right (by decide), ite_eq_right (by decide), liftWord10_eq, liftWordS, liftWordS,
      List.map_flatten, List.prod_flatten, List.map_replicate, List.map_replicate,
      List.prod_replicate]

@[expose] def liftImgsK (k : ℕ) : List ℕ :=
  if k = 6 then liftImgs6 else if k = 8 then liftImgs8 else liftImgs10

@[expose] def liftRowsK (k : ℕ) : List ℕ :=
  if k = 6 then liftRows6 else if k = 8 then liftRows8 else liftRows10

theorem liftData_eq {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) :
    Dyadic.liftData k = (liftWordK k, liftImgsK k, liftRowsK k) := by
  rcases hk with rfl | rfl | rfl <;> rfl

theorem lift_autWord {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) :
    (autWord gArr genImgs (liftWordK k)).toList = liftImgsK k := by
  have h := (Certificates.certificate3098.2.2.1 k hk).1
  rwa [liftData_eq hk] at h

theorem lift_rows {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) :
    (liftImgsK k).map (· % 2 ^ 22) = liftRowsK k := by
  rcases hk with rfl | rfl | rfl <;> decide +kernel

theorem lift_len {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) : (liftRowsK k).length = 22 := by
  rcases hk with rfl | rfl | rfl <;> decide +kernel

theorem lift_lt {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) :
    ∀ i < 22, (liftRowsK k).toArray[i]! < 2 ^ 22 := by
  rcases hk with rfl | rfl | rfl <;> decide +kernel

theorem liftWordK_lt {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) : ∀ l ∈ liftWordK k, l < 2 := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem conj_hs
    {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) {i : ℕ} (hi : i < 22) :
    (hs k)⁻¹ * es i * hs k = qS ((liftImgsK k).getD i 0) := by
  have h1 := lift_autWord hk
  have h2 : (autWord gArr genImgs (liftWordK k)).getD i 0 = (liftImgsK k).getD i 0 := by
    rw [← h1, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [hs_eq_liftWordS hk, conj_liftWordS (liftWordK_lt hk) hi, h2]

theorem hs_mem_Jbar
    {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) : (hs k).unop ∈ Jbar := by
  rw [hs_eq_liftWordS hk]
  have h := (conj_liftWord (liftWordK k) 1 id23 (by simp) (by simp [id23])
    (fun j hj => by rw [inv_one, one_mul, mul_one, id23_getD hj, qS_two_pow hj])
    (liftWordK_lt hk)).2.2
  rwa [one_mul] at h

@[expose] def quotM (k : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) := Max2.decMat (liftRowsK k).toArray

theorem toArray_getElem! {l : List ℕ} {i : ℕ} : l.toArray[i]! = l.getD i 0 := by
  rw [getElem!_def, List.getD_eq_getElem?_getD, List.getElem?_toArray]
  cases l[i]? <;> rfl

theorem quotM_eq (k : ℕ) : quotM k = Dyadic.matRows (liftRowsK k) := by
  ext i j
  rw [quotM, Max2.decMat, Matrix.of_apply, Code.bvec_apply, toArray_getElem!, Dyadic.matRows,
    Matrix.of_apply]

theorem quotM_sq
    {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) : quotM k * quotM k = 1 := by
  have h := (Certificates.certificate3098.2.2.1 k hk).2.1
  rwa [liftData_eq hk, ← quotM_eq] at h

theorem rank_quotM
    {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) : (quotM k - 1).rank = k := by
  have h := (Certificates.certificate3098.2.2.1 k hk).2.2
  rwa [liftData_eq hk, ← quotM_eq] at h

theorem psiS_conj_hs
    {k : ℕ} (hk : k = 6 ∨ k = 8 ∨ k = 10) (i : Fin 22) :
    psiS ((hs k)⁻¹ * es i * hs k) = ∑ j : Fin 22, quotM k i j • psiS (es j) := by
  have hrows := lift_rows hk
  rw [conj_hs hk i.2, psiS_qS_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [psiS_es, quotM, Max2.decMat, Matrix.of_apply, Code.bvec_apply, toArray_getElem!, ← hrows]
  have hb : (((liftImgsK k).map (· % 2 ^ 22)).getD i 0).testBit j =
      ((liftImgsK k).getD i 0).testBit j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases (liftImgsK k)[(i : ℕ)]? with
    | none => rfl
    | some a =>
      rw [Option.map_some, Option.getD_some, Option.getD_some, Nat.testBit_mod_two_pow,
        decide_eq_true j.2, Bool.true_and]
  rw [hb]

theorem hs6_sq :
    hs 6 ^ 2 = xs := by
  have e : hs 6 = gs 1 ^ 12 := by rw [hs, ite_eq_left rfl]
  rw [e, ← pow_mul, show gs 1 = etaS gSeq iotaS dB from rfl, ← map_pow, show 12 * 2 = 24 from rfl,
    etaS_apply, show iotaS (dB ^ 24) = zS iotaS from rfl,
    z_conj_u betaS_explicit iotaS iotaS_beta]
  rfl

theorem hs8_sq :
    hs 8 ^ 2 = 1 := by
  have e : hs 8 = gs 0 := by rw [hs, ite_eq_right (by decide), ite_eq_left rfl]
  rw [e, show gs 0 = etaS gSeq iotaS cB from rfl, ← map_pow, sq, cB_mul_self, map_one]

theorem beta_seed :
    (βr (liftWordS seed10)) = Dyadic.seedK := by
  have key := map_list_prod ((Units.coeHom MatB).comp (betaRow Dyadic.betaS)) (seed10.map gs)
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, List.map_map] at key
  rw [liftWordS, key, Dyadic.seedK, prodK_eq]
  refine congrArg List.prod (List.map_congr_left fun l hl => ?_)
  have hl' : l = 0 ∨ l = 1 := by
    simp only [seed10, List.mem_cons, List.mem_nil_iff, or_false] at hl
    omega
  rcases hl' with rfl | rfl
  · simp only [Function.comp_apply, Units.coeHom_apply, beta_g0K]
    rfl
  · simp only [Function.comp_apply, Units.coeHom_apply, beta_g1K]
    rfl

theorem beta_hs
    (k : ℕ) : (βr (hs k)) = Dyadic.hK k := by
  rw [hs, Dyadic.hK]
  split_ifs
  · rw [map_pow, Units.val_pow_eq_pow_val, beta_g1K]
  · exact beta_g0K
  · rw [map_pow, Units.val_pow_eq_pow_val, beta_seed]
  · rw [map_one, Units.val_one]

theorem beta_rs
    (i : ℕ) : (βr (rs i)) = Dyadic.repK i := by
  rw [rs, map_mul, Units.val_mul, beta_hs, beta_qSK, Dyadic.repK]

theorem hs10_eq :
    hs 10 = liftWordS seed10 ^ 10 := by
  rw [hs, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem lift10_107 : qmul gArr (autApply gArr (liftImgsK 10).toArray 107) 107 = 2 ^ 22 := by
  decide +kernel

theorem hs10_sq :
    hs 10 ^ 2 = xs := by
  have h10 : (10 : ℕ) = 6 ∨ (10 : ℕ) = 8 ∨ (10 : ℕ) = 10 := Or.inr (Or.inr rfl)
  have hr : rs 12 * rs 12 = 1 := by
    apply betaRow_inj betaS_explicit.injective
    rw [map_mul, map_one, Units.val_mul, Units.val_one, beta_rs]
    exact Certificates.certificate3098.2.2.2
  have hr12 : rs 12 = hs 10 * qS 107 := rfl
  have hc : (hs 10)⁻¹ * qS 107 * hs 10 = qS (autApply gArr (liftImgsK 10).toArray 107) :=
    conj_qS (hs_mem_Jbar h10) (fun i hi => by
      rw [conj_hs h10 hi, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getD_eq_getElem?_getD]) 107
  have hx : qS (autApply gArr (liftImgsK 10).toArray 107) * qS 107 = xs := by
    rw [qS_mul, lift10_107, qS_two_pow_22]
  have e : hs 10 ^ 2 * xs = 1 := by
    rw [← hx, ← hc, ← hr, hr12]
    group
  have hxi : xs⁻¹ = xs := inv_eq_of_mul_eq_one_right xs_mul_self
  rw [← hxi]
  exact eq_inv_of_mul_eq_one_left e

theorem native_extraspecial_action_and_three_lift_squares :
    Set.BijOn qS (Set.Iio (2 ^ 23)) (Qs : Set Sbp) ∧
    (∀ n m, qS n * qS m = qS (prodCode n m)) ∧
    genSigns = [3711077, 3015616] ∧
    (∀ i < 22, (gs 0)⁻¹ * es i * gs 0 = qS (signedImg quotRows1 3711077 i)) ∧
    (∀ i < 22, (gs 1)⁻¹ * es i * gs 1 = qS (signedImg quotRows2 3015616 i)) ∧
    (∀ k, (k = 6 ∨ k = 8 ∨ k = 10) →
      (∀ i < 22, (hs k)⁻¹ * es i * hs k = qS ((liftImgsK k).getD i 0)) ∧
      (∀ i : Fin 22, psiS ((hs k)⁻¹ * es i * hs k) = ∑ j : Fin 22, quotM k i j • psiS (es j)) ∧
      quotM k * quotM k = 1 ∧ (quotM k - 1).rank = k) ∧
    hs 6 ^ 2 = xs ∧ hs 8 ^ 2 = 1 ∧ hs 10 ^ 2 = xs :=
  ⟨⟨fun n _ => qS_mem n, qS_injOn, fun _ hg => exists_qS hg⟩, qS_mul_prodCode, rfl,
    fun _ hi => conj_g0 hi, fun _ hi => conj_g1 hi,
    fun _ hk => ⟨fun _ hi => conj_hs hk hi, psiS_conj_hs hk, quotM_sq hk, rank_quotM hk⟩,
    hs6_sq, hs8_sq, hs10_sq⟩

end CFSG.Monster.B.CTIB
