module

public import CFSG.Quasithin.H13.L32ARuU1Inputs
public meta import CFSG.Quasithin.H13.L32ARuU1Inputs
import Certificates.Kernel.SporSch.Ru.C7152
import Certificates.Kernel.SporSch.Ru.C2248P
import Certificates.Kernel.SporSch.Ru.C2253P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.KC.BfsPin CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Quasithin.H13.KGRu CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuB1K
  CertificateChecks.KernelSporSch.RuLines CertificateChecks.KernelSporSch.Rows2
  CertificateChecks.KernelSporSch.RuCt CertificateChecks.KernelSporSch.RuU1

namespace CertificateChecks.KernelSporSch.RuU1

theorem lgN_eq : ∀ (l : List Nat) (i : Nat), lgN l i = l.getD i 0
  | [], _ => List.getD_nil.symm
  | _ :: _, 0 => List.getD_cons_zero.symm
  | _ :: l, i + 1 => (lgN_eq l i).trans List.getD_cons_succ.symm

theorem lgL_eq : ∀ (l : List (List Nat)) (i : Nat), lgL l i = l.getD i []
  | [], _ => List.getD_nil.symm
  | _ :: _, 0 => List.getD_cons_zero.symm
  | _ :: l, i + 1 => (lgL_eq l i).trans List.getD_cons_succ.symm

theorem or_bIf (a b : Bool) : (a || b) = bIf(a, true, b) := by cases a <;> rfl

theorem bw_eq {k : Nat} (hk : k < 4) : ruU1BasisA k = unpack 4060 12 (BW k) := by
  have h := (wordEqK_sound (binds2 c0_eq c1_eq) (perms2 pC0 pC1)
    ((bAnd_iff _ _).1 (allN_spec ch7152wB k hk)).1).1
  rw [← invs2, dword_zero] at h
  exact h

theorem cBW {k : Nat} (hk : k < 4) : canonK 4060 12 (mask 12) (4060 * 12) (BW k) = true :=
  ((bAnd_iff _ _).1 (allN_spec ch7152wB k hk)).2

theorem oa_eq {k : Nat} (hk : k < 6) : ruCW (ruOddA k) = unpack 4060 12 (OA k) := by
  have h := (wordEqK_sound (binds2 c0_eq c1_eq) (perms2 pC0 pC1)
    ((bAnd_iff _ _).1 (allN_spec ch7152wA k hk)).1).1
  rw [← invs2] at h
  exact h

theorem ob_eq {k : Nat} (hk : k < 6) : ruCW (ruOddB k) = unpack 4060 12 (OB k) := by
  have h := (wordEqK_sound (binds2 c0_eq c1_eq) (perms2 pC0 pC1)
    ((bAnd_iff _ _).1 (allN_spec ch7152wO k hk)).1).1
  rw [← invs2] at h
  exact h

theorem cpwZ (m : Nat) : canonK 4060 12 (mask 12) (4060 * 12) (pw Z (m % 2)) = true :=
  ((bAnd_iff _ _).1 (allN_spec ch7152pw (m % 2) (Nat.mod_lt _ (by norm_num)))).1

theorem cpwB {k : Nat} (hk : k < 4) (m : Nat) :
    canonK 4060 12 (mask 12) (4060 * 12) (pw (BW k) (m % 2)) = true :=
  allN_spec ((bAnd_iff _ _).1 (allN_spec ch7152pw (m % 2) (Nat.mod_lt _ (by norm_num)))).2 k hk

theorem pwE {X : Nat} (hX : canonK 4060 12 (mask 12) (4060 * 12) X = true) (e : Nat) :
    powA 4060 (unpack 4060 12 X) e = unpack 4060 12 (pw X e) := pow_eq hX

theorem prod_eq (i : Nat) : ruU1Prod i = unpack 4060 12 (xK i) := by
  rw [ruU1Prod, z_eq, bw_eq (k := 0) (by norm_num), bw_eq (k := 1) (by norm_num),
    bw_eq (k := 2) (by norm_num), bw_eq (k := 3) (by norm_num), pwE RuF.zCanon,
    pwE (cBW (k := 0) (by norm_num)), pwE (cBW (k := 1) (by norm_num)),
    pwE (cBW (k := 2) (by norm_num)), pwE (cBW (k := 3) (by norm_num))]
  have c2 := cpwB (k := 2) (by norm_num) (i / 8)
  have c3 := cpwB (k := 3) (by norm_num) (i / 16)
  have c1 := cpwB (k := 1) (by norm_num) (i / 4)
  have c0 := cpwB (k := 0) (by norm_num) (i / 2)
  rw [compA_unpack c2 c3, compA_unpack c1 (canonK_pcomp c2 c3),
    compA_unpack c0 (canonK_pcomp c1 (canonK_pcomp c2 c3)),
    compA_unpack (cpwZ i) (canonK_pcomp c0 (canonK_pcomp c1 (canonK_pcomp c2 c3)))]
  rfl

theorem cUA {i : Nat} (hi : i < 32) : canonK 4060 12 (mask 12) (4060 * 12) (UA i) = true :=
  ((bAnd_iff _ _).1 (allN_spec ch7152x i hi)).2

theorem ua_eq {i : Nat} (hi : i < 32) : ruU1Arr[i]! = unpack 4060 12 (UA i) := by
  rw [ruU1Arr, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, prod_eq,
    Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec ch7152x i hi)).1]

theorem uf_eq {i : Nat} (hi : i < 32) : ruU1FArr[i]! = unpack 1920 11 (UF i) := by
  have e : ∀ h : i < 32, ruU1Arr[(⟨i, h⟩ : Fin 32)]! = ruU1Arr[i]! := fun _ => rfl
  rw [ruU1FArr, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, RuF.f_eq, RuF.fpos_eq, e,
    ua_eq hi]
  exact resK_sound RuCe.fLt' (cUA hi) ((bAnd_iff _ _).1 (allN_spec ch7152f i hi)).1

theorem cmz_eq {G X : Nat} (hG : canonK 1920 11 (mask 11) (1920 * 11) G = true)
    (hX : canonK 1920 11 (mask 11) (1920 * 11) X = true) :
    ruCommZ1920 (unpack 1920 11 G) (unpack 1920 11 X) = cmz G X := by
  rw [ruCommZ1920, RuF.zf_eq, compA_unpack hG hX, compA_unpack hX hG,
    compA_unpack RuP.cZF (canonK_pcomp hX hG),
    eqA1920 (canonK_pcomp hG hX) (canonK_pcomp hX hG),
    eqA1920 (canonK_pcomp hG hX) (canonK_pcomp RuP.cZF (canonK_pcomp hX hG))]
  unfold cmz
  rw [sb_eq, sb_eq]
  exact or_bIf _ _

theorem beq_false_of_pg {P Q x : Nat} (h : Nat.beq (pg 11 (mask 11) P x) (pg 11 (mask 11) Q x) = false) :
    Nat.beq P Q = false := RuCt.beq_false_of_ne fun e => by
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h.symm

theorem scr1_spec {T0 T X x : Nat} (hX : canonK 1920 11 (mask 11) (1920 * 11) X = true)
    (hx : x < 1920) (h : scr1 T0 T X x = true) :
    cmz (pcomp 1920 11 (mask 11) T0 T) X = false := by
  unfold scr1 at h
  rw [sb_eq, sb_eq] at h
  have hXx : pg 11 (mask 11) X x < 1920 := lt_of_blt (allN_spec (range_of_canonK hX) x hx)
  have h32 : (1920 : Nat) < 2 ^ 32 := by norm_num
  have e1 : pg 11 (mask 11) (pcomp 1920 11 (mask 11) (pcomp 1920 11 (mask 11) T0 T) X) x =
      pg 11 (mask 11) T0 (pg 11 (mask 11) T (pg 11 (mask 11) X x)) := by
    rw [CFSG.KS.PF.pg_pcomp h32 hx, CFSG.KS.PF.pg_pcomp h32 hXx]
  have e2 : pg 11 (mask 11) (pcomp 1920 11 (mask 11) X (pcomp 1920 11 (mask 11) T0 T)) x =
      pg 11 (mask 11) X (pg 11 (mask 11) T0 (pg 11 (mask 11) T x)) := by
    rw [CFSG.KS.PF.pg_pcomp h32 hx, CFSG.KS.PF.pg_pcomp h32 hx]
  have e3 : pg 11 (mask 11) (pcomp 1920 11 (mask 11) RuF.ZF
      (pcomp 1920 11 (mask 11) X (pcomp 1920 11 (mask 11) T0 T))) x =
      pg 11 (mask 11) RuF.ZF (pg 11 (mask 11) X (pg 11 (mask 11) T0 (pg 11 (mask 11) T x))) := by
    rw [CFSG.KS.PF.pg_pcomp h32 hx, e2]
  unfold cmz
  rw [sb_eq, sb_eq]
  cases hab : Nat.beq (pg 11 (mask 11) T0 (pg 11 (mask 11) T (pg 11 (mask 11) X x)))
      (pg 11 (mask 11) X (pg 11 (mask 11) T0 (pg 11 (mask 11) T x)))
  · rw [hab] at h
    cases hab2 : Nat.beq (pg 11 (mask 11) T0 (pg 11 (mask 11) T (pg 11 (mask 11) X x)))
        (pg 11 (mask 11) RuF.ZF (pg 11 (mask 11) X (pg 11 (mask 11) T0 (pg 11 (mask 11) T x))))
    · have n1 := beq_false_of_pg (P := qc (pcomp 1920 11 (mask 11) T0 T) X)
        (Q := qc X (pcomp 1920 11 (mask 11) T0 T)) (x := x) (by
          simp only [qc]
          rw [e1, e2]
          exact hab)
      have n2 := beq_false_of_pg (P := qc (pcomp 1920 11 (mask 11) T0 T) X)
        (Q := qc RuF.ZF (qc X (pcomp 1920 11 (mask 11) T0 T))) (x := x) (by
          simp only [qc]
          rw [e1, e3]
          exact hab2)
      rw [n1, n2]
    · rw [hab2] at h
      exact absurd h Bool.false_ne_true
  · rw [hab] at h
    exact absurd h Bool.false_ne_true

theorem scr_spec {T0 T : Nat} (h : scr T0 T = true) :
    u1pK (pcomp 1920 11 (mask 11) T0 T) = true := by
  obtain ⟨j, hj, h1⟩ := anyK_spec h
  obtain ⟨x, hx, h2⟩ := anyK_spec h1
  have hc : cmz (pcomp 1920 11 (mask 11) T0 T) (RuT1920.L (Nat.add 24 j)) = false :=
    scr1_spec (cLj (j := 24 + j) (by omega)) (by omega) h2
  have hA : allN 6 (fun j => cmz (pcomp 1920 11 (mask 11) T0 T) (RuT1920.L (Nat.add 24 j))) =
      false := by
    cases e : allN 6 (fun j => cmz (pcomp 1920 11 (mask 11) T0 T) (RuT1920.L (Nat.add 24 j)))
    · rfl
    · have h3 := allN_spec e j hj
      rw [hc] at h3
      exact absurd h3 Bool.false_ne_true
  unfold u1pK
  rw [hA]

theorem inner_imp {T0 n : Nat} {T : Nat → Nat}
    (h : allN n (fun b => bIf(scr T0 (T b), true, u1pK (pcomp 1920 11 (mask 11) T0 (T b)))) = true) :
    allN n (fun b => u1pK (pcomp 1920 11 (mask 11) T0 (T b))) = true :=
  allN_of_forall fun b hb => by
    have h1 := allN_spec h b hb
    cases e : scr T0 (T b)
    · rw [e] at h1
      exact h1
    · exact scr_spec e

theorem row_imp {LR TR : Nat → Nat} {a : Nat} (h : u1RowG LR TR a = true) :
    row2K 1920 11 (mask 11) (1920 * 11) LR TR u1pK a = true := by
  unfold u1RowG at h
  unfold row2K
  simp only [sb_eq] at h ⊢
  exact inner_imp h

theorem rowsS : all2 1920 (rawLevels 1920 (ruField1920 1) (ruBaseArr 1920 ruSBase))
    (fun g => !(allLt 6 fun j => ruCommZ1920 g (ruJF j)) ||
      (Nat.any 32 fun i _ => eqA 1920 g ruU1FArr[i]!)) = true := by
  refine all2_of_rows_imp RuSF.bindsS RuSF.pS RuSS2.hl (Nat.le_refl 2) (fun G hG h => ?_)
    (fun a ha => row_imp (LR := RuSS2.LR) (TR := RuSS2.TR)
      (ch7152R.all a (lt_of_lt_of_eq ha (Nat.eq_of_beq_eq_true ch7152cnt))))
  have hA : (allLt 6 fun j => ruCommZ1920 (unpack 1920 11 G) (ruJF j)) =
      allN 6 (fun j => cmz G (RuT1920.L (Nat.add 24 j))) :=
    allLt_eq_allN fun j hj => by
      rw [jf_eq (by omega)]
      exact cmz_eq hG (cLj (by omega))
  unfold u1pK at h
  rw [hA]
  cases hc : allN 6 (fun j => cmz G (RuT1920.L (Nat.add 24 j)))
  · rfl
  · rw [hc] at h
    have h' : anyK 32 (fun i => Nat.beq G (UF i)) = true := h
    obtain ⟨i, hi, hb⟩ := anyK_spec h'
    rw [not_true_or]
    refine nat_any_of hi ?_
    rw [uf_eq hi, ← Nat.eq_of_beq_eq_true hb]
    exact eqK_sound (Nat.beq_refl G)

theorem mulF : ∀ i < 32, ∀ j < 32,
    eqA 4060 (compA 4060 ruU1Arr[i]! ruU1Arr[j]!) ruU1Arr[i ^^^ j]! = true := fun i hi j hj => by
  have h := (bAnd_iff _ _).1 (allN_spec (ch7152m.all i hi) j hj)
  have hx : i ^^^ j < 32 := lt_of_blt h.1
  rw [ua_eq hi, ua_eq hj, ua_eq hx, compA_unpack (cUA hi) (cUA hj),
    eqA_canon (canonK_pcomp (cUA hi) (cUA hj)) (cUA hx)]
  exact h.2

theorem neF : ∀ i < 32, 0 < i → eqA 4060 ruU1Arr[i]! (idA 4060) = false := fun i hi h0 => by
  have h := allN_spec ch7152ne i hi
  rw [RuCt.beq_false_of_ne (by omega : i ≠ 0)] at h
  have h' : (!Nat.beq (UA i) (pidn 4060 12)) = true := h
  rw [ua_eq hi, RuB1K.idA_eq, eqA_canon (cUA hi) RuB1K.cId]
  cases e : Nat.beq (UA i) (pidn 4060 12)
  · rfl
  · rw [e] at h'
    exact absurd h' Bool.false_ne_true

theorem sigF : ∀ k < 4, ∀ i < 32, eqA 4060 (ruConjA ruSGensA[k]! ruU1Arr[i]!)
    ruU1Arr[(ruU1Sig.getD k []).getD i 0]! = true := fun k hk i hi => by
  have h := (bAnd_iff _ _).1 (allN_spec (allN_spec ch7152t3 k hk) i hi)
  have hr : lgN (lgL ruU1Sig k) i < 32 := lt_of_blt h.1
  have hS : canonK 4060 12 (mask 12) (4060 * 12) (SG k) = true := allN_spec RuCe.cSG k hk
  have hSI : canonK 4060 12 (mask 12) (4060 * 12) (SGI k) = true := allN_spec ch7152cs k hk
  have hinv : invCand 4060 ruSGensA[k]! = unpack 4060 12 (SGI k) :=
    (inv_of (sg_eq hk) (allN_spec pSG k hk)).1
  rw [ruConjA, hinv, sg_eq hk, ua_eq hi, ← lgL_eq, ← lgN_eq, ua_eq hr,
    compA_unpack hS (cUA hi), compA_unpack (canonK_pcomp hS (cUA hi)) hSI,
    eqA_canon (canonK_pcomp (canonK_pcomp hS (cUA hi)) hSI) (cUA hr)]
  exact h.2

theorem tauF : ∀ m < 7, eqA 4060 ruEArr[m]! ruU1Arr[ruU1Tau.getD m 0]! = true := fun m hm => by
  have h := (bAnd_iff _ _).1 (allN_spec ch7152t4 m hm)
  have hr : lgN ruU1Tau m < 32 := lt_of_blt h.1
  rw [← lgN_eq, e_eq hm, ua_eq hr, eqA_canon (cEi hm) (cUA hr)]
  exact h.2

theorem piF : ∀ k < 2, ∀ m < 7, eqA 4060 (ruConjA ruNGensA[k]! ruEArr[m]!)
    ruEArr[(ruEPi.getD k []).getD m 0]! = true := fun k hk m hm => by
  have h := (bAnd_iff _ _).1 (allN_spec (allN_spec ch7152n k hk) m hm)
  have hr : lgN (lgL ruEPi k) m < 7 := lt_of_blt h.1
  rw [conj_eq hk hm, ← lgL_eq, ← lgN_eq, e_eq hr, eqA_canon (cConj hk hm) (cEi hr)]
  exact h.2

theorem commF : eqA 4060 (ruCommA 4060 ruSGensA[0]! ruEArr[2]!) ruZA = true := by
  have hS : canonK 4060 12 (mask 12) (4060 * 12) (SG 0) = true := allN_spec RuCe.cSG 0 (by norm_num)
  have hSI : canonK 4060 12 (mask 12) (4060 * 12) (SGI 0) = true :=
    allN_spec ch7152cs 0 (by norm_num)
  have hE := cEi (i := 2) (by norm_num)
  have hinv : invCand 4060 ruSGensA[0]! = unpack 4060 12 (SGI 0) :=
    (inv_of (sg_eq (i := 0) (by norm_num)) (allN_spec pSG 0 (by norm_num))).1
  have hEi : invCand 4060 (unpack 4060 12 (EA 2)) = unpack 4060 12 (EA 2) :=
    (invEqK_sound (allN_spec eInv 2 (by norm_num))).1
  rw [ruCommA, hinv, sg_eq (i := 0) (by norm_num), e_eq (i := 2) (by norm_num), hEi,
    compA_unpack hS hE, compA_unpack (canonK_pcomp hS hE) hSI,
    compA_unpack (canonK_pcomp (canonK_pcomp hS hE) hSI) hE, z_eq,
    eqA_canon (canonK_pcomp (canonK_pcomp (canonK_pcomp hS hE) hSI) hE) RuF.zCanon]
  exact ch7152c

theorem pow_id {P e : Nat} (hP : canonK 4060 12 (mask 12) (4060 * 12) P = true)
    (h : Nat.beq (pw P e) (pidn 4060 12) = true) :
    eqA 4060 (powA 4060 (unpack 4060 12 P) e) (idA 4060) = true := by
  have e1 : pw P e = pidn 4060 12 := Nat.eq_of_beq_eq_true h
  rw [pwE hP, e1, RuB1K.idA_eq]
  exact eqK_sound (Nat.beq_refl _)

theorem oddF : ∀ k < 6, ruOddM k % 2 = 1 ∧ ruOddMA k % 2 = 1 ∧ ruOddMB k % 2 = 1 ∧
    eqA 4060 (powA 4060 (compA 4060 (compA 4060 ruJGensA[k]! (ruCW (ruOddA k)))
      (ruCW (ruOddB k))) (ruOddM k)) (idA 4060) = true ∧
    eqA 4060 (powA 4060 (ruCW (ruOddA k)) (ruOddMA k)) (idA 4060) = true ∧
    eqA 4060 (powA 4060 (ruCW (ruOddB k)) (ruOddMB k)) (idA 4060) = true := fun k hk => by
  have h := (bAnd_iff _ _).1 (allN_spec ch7152o k hk)
  have h2 := (bAnd_iff _ _).1 h.2
  have hJ := (RuCe.jok_spec hk).2
  have hA := ((bAnd_iff _ _).1 (allN_spec ch7152wA k hk)).2
  have hB := ((bAnd_iff _ _).1 (allN_spec ch7152wO k hk)).2
  have hpar : ruOddM k % 2 = 1 ∧ ruOddMA k % 2 = 1 ∧ ruOddMB k % 2 = 1 := by
    interval_cases k <;> decide
  refine ⟨hpar.1, hpar.2.1, hpar.2.2, ?_, ?_, ?_⟩
  · rw [RuCe.jg_eq hk, oa_eq hk, ob_eq hk, compA_unpack hJ hA, compA_unpack (canonK_pcomp hJ hA) hB]
    exact pow_id (canonK_pcomp (canonK_pcomp hJ hA) hB) h.1
  · rw [oa_eq hk]
    exact pow_id hA h2.1
  · rw [ob_eq hk]
    exact pow_id hB h2.2

end CertificateChecks.KernelSporSch.RuU1

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Quasithin.H13.KGRu in
theorem certificate7152 :
    all2 1920 (rawLevels 1920 (ruField1920 1) (ruBaseArr 1920 ruSBase))
        (fun g => !(allLt 6 fun j => ruCommZ1920 g (ruJF j)) ||
          (Nat.any 32 fun i _ => eqA 1920 g ruU1FArr[i]!)) = true ∧
      (∀ i < 32, ∀ j < 32, eqA 4060 (compA 4060 ruU1Arr[i]! ruU1Arr[j]!) ruU1Arr[i ^^^ j]! = true) ∧
      (∀ i < 32, 0 < i → eqA 4060 ruU1Arr[i]! (idA 4060) = false) ∧
      (∀ k < 4, ∀ i < 32, eqA 4060 (ruConjA ruSGensA[k]! ruU1Arr[i]!)
        ruU1Arr[(ruU1Sig.getD k []).getD i 0]! = true) ∧
      (∀ m < 7, eqA 4060 ruEArr[m]! ruU1Arr[ruU1Tau.getD m 0]! = true) ∧
      (∀ a < 32, ∀ b < 32, ruU1PairOK a b = true) ∧
      (∀ k < 2, ∀ m < 7, eqA 4060 (ruConjA ruNGensA[k]! ruEArr[m]!)
        ruEArr[(ruEPi.getD k []).getD m 0]! = true) ∧
      eqA 4060 (ruCommA 4060 ruSGensA[0]! ruEArr[2]!) ruZA = true ∧
      (∀ k < 6, ruOddM k % 2 = 1 ∧ ruOddMA k % 2 = 1 ∧ ruOddMB k % 2 = 1 ∧
        eqA 4060 (powA 4060 (compA 4060 (compA 4060 ruJGensA[k]! (ruCW (ruOddA k)))
          (ruCW (ruOddB k))) (ruOddM k)) (idA 4060) = true ∧
        eqA 4060 (powA 4060 (ruCW (ruOddA k)) (ruOddMA k)) (idA 4060) = true ∧
        eqA 4060 (powA 4060 (ruCW (ruOddB k)) (ruOddMB k)) (idA 4060) = true) :=
  ⟨KernelSporSch.RuU1.rowsS, KernelSporSch.RuU1.mulF, KernelSporSch.RuU1.neF,
    KernelSporSch.RuU1.sigF, KernelSporSch.RuU1.tauF,
    fun a ha b hb => allN_spec (allN_spec KernelSporSch.RuU1.ch7152pair a ha) b hb,
    KernelSporSch.RuU1.piF, KernelSporSch.RuU1.commF, KernelSporSch.RuU1.oddF⟩

end Certificates

end
