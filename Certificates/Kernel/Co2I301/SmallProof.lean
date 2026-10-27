module

public import Certificates.Kernel.Co2I301.ChainK0
public import Certificates.Kernel.Co2I301.ChainL
public import Certificates.Kernel.Co2I301.SixBind
public import Certificates.Kernel.SporSch.Co2M.Words
public import Certificates.Kernel.Sporadic.Co2.ChainA
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Certificates.Kernel.LocalQTCovTPrim
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.KS.Co2I301
  CFSG.Sporadic.Co2I301 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.HardMathSupport.Dickson.I271.Co2Cent
  CFSG.Sporadic.Schreier.Co3.Native CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CertificateChecks.KernelSporSch.Co2M (PV V_get V_size good isInvA_rep aT aRep cmpP invP powP
  rep_cmp rep_inv rep_pow eqA_of_mat ne_of_mat zP zRep)

@[expose] noncomputable def mP (k : ℕ) : ℕ × ℕ := (M k, MI k)

@[expose] noncomputable def fwP (T : List (ℕ × ℕ)) (w : List ℕ) : ℕ × ℕ :=
  w.foldl (fun p l => cmpP p (T.getD l (0, 0))) (I22, I22)

@[expose] noncomputable def qP : List (ℕ × ℕ) :=
  (List.range 3).map fun i => fwP aT co2E81.qW[i]!

@[expose] noncomputable def dP : List (ℕ × ℕ) :=
  (List.range 4).map fun j => fwP qP (co2E81.dW[0]!)[j]!

@[expose] noncomputable def dProdP (k : ℕ) : ℕ × ℕ :=
  cmpP (powP (dP.getD 0 (0, 0)) (digit3 k 0)) (cmpP (powP (dP.getD 1 (0, 0)) (digit3 k 1))
    (cmpP (powP (dP.getD 2 (0, 0)) (digit3 k 2)) (powP (dP.getD 3 (0, 0)) (digit3 k 3))))

@[expose] noncomputable def xbP : ℕ × ℕ := dProdP 1

@[expose] noncomputable def mvK (A : ℕ) : ℕ :=
  ((List.range 2300).find? fun i => !Nat.beq (vmK (VG (PV 0) i) A) (VG (PV 0) i)).getD 2300

@[expose] noncomputable def movesK (A : ℕ) : Bool :=
  Nat.blt (mvK A) 2300 && !Nat.beq (vmK (VG (PV 0) (mvK A)) A) (VG (PV 0) (mvK A))

@[expose] noncomputable def bP (t : ℕ) : ℕ × ℕ :=
  cmpP (powP (mP 1) (t % 3)) (cmpP (powP (mP 3) (t / 3 % 3)) (powP (mP 4) (t / 9)))

@[expose] noncomputable def eP (t : ℕ) : ℕ × ℕ := cmpP (powP (mP 1) (t % 3)) (powP zP (t / 3))

@[expose] noncomputable def cmE (p q : ℕ × ℕ) : Bool := Nat.beq (cmpP p q).1 (cmpP q p).1

theorem mat_ok : (Nat.beq (mP 1).1 (cmpP (mP 0) (cmpP xbP (invP (mP 0)))).1 &&
    cmE zP (mP 1) && cmE zP (mP 2) && cmE zP (mP 3) && cmE zP (mP 4) && cmE zP (mP 5) &&
    cmE zP (mP 6) && cmE (mP 1) (mP 2) && cmE (mP 1) (mP 3) && cmE (mP 1) (mP 4) &&
    cmE (mP 1) (mP 5) && cmE (mP 1) (mP 6) && cmE (mP 3) (mP 4) &&
    Nat.beq (powP (mP 1) 3).1 I22 && Nat.beq (powP (mP 3) 3).1 I22 &&
    Nat.beq (powP (mP 4) 3).1 I22 && Nat.beq (cmpP (mP 2) (mP 2)).1 I22) = true := by
  quickRfl

theorem b27_ok : allN 27 (fun t => Nat.beq t 0 || movesK (bP t).1) = true := by quickRfl

theorem pow_ok : allN 6 (fun t => Nat.beq (t % 3) 0 || movesK (powP (eP t) 512).1) = true := by
  quickRfl

@[expose] noncomputable def HI : ℕ := pinvS 2300 12 (mask 12) (HX.F 0)

@[expose] noncomputable def pkH (t : ℕ) : ℕ := pcomp 2300 12 (mask 12) HI (pcomp 2300 12 (mask 12) t (HX.F 0))

@[expose] noncomputable def pkS (t : ℕ) : ℕ :=
  pcomp 2300 12 (mask 12) (HX.F 2) (pcomp 2300 12 (mask 12) t (HX.F 2))

theorem perm_ok : (CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 0) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 2) && CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 3) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 4) && CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 5) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 6) && CFSG.KC.Misc.ArrEnum.permB 2300 12 HI &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 5) (HX.F 0)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 6) (HX.F 0)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 2) (HX.F 0)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 5) (HX.F 2)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 6) (HX.F 2)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkH (HX.F 5)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkH (HX.F 6)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkH (HX.F 2)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkS (HX.F 5)) &&
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkS (HX.F 6))) = true := by
  quickRfl

@[expose] noncomputable def siftL (G : ℕ) : Bool :=
  siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) LC.LR LC.TRI LC.BP 3 0 G

@[expose] noncomputable def siftK0 (G : ℕ) : Bool :=
  siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) K0.LR K0.TRI K0.BP 4 0 G

theorem sift_ok : (siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12)
    CertificateChecks.KernelSpor.Co2A.LR CertificateChecks.KernelSpor.Co2A.TRI
    CertificateChecks.KernelSpor.Co2A.BP 6 0 (HX.F 0) &&
    siftL (pkH (HX.F 5)) && siftL (pkH (HX.F 6)) && siftL (pkH (HX.F 2)) &&
    siftK0 (HX.F 3) && siftK0 (HX.F 4) && siftK0 (pkS (HX.F 5)) && siftK0 (pkS (HX.F 6))) = true := by
  quickRfl

theorem o6_ok : (∀ j < 6, o6.getD j 0 < 2300) ∧ ∀ j < 6,
    (pg 12 (mask 12) (HX.F 5) (o6.getD j 0) == o6.getD (sigma1.getD j 0) 0 &&
      pg 12 (mask 12) (HX.F 6) (o6.getD j 0) == o6.getD (sigma2.getD j 0) 0) = true := by
  decide +kernel

theorem words_lt : (co2E81.qW.size = 3 ∧ (List.range 3).all fun i => co2E81.qW[i]!.all (· < 2)) ∧
    (co2E81.dW[0]!).size = 4 ∧ (List.range 4).all fun j => (co2E81.dW[0]!)[j]!.all (· < 3) := by
  decide +kernel

theorem rep_mP {k : ℕ} (hk : k < 10) :
    Rep 22 co2PackedVecs (i301Arr k) (mP k).1 (mP k).2 := rep_arr k hk

theorem rep_id : Rep 22 co2PackedVecs (idA 2300) (I22, I22).1 (I22, I22).2 := by
  have h := rep_idA good
  rw [V_size, ← I22_eq] at h
  exact h

theorem rep_posWord {gs : Array (Array ℕ)} {T : List (ℕ × ℕ)}
    (hg : ∀ l < T.length, Rep 22 co2PackedVecs gs[l]! (T.getD l (0, 0)).1 (T.getD l (0, 0)).2)
    (w : List ℕ) (hw : ∀ l ∈ w, l < T.length) :
    Rep 22 co2PackedVecs (posWord 2300 gs w) (fwP T w).1 (fwP T w).2 := by
  unfold posWord fwP
  have key : ∀ (w : List ℕ) (a : Array ℕ) (p : ℕ × ℕ), Rep 22 co2PackedVecs a p.1 p.2 →
      (∀ l ∈ w, l < T.length) →
      Rep 22 co2PackedVecs (w.foldl (fun acc l => compA 2300 acc gs[l]!) a)
        (w.foldl (fun p l => cmpP p (T.getD l (0, 0))) p).1
        (w.foldl (fun p l => cmpP p (T.getD l (0, 0))) p).2 := by
    intro w
    induction w with
    | nil => exact fun _ _ ha _ => ha
    | cons l w ih =>
      intro a p ha hw
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _ (rep_cmp ha (hg l (hw l List.mem_cons_self)))
        fun j hj => hw j (List.mem_cons_of_mem _ hj)
  exact key w _ _ rep_id hw

theorem rep_pg {l : ℕ} (hl : l < aT.length) :
    Rep 22 co2PackedVecs co2E81.pg[l]! (aT.getD l (0, 0)).1 (aT.getD l (0, 0)).2 := by
  have e : co2E81.pg =
      #[CFSG.Sporadic.Co2Schreier.aArrs[0]!, CFSG.Sporadic.Co2Schreier.aArrs[1]!] := rfl
  have hl2 : l < 2 := hl
  rw [e]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact repT_get aRep hl
  · exact repT_get aRep hl

theorem qP_length : qP.length = 3 := by simp [qP]

theorem rep_q {i : ℕ} (hi : i < qP.length) :
    Rep 22 co2PackedVecs (qGens2 ())[i]! (qP.getD i (0, 0)).1 (qP.getD i (0, 0)).2 := by
  obtain ⟨⟨hs, hq⟩, -⟩ := words_lt
  rw [qP_length] at hi
  have e1 : (qGens2 ())[i]! = posWord 2300 co2E81.pg co2E81.qW[i]! := by
    unfold qGens2 qGens
    rw [getElem!_pos _ i (by simp [hs]; omega), Array.getElem_map,
      getElem!_pos co2E81.qW i (by omega)]
    rfl
  have e2 : qP.getD i (0, 0) = fwP aT co2E81.qW[i]! := by
    simp [qP, List.getD_eq_getElem?_getD, hi]
  rw [e1, e2]
  have hw := List.all_eq_true.1 hq i (List.mem_range.2 hi)
  exact rep_posWord (fun l hl => rep_pg hl) _ fun l hl => by
    have := List.all_eq_true.1 hw l hl
    simp only [decide_eq_true_eq] at this
    change l < 2
    exact this

theorem rep_d {j : ℕ} (hj : j < 4) :
    Rep 22 co2PackedVecs (dGens ())[j]! (dP.getD j (0, 0)).1 (dP.getD j (0, 0)).2 := by
  obtain ⟨-, hs, hd⟩ := words_lt
  have e1 : (dGens ())[j]! = posWord 2300 (qGens2 ()) (co2E81.dW[0]!)[j]! := by
    unfold dGens
    rw [getElem!_pos _ j (by simp [hs]; omega), Array.getElem_map,
      getElem!_pos (co2E81.dW[0]!) j (by omega)]
  have e2 : dP.getD j (0, 0) = fwP qP (co2E81.dW[0]!)[j]! := by
    simp [dP, List.getD_eq_getElem?_getD, hj]
  rw [e1, e2]
  have hw := List.all_eq_true.1 hd j (List.mem_range.2 hj)
  exact rep_posWord (fun l hl => rep_q hl) _ fun l hl => by
    have := List.all_eq_true.1 hw l hl
    simp only [decide_eq_true_eq] at this
    rw [qP_length]
    exact this

theorem rep_xB : Rep 22 co2PackedVecs (dElts ())[1]! xbP.1 xbP.2 := by
  have e : (dElts ())[1]! = dProd (dGens ()) 1 := by
    unfold dElts
    rw [getElem!_pos _ 1 (by simp)]
    simp
  rw [e]
  unfold dProd
  have h0 := rep_d (j := 0) (by norm_num)
  have h1 := rep_d (j := 1) (by norm_num)
  have h2 := rep_d (j := 2) (by norm_num)
  have h3 := rep_d (j := 3) (by norm_num)
  exact rep_cmp (rep_pow h0 _) (rep_cmp (rep_pow h1 _) (rep_cmp (rep_pow h2 _) (rep_pow h3 _)))

theorem ne_of_moves {a : Array ℕ} {p : ℕ × ℕ} (ha : Rep 22 co2PackedVecs a p.1 p.2)
    (h : movesK p.1 = true) : eqA 2300 a (idA 2300) = false := by
  unfold movesK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  exact ne_of_mat ha h.1 h.2

theorem comm_of_mat {a b : Array ℕ} {p q : ℕ × ℕ} (ha : Rep 22 co2PackedVecs a p.1 p.2)
    (hb : Rep 22 co2PackedVecs b q.1 q.2) (h : cmE p q = true) : comm2300 a b = true :=
  eqA_of_mat (rep_cmp ha hb) (rep_cmp hb ha) (Nat.eq_of_beq_eq_true h)

theorem eqId_of_mat {a : Array ℕ} {p : ℕ × ℕ} (ha : Rep 22 co2PackedVecs a p.1 p.2)
    (h : Nat.beq p.1 I22 = true) : eqA 2300 a (idA 2300) = true :=
  eqA_of_mat (q := (I22, I22)) ha rep_id (Nat.eq_of_beq_eq_true h)

theorem szOK' : szOK 2300 12 = true := by decide +kernel

theorem perm_parts : CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 0) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 2) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 3) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 4) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 5) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (HX.F 6) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 HI = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 5) (HX.F 0)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 6) (HX.F 0)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 2) (HX.F 0)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 5) (HX.F 2)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) (HX.F 6) (HX.F 2)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkH (HX.F 5)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkH (HX.F 6)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkH (HX.F 2)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkS (HX.F 5)) = true ∧
    CFSG.KC.Misc.ArrEnum.permB 2300 12 (pkS (HX.F 6)) = true := by
  have h := perm_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hi⟩, a5⟩, a6⟩, a2⟩, b5⟩, b6⟩, c5⟩, c6⟩, c2⟩,
    d5⟩, d6⟩ := h
  exact ⟨h0, h2, h3, h4, h5, h6, hi, a5, a6, a2, b5, b6, c5, c6, c2, d5, d6⟩

theorem sift_parts : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12)
      CertificateChecks.KernelSpor.Co2A.LR CertificateChecks.KernelSpor.Co2A.TRI
      CertificateChecks.KernelSpor.Co2A.BP 6 0 (HX.F 0) = true ∧
    siftL (pkH (HX.F 5)) = true ∧ siftL (pkH (HX.F 6)) = true ∧ siftL (pkH (HX.F 2)) = true ∧
    siftK0 (HX.F 3) = true ∧ siftK0 (HX.F 4) = true ∧ siftK0 (pkS (HX.F 5)) = true ∧
    siftK0 (pkS (HX.F 6)) = true := by
  have h := sift_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, l5⟩, l6⟩, l2⟩, k3⟩, k4⟩, s5⟩, s6⟩ := h
  exact ⟨h0, l5, l6, l2, k3, k4, s5, s6⟩

theorem comp_u {p q : ℕ} (hp : CFSG.KC.Misc.ArrEnum.permB 2300 12 p = true)
    (hq : CFSG.KC.Misc.ArrEnum.permB 2300 12 q = true) :
    compA 2300 (unpack 2300 12 p) (unpack 2300 12 q) = unpack 2300 12 (pcomp 2300 12 (mask 12) p q) :=
  CFSG.KC.Misc.ArrEnum.comp_unpack' szOK' hp hq

theorem hi_eq : invCand 2300 (i301H ()) = unpack 2300 12 HI := by
  rw [show i301H () = i301Arr 0 from rfl, arr_eq 0 (by norm_num)]
  exact CFSG.KC.LQT.Cov.T.invCand_unpack perm_parts.1

theorem k1_eq : i301K1 () = unpack 2300 12 (HX.F 5) := by
  rw [i301K1_eq, arr_eq 5 (by norm_num)]

theorem k2_eq : i301K2 () = unpack 2300 12 (HX.F 6) := by
  rw [i301K2_eq, arr_eq 6 (by norm_num)]

theorem conjH_eq {t : ℕ} (ht : CFSG.KC.Misc.ArrEnum.permB 2300 12 t = true)
    (h1 : CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) t (HX.F 0)) = true) :
    conj2300 (invCand 2300 (i301H ())) (i301H ()) (unpack 2300 12 t) = unpack 2300 12 (pkH t) := by
  have e0 : i301H () = unpack 2300 12 (HX.F 0) := arr_eq 0 (by norm_num)
  unfold conj2300 pkH
  rw [hi_eq, e0, comp_u ht perm_parts.1, comp_u perm_parts.2.2.2.2.2.2.1 h1]

theorem conjS_eq {t : ℕ} (ht : CFSG.KC.Misc.ArrEnum.permB 2300 12 t = true)
    (h1 : CFSG.KC.Misc.ArrEnum.permB 2300 12 (pcomp 2300 12 (mask 12) t (HX.F 2)) = true) :
    conj2300 (i301S ()) (i301S ()) (unpack 2300 12 t) = unpack 2300 12 (pkS t) := by
  have e2 : i301S () = unpack 2300 12 (HX.F 2) := arr_eq 2 (by norm_num)
  unfold conj2300 pkS
  rw [e2, comp_u ht perm_parts.2.1, comp_u perm_parts.2.1 h1]

theorem range_of {p : ℕ} (hp : CFSG.KC.Misc.ArrEnum.permB 2300 12 p = true) :
    allN 2300 (fun i => Nat.blt (pg 12 (mask 12) p i) 2300) = true :=
  range_of_permOK hp

theorem bindsK0 : Binds 2300 12 K0.S 5 4 K0.BP (k0Arrs ()) k0Base := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [k0Arrs], fun j hj => ?_, by decide,
    K0.bget⟩
  have e : K0.S j = HX.F (5 + j) := Nat.eq_of_beq_eq_true (allN_spec K0.bS j hj)
  rw [e, ← arr_eq (5 + j) (by omega)]
  unfold k0Arrs
  rw [getElem!_pos _ j (by simp; omega)]
  simp

theorem bindsL : Binds 2300 12 LC.S 6 3 LC.BP (CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LArrs ())
    CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LBase := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    by simp [CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LArrs], fun j hj => ?_, by decide,
    LC.bget⟩
  have e : LC.S j = CH.F (37 + j) := Nat.eq_of_beq_eq_true (allN_spec LC.bS j hj)
  rw [e, ← co2Arr_eq (37 + j) (by omega)]
  unfold CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LArrs
  rw [getElem!_pos _ j (by simp; omega)]
  simp

theorem wK0 : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 5 k0D = k0Words := by decide +kernel

theorem chainK0 : caseChainOK2P 2300 (k0Arrs ()) k0Base k0Words (i301K1 ()) (i301K2 ()) = true := by
  have h := rawChainK_sound (chunks := 1) (NS := K0.NS) (CH := 2300) bindsK0 K0.head K0.hl
    K0.hNS K0.hs
  rw [wK0] at h
  have e1 : eqA 2300 (k0Arrs ())[0]! (i301K1 ()) = true :=
    CertificateChecks.KernelSporSch.Co2M.eqA_self _ _
  have e2 : eqA 2300 (k0Arrs ())[1]! (i301K2 ()) = true :=
    CertificateChecks.KernelSporSch.Co2M.eqA_self _ _
  unfold caseChainOK2P
  rw [h, e1, e2]
  rfl

theorem orbitsK0 : ((rawOrbitSizes 2300 (k0Arrs ()) k0Base).prod == 360) = true := by
  rw [rawOrbitSizesK_sound bindsK0 K0.perm K0.hl, K0.orbProd]
  rfl

theorem siftL_sound {t : ℕ} (hp : CFSG.KC.Misc.ArrEnum.permB 2300 12 t = true)
    (h : siftL t = true) :
    siftA 2300 (rawLevels 2300 (CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LArrs ())
      CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LBase)
      CFSG.HardMathSupport.Dickson.I271.Co2Cent.co2LBase 0 (unpack 2300 12 t) = true :=
  siftK_sound bindsL LC.perm LC.hl rfl (range_of hp) h

theorem siftK0_sound {t : ℕ} (hp : CFSG.KC.Misc.ArrEnum.permB 2300 12 t = true)
    (h : siftK0 t = true) : inK0 (rawLevels 2300 (k0Arrs ()) k0Base) (unpack 2300 12 t) = true :=
  siftK_sound bindsK0 K0.perm K0.hl rfl (range_of hp) h

theorem small_check : smallCheck () = true := by
  have hm := mat_ok
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hconj, hz1⟩, hz2⟩, hz3⟩, hz4⟩, hz5⟩, hz6⟩, hd2⟩, hd3⟩, hd4⟩, hd5⟩,
    hd6⟩, hb⟩, hpd⟩, hpb2⟩, hpb3⟩, hss⟩ := hm
  obtain ⟨p0, p2, p3, p4, p5, p6, -, a5, a6, a2, b5, b6, c5, c6, c2, d5, d6⟩ := perm_parts
  obtain ⟨s0, l5, l6, l2, k3, k4, s5, s6⟩ := sift_parts
  have rH : MatRep.Rep 22 co2PackedVecs (i301H ()) (mP 0).1 (mP 0).2 := rep_mP (by norm_num)
  have rD : MatRep.Rep 22 co2PackedVecs (i301D ()) (mP 1).1 (mP 1).2 := rep_mP (by norm_num)
  have rS : MatRep.Rep 22 co2PackedVecs (i301S ()) (mP 2).1 (mP 2).2 := rep_mP (by norm_num)
  have rB2 : MatRep.Rep 22 co2PackedVecs (i301B2 ()) (mP 3).1 (mP 3).2 := rep_mP (by norm_num)
  have rB3 : MatRep.Rep 22 co2PackedVecs (i301B3 ()) (mP 4).1 (mP 4).2 := rep_mP (by norm_num)
  have rK1 := rep_mP (k := 5) (by norm_num)
  have rK2 := rep_mP (k := 6) (by norm_num)
  rw [← i301K1_eq] at rK1
  rw [← i301K2_eq] at rK2
  have eS : i301S () = unpack 2300 12 (HX.F 2) := arr_eq 2 (by norm_num)
  have rZ : Rep 22 co2PackedVecs CFSG.Sporadic.Co2Schreier.zArr zP.1 zP.2 :=
    CertificateChecks.KernelSporSch.Co2M.zRep
  have e0 : i301H () = unpack 2300 12 (HX.F 0) := arr_eq 0 (by norm_num)
  have e3 : i301B2 () = unpack 2300 12 (HX.F 3) := arr_eq 3 (by norm_num)
  have e4 : i301B3 () = unpack 2300 12 (HX.F 4) := arr_eq 4 (by norm_num)
  have c_vH : validA 2300 (i301H ()) = true := isInvA_rep rH
  have c_vD : validA 2300 (i301D ()) = true := isInvA_rep rD
  have c_vS : validA 2300 (i301S ()) = true := isInvA_rep rS
  have c_vB2 : validA 2300 (i301B2 ()) = true := isInvA_rep rB2
  have c_vB3 : validA 2300 (i301B3 ()) = true := isInvA_rep rB3
  have c_vX : validA 2300 (dElts ())[1]! = true := isInvA_rep rep_xB
  have c_inP : inP (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T.levels ()) (i301H ()) =
      true := by
    unfold inP CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T.levels
    exact siftK_sound CertificateChecks.KernelSpor.Co2A.binds CertificateChecks.KernelSpor.Co2A.perm
      CertificateChecks.KernelSpor.Co2A.hl e0 (range_of p0) s0
  have c_conj : eqA 2300 (i301D ()) (conj2300 (i301H ()) (invCand 2300 (i301H ()))
      (dElts ())[1]!) = true :=
    eqA_of_mat rD (rep_cmp rH (rep_cmp rep_xB (rep_inv rH))) (Nat.eq_of_beq_eq_true hconj)
  have c_pD : eqA 2300 (powArr 2300 (i301D ()) 3) (idA 2300) = true := eqId_of_mat (rep_pow rD 3) hpd
  have c_pB2 : eqA 2300 (powArr 2300 (i301B2 ()) 3) (idA 2300) = true :=
    eqId_of_mat (rep_pow rB2 3) hpb2
  have c_pB3 : eqA 2300 (powArr 2300 (i301B3 ()) 3) (idA 2300) = true :=
    eqId_of_mat (rep_pow rB3 3) hpb3
  have c_ss : eqA 2300 (compA 2300 (i301S ()) (i301S ())) (idA 2300) = true :=
    eqId_of_mat (rep_cmp rS rS) hss
  have c_27 : allLt 27 (fun t => t == 0 || !(eqA 2300 (compA 2300 (powArr 2300 (i301D ()) (t % 3))
      (compA 2300 (powArr 2300 (i301B2 ()) (t / 3 % 3)) (powArr 2300 (i301B3 ()) (t / 9))))
      (idA 2300))) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro t ht
    have h := allN_spec b27_ok t ht
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rfl
    · have h0 : Nat.beq t 0 = false := beq_false (by omega)
      rw [h0, Bool.false_or] at h
      rw [ne_of_moves (rep_cmp (rep_pow rD (t % 3)) (rep_cmp (rep_pow rB2 (t / 3 % 3))
        (rep_pow rB3 (t / 9)))) h]
      simp
  have c_512 : allLt 6 (fun t => t % 3 == 0 || !(eqA 2300 (powArr 2300
      (dzElts (i301D ()) CFSG.Sporadic.Co2Schreier.zArr)[t]! 512) (idA 2300))) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro t ht
    have h := allN_spec pow_ok t ht
    by_cases h3 : t % 3 = 0
    · simp [h3]
    · have h0 : Nat.beq (t % 3) 0 = false := beq_false h3
      rw [h0, Bool.false_or] at h
      have e : (dzElts (i301D ()) CFSG.Sporadic.Co2Schreier.zArr)[t]! =
          compA 2300 (powArr 2300 (i301D ()) (t % 3))
            (powArr 2300 CFSG.Sporadic.Co2Schreier.zArr (t / 3)) := by
        unfold dzElts
        rw [getElem!_pos _ t (by simp; omega)]
        simp
      rw [e, ne_of_moves (rep_pow (rep_cmp (rep_pow rD (t % 3)) (rep_pow rZ (t / 3))) 512) h]
      simp
  have c_o6 : allLt 6 (fun j => (i301K1 ())[o6.getD j 0]! == o6.getD (sigma1.getD j 0) 0 &&
      (i301K2 ())[o6.getD j 0]! == o6.getD (sigma2.getD j 0) 0) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff, k1_eq, k2_eq]
    intro j hj
    rw [Orb.unpack_get (o6_ok.1 j hj), Orb.unpack_get (o6_ok.1 j hj)]
    exact o6_ok.2 j hj
  have c_L1 := siftL_sound c5 l5
  have c_L2 := siftL_sound c6 l6
  have c_L3 := siftL_sound c2 l2
  rw [← conjH_eq p5 a5, ← k1_eq] at c_L1
  rw [← conjH_eq p6 a6, ← k2_eq] at c_L2
  rw [← conjH_eq p2 a2, ← eS] at c_L3
  have c_K3 := siftK0_sound p3 k3
  have c_K4 := siftK0_sound p4 k4
  have c_K5 := siftK0_sound d5 s5
  have c_K6 := siftK0_sound d6 s6
  rw [← e3] at c_K3
  rw [← e4] at c_K4
  rw [← conjS_eq p5 b5, ← k1_eq] at c_K5
  rw [← conjS_eq p6 b6, ← k2_eq] at c_K6
  obtain ⟨cols1, -, cols5, cols6⟩ := sixColsOK_arr
  rw [← i301K1_eq] at cols5
  rw [← i301K2_eq] at cols6
  have cols1' : sixColsOK (i301D ()) = true := cols1
  unfold smallCheck
  dsimp only
  rw [c_vH, c_inP, c_vD, c_vS, c_vB2, c_vB3, c_vX, c_conj, chainK0, orbitsK0,
    comm_of_mat rZ rD hz1, comm_of_mat rZ rS hz2, comm_of_mat rZ rB2 hz3, comm_of_mat rZ rB3 hz4,
    comm_of_mat rZ rK1 hz5, comm_of_mat rZ rK2 hz6, comm_of_mat rD rS hd2, comm_of_mat rD rB2 hd3,
    comm_of_mat rD rB3 hd4, comm_of_mat rD rK1 hd5, comm_of_mat rD rK2 hd6,
    comm_of_mat rB2 rB3 hb, c_pD, c_pB2, c_pB3, c_ss, c_27, c_L1, c_L2, c_L3, c_K3, c_K4, c_K5,
    c_K6, c_512, c_o6, cols5, cols6, cols1']
  rfl

end CertificateChecks.KernelCo2I301

end
