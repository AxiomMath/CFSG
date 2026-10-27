module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQAssem
public import Certificates.Kernel.BabyMonster.CTIB.CosetQ6
public import Certificates.Kernel.BabyMonster.CTIB.CosetQ8
public import Certificates.Kernel.BabyMonster.CTIB.CosetQ10
public import Certificates.Kernel.BabyMonster.CTIB.CosetQWords
public import Certificates.Kernel.BabyMonster.CTIB.CosetQSym
public import Certificates.Data.Kernel.BabyMonster.CTIB.CentWords
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB

set_option exponentiation.threshold 1024

theorem loq_eq : LOq = loOf (gArr ()) := Nat.eq_of_beq_eq_true (by quickRfl)

theorem g0_eq : genImgs 0 = arrOf (nthN Syms 0) := by decide +kernel

theorem g1_eq : genImgs 1 = arrOf (nthN Syms 1) := by decide +kernel

theorem cw_steps : centWordsL = (List.range 45).map fun t => (nthLL Steps t).flatMap symLetters := by
  decide +kernel

theorem steps_lt : ∀ t < 45, (nthLL Steps t).all (· < 17) = true := by decide +kernel

theorem ds_eq : ∀ t < 45, deltaVals.getD t 0 = nthN Ds t := by decide +kernel

theorem ct_eq : ∀ s < 17, nthN CTs s = ctabK (loOf (gArr ())) (nthN Syms s) := fun s hs => by
  have h := cqw_cts s hs
  unfold ctOK at h
  rw [loq_eq, beq_true] at h
  exact h.symm

theorem pow_fold {S CT : ℕ} (hct : CT = ctabK (loOf (gArr ())) S) : ∀ n,
    arrOf (Nat.rec (motive := fun _ => ℕ) (id32 22) (fun _ acc => compAutF S CT acc) n) =
      autPow (gArr ()) (arrOf S) n
  | 0 => (id23_eq).symm
  | n + 1 => by
    change arrOf (compAutF S CT (Nat.rec (motive := fun _ => ℕ) (id32 22)
      (fun _ acc => compAutF S CT acc) n)) = _
    rw [hct, compAutF_ctabK _ symG_gArr, compAut_loOf _ symG_gArr, ← hct, pow_fold hct n,
      autPow]

theorem symFacts : SymFacts (gArr ()) Syms := by
  have h := cqw_syms
  rw [loq_eq] at h
  unfold symsOK at h
  obtain ⟨h0, h⟩ := andB_true.1 h
  obtain ⟨h1, h⟩ := andB_true.1 h
  obtain ⟨hsq, h⟩ := andB_true.1 h
  obtain ⟨hpow, h⟩ := andB_true.1 h
  obtain ⟨h47, hipow⟩ := andB_true.1 h
  have hr := cqs_rel
  rw [loq_eq] at hr
  have hi := cqs_inv
  rw [loq_eq] at hi
  obtain ⟨hi1, hi13⟩ := andB_true.1 hi
  have e : ∀ {A B C : ℕ}, Nat.beq (compAut (loOf (gArr ())) A B) C = true →
      autComp (gArr ()) (arrOf A) (arrOf B) = arrOf C := fun hc => by
    rw [← compAut_loOf _ symG_gArr, beq_true.1 hc]
  refine ⟨g0_eq, g1_eq, ?_, (relOK_spec _ symG_gArr h0).2, (relOK_spec _ symG_gArr h1).2,
    (relOK_spec _ symG_gArr hr).2, by rw [e hsq, ← id23_eq], by rw [e hi1, ← id23_eq],
    by rw [e hi13, ← id23_eq], fun r hr => (e (allLt_true.1 hpow r hr)).symm,
    fun r hr => ?_⟩
  · rw [genInvImgs, g1_eq, ← beq_true.1 h47]
    exact (pow_fold (ct_eq 1 (by decide)) 47).symm
  · exact (e (allLt_true.1 hipow r hr)).symm

theorem wOK_eq {t : ℕ} (ht : t < 45) :
    wordKF Syms CTs (nthLL Steps t) (id32 22) = nthN Gs t ∧ relOK (loOf (gArr ())) (nthN Gs t) = true := by
  have h := cqw_words t ht
  unfold wOK at h
  rw [loq_eq] at h
  obtain ⟨h1, h2⟩ := andB_true.1 h
  exact ⟨beq_true.1 h1, h2⟩

theorem rank6 : RankOK (gArr ()) AH6 6 Bs6 T6 4194304 VT6 PT6 TR6 RT6 529 Gs Ds 0 where
  symm := symG_gArr
  setup := by rw [← loq_eq]; exact cq6_setup
  hk := by decide
  hw := Or.inr rfl
  v := fun j hj => by rw [← loq_eq]; exact cq6_v j hj
  pt := fun p hp => by rw [← loq_eq]; exact cq6_pt p hp
  inc := (andB_true.1 cq6_agg).2
  clos := fun q hq => by rw [← loq_eq]; exact cq6_clos q hq
  tr := fun q hq => by rw [← loq_eq]; exact cq6_tr q hq
  d := fun t ht => by rw [← loq_eq, Nat.zero_add]; exact cq6_d t ht
  rel := fun t ht => (wOK_eq (by omega)).2

theorem rank8 : RankOK (gArr ()) AH8 8 Bs8 T8 0 VT8 PT8 TR8 RT8 37 Gs Ds 15 where
  symm := symG_gArr
  setup := by rw [← loq_eq]; exact cq8_setup
  hk := by decide
  hw := Or.inl rfl
  v := fun j hj => by rw [← loq_eq]; exact cq8_v j hj
  pt := fun p hp => by rw [← loq_eq]; exact cq8_pt p hp
  inc := (andB_true.1 cq8_agg).2
  clos := fun q hq => by rw [← loq_eq]; exact cq8_clos q hq
  tr := fun q hq => by rw [← loq_eq]; exact cq8_tr q hq
  d := fun t ht => by rw [← loq_eq]; exact cq8_d t ht
  rel := fun t ht => (wOK_eq (by omega)).2

theorem rank10 : RankOK (gArr ()) AH10 10 Bs10 T10 4194304 VT10 PT10 TR10 RT10 3 Gs Ds 30 where
  symm := symG_gArr
  setup := by rw [← loq_eq]; exact cq10_setup
  hk := by decide
  hw := Or.inr rfl
  v := fun j hj => by rw [← loq_eq]; exact cq10_v j hj
  pt := fun p hp => by rw [← loq_eq]; exact cq10_pt p hp
  inc := (andB_true.1 cq10_agg).2
  clos := fun q hq => by rw [← loq_eq]; exact cq10_clos q hq
  tr := fun q hq => by rw [← loq_eq]; exact cq10_tr q hq
  d := fun t ht => by rw [← loq_eq]; exact cq10_d t ht
  rel := fun t ht => (wOK_eq (by omega)).2

theorem words_of (hP : parseWords centWordStr = centWordsL) {k : ℕ} {j : ℕ}
    (hj : rankOff k + j < 45) :
    centWordN k j = (nthLL Steps (rankOff k + j)).flatMap symLetters := by
  rw [centWordN, hP, cw_steps]
  simp [hj]

theorem steps_of {t : ℕ} (ht : t < 45) : ∀ s ∈ nthLL Steps t, s < 17 := by
  have := steps_lt t ht
  rw [List.all_eq_true] at this
  exact fun s hs => of_decide_eq_true (this s hs)

theorem lift6 : (liftImgsN 6).toArray = arrOf AH6 := by decide +kernel

theorem rows6 : ∀ i < 22, (liftRowsN 6).toArray[i]! = fld32 AH6 i % 2 ^ 22 := by decide +kernel

theorem sum6 : ((List.range 529).map (sizeOf 6 PT6)).sum = 67584 := by decide +kernel

theorem fr6 : fusionRecsN 6 = (List.range 5).map fun r =>
    (((Finset.range 529).filter (fun q => labOf PT6 q = r)).card,
      ((Finset.range 529).filter (fun q => labOf PT6 q = r)).sum (sizeOf 6 PT6),
      repOf PT6 (fld32 RT6 r)) := by decide +kernel

theorem root6 : ∀ r < 5, fld32 RT6 r < 529 ∧ fld32 TR6 (fld32 RT6 r) = 0 ∧
    labOf PT6 (fld32 RT6 r) = r := by decide +kernel

theorem lift8 : (liftImgsN 8).toArray = arrOf AH8 := by decide +kernel

theorem rows8 : ∀ i < 22, (liftRowsN 8).toArray[i]! = fld32 AH8 i % 2 ^ 22 := by decide +kernel

theorem sum8 : ((List.range 37).map (sizeOf 8 PT8)).sum = 18432 := by decide +kernel

theorem fr8 : fusionRecsN 8 = (List.range 3).map fun r =>
    (((Finset.range 37).filter (fun q => labOf PT8 q = r)).card,
      ((Finset.range 37).filter (fun q => labOf PT8 q = r)).sum (sizeOf 8 PT8),
      repOf PT8 (fld32 RT8 r)) := by decide +kernel

theorem root8 : ∀ r < 3, fld32 RT8 r < 37 ∧ fld32 TR8 (fld32 RT8 r) = 0 ∧
    labOf PT8 (fld32 RT8 r) = r := by decide +kernel

theorem lift10 : (liftImgsN 10).toArray = arrOf AH10 := by decide +kernel

theorem rows10 : ∀ i < 22, (liftRowsN 10).toArray[i]! = fld32 AH10 i % 2 ^ 22 := by
  decide +kernel

theorem sum10 : ((List.range 3).map (sizeOf 10 PT10)).sum = 6144 := by decide +kernel

theorem fr10 : fusionRecsN 10 = (List.range 2).map fun r =>
    (((Finset.range 3).filter (fun q => labOf PT10 q = r)).card,
      ((Finset.range 3).filter (fun q => labOf PT10 q = r)).sum (sizeOf 10 PT10),
      repOf PT10 (fld32 RT10 r)) := by decide +kernel

theorem root10 : ∀ r < 2, fld32 RT10 r < 3 ∧ fld32 TR10 (fld32 RT10 r) = 0 ∧
    labOf PT10 (fld32 RT10 r) = r := by decide +kernel

theorem frs_ok : repsIncreasing ((fusionRecsN 6).map (·.2.2)) = true ∧
    ((fusionRecsN 6).map (·.2.1)).sum = 67584 ∧
    repsIncreasing ((fusionRecsN 8).map (·.2.2)) = true ∧
    ((fusionRecsN 8).map (·.2.1)).sum = 18432 ∧
    repsIncreasing ((fusionRecsN 10).map (·.2.2)) = true ∧
    ((fusionRecsN 10).map (·.2.1)).sum = 6144 := by decide +kernel

theorem coset6 (hP : parseWords centWordStr = centWordsL) (hO : orbitRecs 6 = qrecs 6 PT6 529) :
    cosetOK 6 67584 = true :=
  cosetOK_of (nl := 5) (Steps := Steps) rank6 symFacts ct_eq lift6 rows6 (by decide)
    (by
      change 2 ^ 7 * cntV VT6 1024 = 67584
      rw [beq_true.1 (andB_true.1 cq6_agg).1]
      rfl)
    hO sum6 fr6 root6 frs_ok.1 frs_ok.2.1 (fun j hj => words_of hP (by simp [rankOff]; omega))
    (fun j hj => steps_of (by omega)) (fun j hj => (wOK_eq (by omega)).1)
    (fun j hj => by rw [deltaN, ds_eq _ (by simp [rankOff]; omega)]; rfl)

theorem coset8 (hP : parseWords centWordStr = centWordsL) (hO : orbitRecs 8 = qrecs 8 PT8 37) :
    cosetOK 8 18432 = true :=
  cosetOK_of (nl := 3) (Steps := Steps) rank8 symFacts ct_eq lift8 rows8 (by decide)
    (by
      change 2 ^ 9 * cntV VT8 64 = 18432
      rw [beq_true.1 (andB_true.1 cq8_agg).1]
      rfl)
    hO sum8 fr8 root8 frs_ok.2.2.1 frs_ok.2.2.2.1
    (fun j hj => words_of hP (by simp [rankOff]; omega))
    (fun j hj => steps_of (by omega)) (fun j hj => (wOK_eq (by omega)).1)
    (fun j hj => by rw [deltaN, ds_eq _ (by simp [rankOff]; omega)]; rfl)

theorem coset10 (hP : parseWords centWordStr = centWordsL) (hO : orbitRecs 10 = qrecs 10 PT10 3) :
    cosetOK 10 6144 = true :=
  cosetOK_of (nl := 2) (Steps := Steps) rank10 symFacts ct_eq lift10 rows10 (by decide)
    (by
      change 2 ^ 11 * cntV VT10 4 = 6144
      rw [beq_true.1 (andB_true.1 cq10_agg).1]
      rfl)
    hO sum10 fr10 root10 frs_ok.2.2.2.2.1 frs_ok.2.2.2.2.2
    (fun j hj => words_of hP (by simp [rankOff]; omega))
    (fun j hj => steps_of (by omega)) (fun j hj => (wOK_eq (by omega)).1)
    (fun j hj => by rw [deltaN, ds_eq _ (by simp [rankOff]; omega)]; rfl)

@[expose] noncomputable def imgsL : List ℕ :=
  (List.range 45).flatMap fun t => (List.range 22).map (fld32 (nthN Gs t))

theorem imgs_blocks : ∀ t < 45,
    (arrOf (nthN Gs t)).toList = (imgsL.drop (22 * t)).take 22 := by decide +kernel

theorem centImgs_of (hP : parseWords centWordStr = centWordsL) (hI : parseNats centImgsStr = imgsL) :
    centImgsOK () = true := by
  unfold centImgsOK
  rw [hP, hI, List.all_eq_true]
  intro t ht
  have ht' := List.mem_range.1 ht
  rw [beq_iff_eq, cw_steps, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range ht', Option.map_some, Option.getD_some,
    word_imgs symFacts ct_eq _ (steps_of ht'), (wOK_eq ht').1]
  exact imgs_blocks t ht'

theorem cosetCheck_of (hP : parseWords centWordStr = centWordsL)
    (hO6 : orbitRecs 6 = qrecs 6 PT6 529) (hO8 : orbitRecs 8 = qrecs 8 PT8 37)
    (hO10 : orbitRecs 10 = qrecs 10 PT10 3) (hI : parseNats centImgsStr = imgsL) :
    cosetCheck () = true := by
  unfold cosetCheck
  rw [coset6 hP hO6, coset8 hP hO8, coset10 hP hO10, centImgs_of hP hI]
  rfl

end CertificateChecks.KernelBM.CTIB.CosetQ

end
