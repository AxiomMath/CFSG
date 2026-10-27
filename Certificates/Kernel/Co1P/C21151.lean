module

public import Certificates.Kernel.Co1P.C21156
public import Certificates.Kernel.Co1P.Chk21151
public import Certificates.Kernel.Co1P.Chk21151W
public import Certificates.Kernel.Co1P.Chk21151K4
public import Certificates.Kernel.Co1P.Chk21151KF
public import Certificates.Kernel.Co1P.Chk21151C
public import CFSG.Certificates.Kernel.Co1PTreeKeys

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native CertificateChecks.KernelCo1B

theorem gensArr_Kz {l : Nat} (hl : l < 6) : (gensArr gensKz)[l]! = unpackR 24 (getL 0 GZ l) := by
  have e : getL 0 GZ l = getL oneK GDS (gensKz.getD l 0 - 1) := by interval_cases l <;> rfl
  have hl' : l < gensKz.length := hl
  rw [e, gensArr, getElem!_pos _ l (by simpa using hl'),
    List.getElem_toArray, List.getElem_map, gEl_eq, ← List.getD_eq_getElem _ 0]

theorem gensInvArr_Kz {l : Nat} (hl : l < 6) :
    (gensInvArr gensKz)[l]! = unpackR 24 (getL 0 GZI l) := by
  have e : getL 0 GZI l = getL oneK GDIS (gensKz.getD l 0 - 1) := by interval_cases l <;> rfl
  have hl' : l < gensKz.length := hl
  rw [e, gensInvArr, getElem!_pos _ l (by simpa using hl'),
    List.getElem_toArray, List.getElem_map, gElInv_eq, ← List.getD_eq_getElem _ 0]

theorem gensArr_Kz_size : (gensArr gensKz).size = 6 := by simp [gensArr, gensKz]

theorem gensArr_KzL : gensArr gensKz = (GZ.map (unpackR 24)).toArray := by
  unfold gensArr GZ
  rw [List.map_map, List.map_congr_left (fun j _ => gEl_eq j)]
  rfl

theorem centOK_of {L : List Nat} {GK : List Nat} {Z : Nat} (hL : gensArr L = (GK.map (unpackR 24)).toArray)
    (h : (GK.all fun g => andB (eqK (mulWK g AL) (mulWK AL g)) (eqK (mulWK g Z) (mulWK Z g))) = true) :
    centOK (gensArr L) (unpackR 24 Z) = true := by
  unfold centOK
  rw [hL, List.all_toArray, List.all_map, List.all_eq_true]
  intro g hg
  have hg' := List.all_eq_true.1 h g hg
  rw [andB_eq] at hg'
  rw [Function.comp_apply, iotaA_K, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW,
    CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, beq_unpack, beq_unpack]
  exact hg'

theorem centOK_Ke : centOK (gensArr gensKe) CFSG.Sporadic.Co1Patterson.Native.eRows = true := by
  have hsm := tri_small
  unfold triSmallK at hsm
  simp only [andB_eq, Bool.and_eq_true] at hsm
  obtain ⟨-, s3, -⟩ := hsm
  rw [CFSG.Sporadic.Co1Patterson.Native.eRows, repRows_eq]
  refine centOK_of gensArr_KeL ?_
  simp only [andB_eq]
  exact s3

theorem sub45_parts : (eqK (mulWK (mulWK AL (repK 6)) (mulWK AL (repK 6))) (repK 1) = true ∧
      eqK (mulWK (mulWK AL (repK 7)) (mulWK AL (repK 7))) (repK 1) = true ∧
      eqK (mulWK (mulWK (mulWK AL (repK 9)) (mulWK AL (repK 9))) (mulWK AL (repK 9))) (repK 1) = true) ∧
    (memE (mulWK (mulWK (repXiK 1) (repK 4)) (repXK 1)) = true ∧
      mem4 (mulWK (mulWK (repXiK 1) (repK 8)) (repXK 1)) = true ∧
      mem4 (mulWK (mulWK (repXiK 0) (repK 5)) (repXK 0)) = true) ∧
    (invsOK GZ GZI = true ∧ lenL GZ = 6 ∧
      (GZ.all fun g => andB (eqK (mulWK g AL) (mulWK AL g)) (eqK (mulWK g (repK 0)) (mulWK (repK 0) g))) =
        true) := by
  have h := sub45_ok
  unfold sub45K at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h1
  obtain ⟨h5, h6⟩ := CFSG.KC.TreeK.andB_true h3
  obtain ⟨h7, h8⟩ := CFSG.KC.TreeK.andB_true h2
  obtain ⟨h9, h10⟩ := CFSG.KC.TreeK.andB_true h7
  obtain ⟨h11, h12⟩ := CFSG.KC.TreeK.andB_true h10
  obtain ⟨h13, h14⟩ := CFSG.KC.TreeK.andB_true h8
  obtain ⟨h15, h16⟩ := CFSG.KC.TreeK.andB_true h13
  exact ⟨⟨h5, h6, h4⟩, ⟨h9, h11, h12⟩, ⟨h15, Nat.eq_of_beq_eq_true h16, h14⟩⟩

theorem recs4C_len : (recsT orb4cMasks).length = 34559 := by
  have h := recs4C_lenB
  rw [Nat.beq_eq] at h
  exact h

theorem recsF8_len : (recsT fib8Masks).length = 24575 := by
  have h := recsF8_lenB
  rw [Nat.beq_eq] at h
  exact h

theorem recsF5_len : (recsT fib5Masks).length = 16383 := by
  have h := recsF5_lenB
  rw [Nat.beq_eq] at h
  exact h

theorem invs_Ke : invsOK GE GEI = true := by
  have h := loc_ok.1
  rw [orbChk_eq] at h
  exact (CFSG.KC.TreeK.andB_true (CFSG.KC.TreeK.andB_true (CFSG.KC.TreeK.andB_true h).2).1).2

theorem fibre_small {k np n : Nat} {ms : List Nat} (h : orbChk GE GEI 6 (repK k) np (recsT ms) = true)
    (hn : (recsT ms).length + 1 = n) :
    fibreOK gensKe eRows (repRows k) n (treeT ms) = true := by
  unfold fibreOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [repRows_eq, treeT_eq]
  exact ⟨⟨centOK_Ke, orbOK_of_chk gensArr_Ke_size (fun _ hl => gensArr_Ke hl)
    (fun _ hl => gensInvArr_Ke hl) h⟩, by rw [mkOrbT_size, hn]⟩

theorem keysF8 : ∀ s < 24576, keyAtP 24576 64 skF8 ixF8 ptF8 s = true :=
  chunks_all (f := keyAtP 24576 64 skF8 ixF8 ptF8) (N := 24576) (nc := 384) (by decide)
    fun c hc => KeyF8.all c hc

theorem keysF5 : ∀ s < 16384, keyAtP 16384 64 skF5 ixF5 ptF5 s = true :=
  chunks_all (f := keyAtP 16384 64 skF5 ixF5 ptF5) (N := 16384) (nc := 256) (by decide)
    fun c hc => KeyF5.all c hc

theorem keys4C : ∀ s < 34560, keyAtP 34560 64 sk4C ix4C pt4C s = true :=
  chunks_all (f := keyAtP 34560 64 sk4C ix4C pt4C) (N := 34560) (nc := 540) (by decide)
    fun c hc => Key4C.all c hc

theorem fibre8 : fibreOK gensKe eRows (repRows 8) 24576 (treeT fib8Masks) = true := by
  unfold fibreOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [repRows_eq, treeT_eq]
  have hN : (recsT fib8Masks).length + 1 = 24576 := by rw [recsF8_len]
  exact ⟨⟨centOK_Ke, orbOK_of_nodup gensArr_Ke_size (fun _ hl => gensArr_Ke hl)
    (fun _ hl => gensInvArr_Ke hl) walkF8_hs walkF8_his rfl invs_Ke
    (ptsL_nodup walkF8_hs walkF8_his recsF8_pin hN keysF8 (by decide))⟩, by rw [mkOrbT_size, hN]⟩

theorem fibre5 : fibreOK gensKz CFSG.Sporadic.Co1Patterson.Native.zRows (repRows 5) 16384
    (treeT fib5Masks) = true := by
  obtain ⟨-, -, hinv, -, hc⟩ := sub45_parts
  unfold fibreOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [repRows_eq, treeT_eq, CFSG.Sporadic.Co1Patterson.Native.zRows, repRows_eq]
  have hN : (recsT fib5Masks).length + 1 = 16384 := by rw [recsF5_len]
  exact ⟨⟨centOK_of gensArr_KzL hc, orbOK_of_nodup gensArr_Kz_size (fun _ hl => gensArr_Kz hl)
    (fun _ hl => gensInvArr_Kz hl) walkF5_hs walkF5_his rfl hinv
    (ptsL_nodup walkF5_hs walkF5_his recsF5_pin hN keysF5 (by decide))⟩, by rw [mkOrbT_size, hN]⟩

theorem orb4c_mem (X : Nat) : (ptSet orb4c).contains (unpackR 24 X) = mem4 X := by
  have hN : (recsT orb4cMasks).length + 1 = 34560 := by rw [recs4C_len]
  rw [orb4c, repRows_eq, treeT_eq, contains_mkOrbT (fun l hl => brayArr_get hl)
    (fun l hl => brayInvArr_get hl) walk4C_hs walk4C_his X,
    ptsL_any walk4C_hs walk4C_his recs4C_pin hN keys4C (dd := 16) (by decide) (by decide) X]
  rfl

theorem orb4c_size : orb4c.c.pts.size = 34560 := by
  rw [orb4c, repRows_eq, treeT_eq, mkOrbT_size, recs4C_len]

theorem sumN_congr {n : Nat} {F G : Nat → Nat} (h : ∀ c < n, F c = G c) : sumN n F = sumN n G := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumN_succ, sumN_succ, h n (by omega), ih fun c hc => h c (by omega)]

theorem cnt_parts {c : Nat} (hc : c < 197) :
    cntK 12600 (fun i => memE (conjE i (repK 4))) c = getL 0 CN4 c ∧
      cntK 12600 (fun i => mem4 (conjE i (repK 8))) c = getL 0 CN8 c := by
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true (Cnt21151.all c hc)
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem conjPt_E {i : Nat} (hi : i < 12600) (B : Nat) :
    conjPt orbE (repX 1) (repXi 1) i (unpackR 24 B) = unpackR 24 (conjE i B) := by
  rw [conjPt, orbE_his' hi, orbE_hs' hi, repX_eq, repXi_eq]
  simp only [CFSG.KC.F2W.mul_unpackW]
  rfl

theorem conjPt_Q {i : Nat} (hi : i < 270) (B : Nat) :
    conjPt orbQ (repX 0) (repXi 0) i (unpackR 24 B) = unpackR 24 (conjQ i B) := by
  rw [conjPt, orbQ_his' hi, orbQ_hs' hi, repX_eq, repXi_eq]
  simp only [CFSG.KC.F2W.mul_unpackW]
  rfl

theorem countE4 : countN orbE (repX 1) (repXi 1) (ptSet orbE) (repRows 4) = 45 := by
  have hs := cnt_sums
  obtain ⟨h1, -⟩ := CFSG.KC.TreeK.andB_true hs
  unfold countN
  rw [orbE_size', repRows_eq, List.filter_congr (q := fun i => memE (conjE i (repK 4))) (fun i hi => by
    rw [conjPt_E (List.mem_range.1 hi), orbE_mem]),
    count_chunks _ (nc := 197) (by decide), sumN_congr fun c hc => (cnt_parts hc).1]
  exact Nat.eq_of_beq_eq_true h1

theorem countE8 : countN orbE (repX 1) (repXi 1) (ptSet orb4c) (repRows 8) = 25 := by
  have hs := cnt_sums
  obtain ⟨-, h2⟩ := CFSG.KC.TreeK.andB_true hs
  unfold countN
  rw [orbE_size', repRows_eq, List.filter_congr (q := fun i => mem4 (conjE i (repK 8))) (fun i hi => by
    rw [conjPt_E (List.mem_range.1 hi), orb4c_mem]),
    count_chunks _ (nc := 197) (by decide), sumN_congr fun c hc => (cnt_parts hc).2]
  exact Nat.eq_of_beq_eq_true h2

theorem countQ5 : countN orbQ (repX 0) (repXi 0) (ptSet orb4c) (repRows 5) = 9 := by
  unfold countN
  rw [orbQ_size', repRows_eq, List.filter_congr (q := fun i => mem4 (conjQ i (repK 5))) (fun i hi => by
    rw [conjPt_Q (List.mem_range.1 hi), orb4c_mem]),
    count_chunks _ (nc := 5) (by decide)]
  exact Nat.eq_of_beq_eq_true cntQ_ok

theorem valid_E (B : Nat) : conjValid orbE (repX 1) (repXi 1) (unpackR 24 B) = true := by
  unfold conjValid
  rw [orbE_size', List.all_eq_true]
  intro i hi
  rw [conjPt_E (List.mem_range.1 hi)]
  exact validRows_unpackR _

theorem valid_Q (B : Nat) : conjValid orbQ (repX 0) (repXi 0) (unpackR 24 B) = true := by
  unfold conjValid
  rw [orbQ_size', List.all_eq_true]
  intro i hi
  rw [conjPt_Q (List.mem_range.1 hi)]
  exact validRows_unpackR _

theorem suborb4 : suborbCheck4 = true := by
  obtain ⟨⟨a1, a2, a3⟩, -⟩ := sub45_parts
  obtain ⟨f6, f7, f9, -⟩ := fibS_ok
  unfold suborbCheck4
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  obtain ⟨n6, n7, n9, -⟩ := fibS_len
  rw [Nat.beq_eq] at n6 n7 n9
  refine ⟨?_, ?_, ?_, fibre_small f6 (by rw [n6]), fibre_small f7 (by rw [n7]),
    fibre_small f9 (by rw [n9])⟩
  · rw [CFSG.Sporadic.Co1Patterson.Native.eRows, repRows_eq, repRows_eq, iotaA_K,
      CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq a1
  · rw [CFSG.Sporadic.Co1Patterson.Native.eRows, repRows_eq, repRows_eq, iotaA_K,
      CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq a2
  · rw [CFSG.Sporadic.Co1Patterson.Native.eRows, repRows_eq, repRows_eq, iotaA_K]
    simp only [CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq a3

theorem suborb5 : suborbCheck5 = true := by
  obtain ⟨-, ⟨m1, m2, m3⟩, -⟩ := sub45_parts
  obtain ⟨-, -, -, f4⟩ := fibS_ok
  obtain ⟨-, -, -, n4⟩ := fibS_len
  rw [Nat.beq_eq] at n4
  unfold suborbCheck5
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, countE4, countE8, countQ5, fibre_small f4 (by rw [n4]), fibre8,
    fibre5⟩
  · rw [repRows_eq, repXi_eq, repX_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, orbE_mem]
    exact m1
  · rw [repRows_eq, repXi_eq, repX_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, orb4c_mem]
    exact m2
  · rw [repRows_eq, repXi_eq, repX_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, orb4c_mem]
    exact m3
  · rw [repRows_eq]
    exact valid_E _
  · rw [repRows_eq]
    exact valid_E _
  · rw [repRows_eq]
    exact valid_Q _

open Certificates in
theorem c21151 : CFSG.Sporadic.Co1Patterson.Native.suborbCheck4 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.suborbCheck5 = true := ⟨suborb4, suborb5⟩

end CertificateChecks.KernelCo1P

end
