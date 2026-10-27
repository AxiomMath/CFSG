module

public import Certificates.Kernel.Co1I301.Orb810305
public import Certificates.Kernel.Co1P.C21158
public import Certificates.Kernel.Co1ThreeK.LettersEq
public import CFSG.Certificates.Kernel.Co1I301KSound
public import CFSG.Certificates.Kernel.Co1BSpinSound
public import CFSG.Certificates.Kernel.SporSch.Co1ConjTreeSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSegFSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1I301

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KC.Co1I301 CFSG.KLie.CT
  CFSG.KC.M1F2 CertificateChecks.KernelCo1P CFSG.Sporadic.Co1I301.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native
open CFSG.KC.Co1BSpin (allN_true')
open CFSG.KS.SporSch.M24 (gtPinK bfsMemK bfsK ctStepK gtBFS_of_K bfsMemK_sound bfsTree
  unpackR_eq_unpack conjTree_of_K bfsHeadK_root bfsK_of_seg)

theorem cDag_eq : cDag () = (KI.CDS.map (unpackR 24), KI.CDIS.map (unpackR 24), true) := by
  rw [cDag, gBase_eq]
  exact dag_sound kDag

theorem cEl_eq (j : Nat) : cEl (cDag ()) j = unpackR 24 (elK j) := by
  unfold cEl
  rw [cDag_eq]
  dsimp only
  rw [one_eq]
  exact CFSG.KC.Co1BSpin.getD_map_unpack oneK KI.CDS (j - 1)

theorem d_eq : dRw () = unpackR 24 DK := cEl_eq 21
theorem k1_eq : k1Rw () = unpackR 24 K1K := cEl_eq 22
theorem k2_eq : k2Rw () = unpackR 24 K2K := cEl_eq 23
theorem e_eq (i : Nat) : eRw i = unpackR 24 (EK i) := cEl_eq _
theorem r_eq (i : Nat) : rRw i = unpackR 24 (RK i) := cEl_eq _
theorem a_eq : aRw = unpackR 24 AL := iotaA_K

theorem c_dag : chkDag () = true := by
  have h1 : (cDag ()).2.2 = true := by rw [cDag_eq]
  have h2 : ((cDag ()).1.length == 32) = true := by
    rw [cDag_eq, List.length_map, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true kLen
  have h3 : ((List.range 32).all fun j =>
      CFSG.Sporadic.Co1.InvNative.validRows (cEl (cDag ()) (j + 1))) = true :=
    List.all_eq_true.2 fun j _ => by rw [cEl_eq]; exact validRows_unpackR _
  unfold chkDag
  rw [h1, h2, h3]
  rfl

theorem andB_parts {a b : Bool} (h : andB a b = true) : a = true ∧ b = true :=
  (co1I301_andB a b).1 h

theorem commR_of {x y : Nat} (h : commK x y = true) :
    commR (unpackR 24 x) (unpackR 24 y) = true := by
  unfold commR
  rw [CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, beq_unpack]
  exact h

theorem not_of_notB' {b : Bool} (h : notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem pow_one_of {x : Nat} {e : Nat} (h : eqK (powWK x e) oneK = true) :
    (pow (unpackR 24 x) e == one) = true := by
  rw [CFSG.KC.Co1BSpin.pow_unpack', one_eq, beq_unpack]
  exact h

theorem kSub : (CFSG.HardMathSupport.Dickson.I271.TabMFive.subOneRows (unpackR 24 DK) ==
    unpackR 24 DM1) = true := by
  decide +kernel

theorem kFix : CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCheck (unpackR 24 DK) (unpackR 24 oneK)
    (unpackR 24 KI.DSI) 24 = true := by
  decide +kernel

theorem c_d : chkD () = true := by
  have h := kD
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hs : CFSG.HardMathSupport.Dickson.I271.TabMFive.subOneRows (unpackR 24 DK) = unpackR 24 DM1 :=
    beq_iff_eq.1 kSub
  have hi : inv (unpackR 24 DM1) = unpackR 24 KI.DSI := inv_sound' kInvS
  unfold chkD
  rw [d_eq, a_eq, hs, hi, pow_one_of h1, commR_of h3, one_eq, kFix, bne, beq_unpack,
    not_of_notB' h2]
  rfl

theorem c_roots : chkRoots () = true := by
  have h := kRoots
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  unfold chkRoots
  simp only [rootFix, List.all_cons, List.all_nil, Bool.and_true]
  rw [CertificateChecks.KernelCo1ThreeK.rootRows_eq (by decide),
    CertificateChecks.KernelCo1ThreeK.rootRows_eq (by decide),
    CertificateChecks.KernelCo1ThreeK.rootRows_eq (by decide), ← unpackR_eq_unpack,
    ← unpackR_eq_unpack, ← unpackR_eq_unpack, CFSG.KC.F2W.act_unpackR rfl,
    CFSG.KC.F2W.act_unpackR rfl, CFSG.KC.F2W.act_unpackR rfl, Nat.eq_of_beq_eq_true h0,
    Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  decide

theorem bray_gens : brayArr = CFSG.KS.SporSch.M24.gensArr 8 BKM := by
  apply Array.ext (by simp [CFSG.KS.SporSch.M24.gensArr, brayArr_size])
  intro i h1 h2
  have hi : i < 8 := by simpa [brayArr_size] using h1
  rw [← getElem!_pos brayArr i h1, brayArr_get hi]
  simp [CFSG.KS.SporSch.M24.gensArr, BKM, unpackR_eq_unpack]

theorem brayInv_gens : brayInvArr = CFSG.KS.SporSch.M24.gensArr 8 BIKM := by
  have hs : brayInvArr.size = 8 := by simp [brayInvArr, brayArr_size]
  apply Array.ext (by simp [CFSG.KS.SporSch.M24.gensArr, hs])
  intro i h1 h2
  have hi : i < 8 := by simpa [hs] using h1
  rw [← getElem!_pos brayInvArr i h1, brayInvArr_get hi]
  simp [CFSG.KS.SporSch.M24.gensArr, BIKM, unpackR_eq_unpack]

theorem kDT' : DT.L0.N = 8960 ∧ DT.L0.PAR 0 = 0 ∧ DT.L0.LAB 0 = 0 ∧
    bfsK (ctStepK BKM BIKM) DT.L0.P DT.L0.PAR DT.L0.LAB DT.L0.W DT.L0.S 8 8961 8960 DK = true := by
  obtain ⟨hN, hh⟩ := Bool.and_eq_true _ _ ▸ kDTh
  obtain ⟨-, hp0, hl0⟩ := bfsHeadK_root hh
  exact ⟨Nat.eq_of_beq_eq_true hN, hp0, hl0, bfsK_of_seg hh kDTs⟩

theorem kRec' : KI.RP.length = 8959 ∧ KI.RL.length = 8959 ∧
    eqListK DT.L0.PAR KI.RP 1 = true ∧ eqListK DT.L0.LAB KI.RL 1 = true := by
  have h := kRec
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem ofFn_cons {F : Nat → Nat} {L : List Nat} (h0 : F 0 = 0) (hl : L.length = 8959)
    (h : eqListK F L 1 = true) :
    (Array.ofFn (n := 8960) fun i => F i.val) = (0 :: L).toArray := by
  apply Array.ext (by simp [hl])
  intro i h1 h2
  rw [Array.getElem_ofFn]
  simp only [List.getElem_toArray]
  cases i with
  | zero => simpa using h0
  | succ i =>
    rw [List.getElem_cons_succ, eqListK_sound h i (by simp at h2; omega)]
    congr 1
    omega

theorem conjTree_eq : conjTree brayArr brayInvArr (unpackR 24 DK) 8960 =
    treeArr (zipK KI.RP KI.RL) := by
  obtain ⟨hN, hp0, hl0, hb⟩ := kDT'
  obtain ⟨hpl, hll, hp, hl⟩ := kRec'
  have hlen : KI.RP.length = KI.RL.length := by rw [hpl, hll]
  rw [bray_gens, brayInv_gens, unpackR_eq_unpack, conjTree_of_K hb, treeArr, zipK_fst hlen,
    zipK_snd hlen, ofFn_cons hp0 hpl hp, ofFn_cons hl0 hll hl]

theorem c_orbit : chkOrbit () = true := by
  have hok := orbOK_of_chk (ng := 8) brayArr_size (fun l hl => brayArr_get hl)
    (fun l hl => brayInvArr_get hl) kOrb
  have hsz : (mkOrbT brayArr brayInvArr (unpackR 24 DK) (treeArr (zipK KI.RP KI.RL))).c.pts.size =
      8960 := by
    rw [mkOrbT_size, zipK_length (by rw [kRec'.1, kRec'.2.1]), kRec'.1]
  unfold chkOrbit dOrb
  rw [d_eq, conjTree_eq, hok, hsz]
  rfl

theorem kR0' : gtPinK R0M 7 128 R0T.N R0T.P R0T.PAR R0T.LAB R0T.W R0T.S = true ∧ R0T.N = 128 := by
  have h := kR0
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem r0Gens_eq : r0Gens () = CFSG.KS.SporSch.M24.gensArr 7 R0M := by
  apply Array.ext (by simp [CFSG.KS.SporSch.M24.gensArr, r0Gens])
  intro i h1 h2
  have hi : i < 7 := by simpa [r0Gens] using h1
  interval_cases i <;> simp [CFSG.KS.SporSch.M24.gensArr, r0Gens, R0M, a_eq, r_eq, getL_eq, unpackR_eq_unpack]

theorem r0Tree_eq : r0Tree () = bfsTree R0T.N R0T.P R0T.PAR R0T.LAB := by
  rw [r0Tree, r0Gens_eq]
  exact (gtBFS_of_K kR0'.1).1

theorem r0Set_contains {x : Nat} (h : inR0 x = true) : (r0Set ()).contains (unpackR 24 x) = true := by
  obtain ⟨hw, hP⟩ := bfsMemK_sound h
  rw [r0Set, Std.HashSet.contains_ofList, List.contains_iff_mem, Array.mem_toList_iff, r0Tree_eq]
  simp only [bfsTree, Array.mem_ofFn]
  exact ⟨⟨_, hw⟩, by rw [hP, unpackR_eq_unpack]⟩

theorem r0Set_not {x : Nat} (h : ∀ i < 128, notB (eqK x (R0T.P i)) = true) :
    (r0Set ()).contains (unpackR 24 x) = false := by
  rw [Bool.eq_false_iff]
  intro hc
  rw [r0Set, Std.HashSet.contains_ofList, List.contains_iff_mem, Array.mem_toList_iff, r0Tree_eq]
    at hc
  simp only [bfsTree, Array.mem_ofFn] at hc
  obtain ⟨⟨i, hi⟩, he⟩ := hc
  have hi' : i < 128 := kR0'.2 ▸ hi
  have h1 := not_of_notB' (h i hi')
  rw [← beq_unpack] at h1
  rw [← unpackR_eq_unpack] at he
  dsimp only at he
  rw [← he] at h1
  exact absurd h1 (by simp)

theorem twoAQ_toList : CFSG.Sporadic.Co1Block.twoAQTree.pts.toList = QL.map (unpackR 24) := by
  have hT : CFSG.Sporadic.Co1Block.twoAQTree = CFSG.Sporadic.Co1Block.gtOfMasks
      CFSG.Sporadic.Co1Block.twoAQRows.toArray (treeArr (recsT CFSG.Sporadic.Co1Block.twoAQMasks)) := by
    rw [CFSG.Sporadic.Co1Block.twoAQTree, treeOfMasks_eq]
    rfl
  obtain ⟨hs, hg⟩ := gtOfMasks_get (fun l hl => twoAQ_get hl) treeAQ_ok
  have hl := walk_length treeAQ_ok
  rw [hT]
  exact toList_eq_map (L := QL) (by rw [hs]; exact hl.symm)
    (fun j hj => by rw [hg j (by rw [← hl]; exact hj)]; rfl)

theorem cR_eq (i j : Fin 6) : (if cR i j = 1 then unpackR 24 AL else one) =
    unpackR 24 (Bool.rec (motive := fun _ => Nat) oneK AL (Nat.beq (cRN i.val j.val) 1)) := by
  have hc : ∀ i j : Fin 6, (cR i j = 1) ↔ (Nat.beq (cRN i.val j.val) 1 = true) := by decide
  rw [one_eq]
  by_cases h : cR i j = 1
  · rw [if_pos h, (hc i j).1 h]
  · rw [if_neg h, Bool.eq_false_iff.2 (fun h' => h ((hc i j).2 h'))]

theorem c_r0 : chkR0 () = true := by
  have hgt := gtBFS_of_K kR0'.1
  unfold chkR0
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [r0Tree, r0Gens_eq, hgt.1]
    exact hgt.2
  · rw [r0Tree_eq, beq_iff_eq]
    simp [bfsTree, kR0'.2]
  · rw [List.all_eq_true]
    intro i hi
    have h := andB_parts (allN_true' kRi i (List.mem_range.1 hi))
    have h' := andB_parts h.1
    rw [r_eq, d_eq, commR_of h'.1, qPts_contains, h'.2, CFSG.KC.F2W.mul_unpackW, one_eq,
      beq_unpack]
    exact h.2
  · rw [← Array.all_toList, twoAQ_toList, List.all_map, List.all_eq_true]
    intro x hx
    simp only [Function.comp_apply, d_eq]
    by_cases hc : commK x DK = true
    · rw [r0Set_contains (impAllK_sound kQ x hx hc), Bool.or_true]
    · have : commR (unpackR 24 x) (unpackR 24 DK) = false := by
        unfold commR
        rw [CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, beq_unpack]
        exact Bool.eq_false_iff.2 hc
      rw [this]
      rfl
  · rw [List.all_eq_true]
    intro i _
    rw [List.all_eq_true]
    intro j _
    rw [r_eq, r_eq, a_eq, cR_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW,
      CFSG.KC.F2W.mul_unpackW, beq_unpack]
    exact allN_true' (allN_true' kCR i.val i.isLt) j.val j.isLt

theorem c_k : chkK () = true := by
  have h := kK
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have i1 : inv (unpackR 24 K1K) = unpackR 24 K1I := inv_sound' h5
  have i2 : inv (unpackR 24 K2K) = unpackR 24 K2I := inv_sound' h6
  have m1 : (mul (unpackR 24 K1K) (unpackR 24 K1I) == one) = true := by
    rw [mul_unpack, one_eq, beq_unpack]
    exact (andB_parts h5).2
  have m2 : (mul (unpackR 24 K2K) (unpackR 24 K2I) == one) = true := by
    rw [mul_unpack, one_eq, beq_unpack]
    exact (andB_parts h6).2
  have hrel : (CFSG.HardMathSupport.Dickson.I271.U42Presentation.u42Words.all fun w =>
      CFSG.Sporadic.Co1.InvNative.validRows (relRows (unpackR 24 K1K) (unpackR 24 K2K)
        (unpackR 24 K1I) (unpackR 24 K2I) w) &&
      (r0Set ()).contains (relRows (unpackR 24 K1K) (unpackR 24 K2K) (unpackR 24 K1I)
        (unpackR 24 K2I) w)) = true := by
    rw [List.all_eq_true]
    intro w hw
    rw [relK_sound, validRows_unpackR, r0Set_contains (List.all_eq_true.1 kRel w hw)]
    rfl
  have hn : (r0Set ()).contains (unpackR 24 K1K) = false := r0Set_not (allN_true' kK1)
  unfold chkK
  rw [k1_eq, k2_eq, d_eq, a_eq, i1, i2, commR_of h1, commR_of h2, commR_of h3, commR_of h4, hrel,
    hn, m1, m2]
  rfl

theorem c_e : chkE () = true := by
  have h := kE
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold chkE
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro i hi
    have hh := andB_parts (allN_true' h1 i (List.mem_range.1 hi))
    have hh' := andB_parts hh.1
    rw [e_eq, d_eq, a_eq, pow_one_of hh'.1, commR_of hh'.2, commR_of hh.2]
    rfl
  · rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro j hj
    rw [e_eq, e_eq]
    exact commR_of (allN_true' (allN_true' h2 i (List.mem_range.1 hi)) j (List.mem_range.1 hj))
  · rw [List.all_eq_true]
    intro n hn
    have hh := allN_true' kE81 n (List.mem_range.1 hn)
    rw [d_eq, e_eq, e_eq, e_eq, CFSG.KC.Co1BSpin.pow_unpack', CFSG.KC.Co1BSpin.pow_unpack',
      CFSG.KC.Co1BSpin.pow_unpack', CFSG.KC.Co1BSpin.pow_unpack', CFSG.KC.F2W.mul_unpackW,
      CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, one_eq, bne, beq_unpack]
    by_cases h0 : n = 0
    · subst h0
      rfl
    · have hb : Nat.beq n 0 = false := by
        cases n with
        | zero => exact absurd rfl h0
        | succ n => rfl
      rw [hb] at hh
      have hb' : (n == 0) = false := _root_.beq_false_of_ne h0
      rw [hb']
      change (!eqK (prodE n) oneK) = true
      rw [not_of_notB' hh]
      rfl

open Certificates in
theorem c810305 : CFSG.Sporadic.Co1I301.Native.co1RowCheck () = true := by
  unfold co1RowCheck
  rw [c_dag, c_d, c_roots, c_orbit, c_r0, c_k, c_e]
  rfl

end CertificateChecks.KernelCo1I301

end
