module

public import Certificates.Kernel.Co1FiveK.Chk
public import CFSG.Certificates.Kernel.Co1FiveKSound
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.Certificates.Kernel.Co1PSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveK

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1FiveK Timmesfeld.Co1Five
  CFSG.Sporadic.Co1Schreier.Native
open CFSG.KC.Co1B (mulWK)

@[expose] noncomputable def rs : List Rows := (List.range 137).map fun i => unpack 24 24 (D.M i)

theorem base_eq : [CFSG.Sporadic.Co1.Native.co1Data.rowsA, CFSG.Sporadic.Co1.Native.co1Data.rowsB] =
    (List.range 2).map fun i => unpack 24 24 (D.M i) := by
  have h := kBase
  simp only [Bool.and_eq_true] at h
  have hA : CFSG.Sporadic.Co1.Native.co1Data.rowsA = unpack 24 24 (D.M 0) := by
    rw [Nat.eq_of_beq_eq_true h.1]
    exact CertificateChecks.KernelSporSch.Co1Packed.aR_u
  have hB : CFSG.Sporadic.Co1.Native.co1Data.rowsB = unpack 24 24 (D.M 1) := by
    rw [Nat.eq_of_beq_eq_true h.2]
    exact CertificateChecks.KernelSporSch.Co1Packed.bR_u
  rw [hA, hB]
  rfl

theorem gDag_eq : gDag CFSG.Sporadic.Co1.Native.co1Data.rowsA CFSG.Sporadic.Co1.Native.co1Data.rowsB =
    (rs, (List.range 137).map fun i => unpack 24 24 (D.MI i), true) := by
  unfold gDag
  exact dagWK_sound base_eq kD

theorem rowAt_rs {k : Nat} (hk : k < 137) : rowAt rs k = unpack 24 24 (D.M k) := by
  unfold rowAt rs
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem inv_rs {k : Nat} (hk : k < 137) :
    mul (rowAt rs k) (inv (rowAt rs k)) = one () ∧ inv (rowAt rs k) = unpack 24 24 (D.MI k) := by
  obtain ⟨h1, h2⟩ := invOKW_sound (dagWK_inv kD k hk)
  rewrite [rowAt_rs hk, h2]
  exact ⟨h1, rfl⟩

theorem idxD_get {i : Nat} (hi : i < 3) : idxD.getD i 0 = 70 + i := by
  interval_cases i <;> with_unfolding_all rfl

theorem idxR_get {j : Nat} (hj : j < 20) : idxR.getD j 0 = 73 + j := by
  interval_cases j <;> with_unfolding_all rfl

theorem idxC_get {j : Nat} (hj : j < 20) : idxC.getD j 0 = 93 + j := by
  interval_cases j <;> with_unfolding_all rfl

theorem dK_rs {i : Nat} (hi : i < 3) : rowAt rs (idxD.getD i 0) = unpack 24 24 (DK i) := by
  rw [idxD_get hi, rowAt_rs (by omega)]
  rfl

theorem a0Row_rs (k : Nat) : a0Row rs k = unpack 24 24 (a0K DK k) :=
  a0Row_eq (fun _ hi => dK_rs hi) k

theorem toArray_gensArr {n : Nat} {GM : Nat → Nat} :
    ((List.range n).map fun i => unpack 24 24 (GM i)).toArray = gensArr n GM := by
  apply Array.ext
  · simp [gensArr]
  · intro i h1 h2
    simp [gensArr]

theorem qGens_eq : (qGens rs).toArray = gensArr 3 QM := by
  rw [← toArray_gensArr]
  have e : idxQ = [67, 68, 69] := by with_unfolding_all rfl
  unfold qGens
  rw [e]
  simp only [List.map_cons, List.map_nil, rowAt_rs (by norm_num : 67 < 137),
    rowAt_rs (by norm_num : 68 < 137), rowAt_rs (by norm_num : 69 < 137)]
  rfl

theorem qTree_eq : qTree rs = bfsTree QT.N QT.P QT.PAR QT.LAB ∧
    CFSG.Sporadic.Co1.TwoBNative.gtOK (qGens rs).toArray (qTree rs) = true := by
  obtain ⟨hT, hok⟩ := gtBFS_of_K kQ
  have e : qTree rs = bfsTree QT.N QT.P QT.PAR QT.LAB := by
    unfold qTree
    rewrite [qGens_eq]
    exact hT
  refine ⟨e, ?_⟩
  rewrite [e, qGens_eq]
  exact hok

theorem qN : QT.N = 625 := Nat.eq_of_beq_eq_true kQN

theorem AT_a0K {k : Nat} (hk : k < 125) : AT k = a0K DK k := by
  have h : Nat.beq (AT k) (a0K DK k) = true := MatL.allN_iff.1 kAT k hk
  exact Nat.eq_of_beq_eq_true h

theorem pw5 {i : Nat} (hi : i < 625) : pwK (QT.P i) 5 = idM := by
  have h : Nat.beq (pwK (QT.P i) 5) idM = true := MatL.allN_iff.1 kQ5 i hi
  exact Nat.eq_of_beq_eq_true h

theorem pts_qTree {i : Nat} (hi : i < QT.N) :
    (qTree rs).pts[i]! = unpack 24 24 (QT.P i) := by
  rw [qTree_eq.1, getElem!_pos _ i (by simp [bfsTree, hi])]
  simp [bfsTree]

theorem size_qTree : (qTree rs).pts.size = QT.N := by
  rw [qTree_eq.1]
  simp [bfsTree]

theorem beq_unpack_self (X Y : Nat) (h : X = Y) : (unpack 24 24 X == unpack 24 24 Y) = true := by
  rw [h]
  exact beq_self_eq_true _

theorem qOK_true : qOK rs = true := by
  unfold qOK
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨⟨qTree_eq.2, by rewrite [size_qTree, qN]; rfl⟩, fun i hi => ?_⟩
  rewrite [size_qTree] at hi
  rewrite [← getElem!_pos, pts_qTree hi, pow_unpack, ← MatL.unpack_idM, pw5 (qN ▸ hi)]
  rfl

theorem a0OK_true : a0OK rs = true := by
  unfold a0OK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun i hi => ?_, ?_⟩
  · have h := MatL.allN_iff.1 kA0 i hi
    simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h5, hc⟩ := h
    rewrite [dK_rs hi]
    refine ⟨⟨CFSG.KC.Co1End.validRows_unpack _, ?_⟩, fun j hj => ?_⟩
    · rewrite [pow_unpack, ← MatL.unpack_idM]
      exact beq_unpack_self _ _ (Nat.eq_of_beq_eq_true h5)
    · have hj' : Nat.beq (mulWK (DK i) (DK j)) (mulWK (DK j) (DK i)) = true :=
        MatL.allN_iff.1 hc j hj
      rewrite [dK_rs hj, mul_unpackW, mul_unpackW]
      exact beq_unpack_self _ _ (Nat.eq_of_beq_eq_true hj')
  · apply CFSG.KC.Co1P.distinctKeys_of_nodup
    rw [List.nodup_iff_injective_get]
    intro a b e
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at e
    have ha : (a : Nat) < 125 := by simpa using a.2
    have hb : (b : Nat) < 125 := by simpa using b.2
    have hAT : ∀ k < 125, a0Row rs k = unpack 24 24 (AT k) := fun k hk => by
      rewrite [a0Row_rs, AT_a0K hk]
      rfl
    rewrite [hAT _ ha, hAT _ hb] at e
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have hd : (!CFSG.KC.Co1End.eqK (AT b) (AT a)) = true :=
        MatL.allN_iff.1 (MatL.allN_iff.1 kATd b hb) a h
      exact ne_of_eqK (by simpa using hd) e.symm
    · have hd : (!CFSG.KC.Co1End.eqK (AT a) (AT b)) = true :=
        MatL.allN_iff.1 (MatL.allN_iff.1 kATd a ha) b h
      exact ne_of_eqK (by simpa using hd) e

end CertificateChecks.KernelCo1FiveK

end
