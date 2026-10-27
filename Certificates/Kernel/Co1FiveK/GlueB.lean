module

public import Certificates.Kernel.Co1FiveK.Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveK

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1FiveK Timmesfeld.Co1Five
  CFSG.Sporadic.Co1Schreier.Native
open CFSG.KC.Co1B (mulWK)
open CFSG.KC.Co1F2 (getL)

theorem bIf_split {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c
  · exact ⟨fun h' => absurd h' (by simp), fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => absurd h' (by simp)⟩

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem blt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem AT_eq {k : Nat} (hk : k < 125) : a0Row rs k = unpack 24 24 (AT k) := by
  rewrite [a0Row_rs, AT_a0K hk]
  rfl

theorem mem_a0 {k : Nat} (hk : k < 125) :
    unpack 24 24 (AT k) ∈ (List.range 125).map (a0Row rs) :=
  List.mem_map.2 ⟨k, List.mem_range.2 hk, AT_eq hk⟩

theorem pt_mem {y : Nat} (hy : y < QT.N) :
    unpack 24 24 (QT.P y) ∈ (qTree rs).pts.toList := by
  rewrite [qTree_eq.1]
  simp only [bfsTree, Array.toList_ofFn, List.mem_ofFn]
  exact ⟨⟨y, hy⟩, rfl⟩

theorem fusOK_true : fusOK rs = true := by
  unfold fusOK
  simp only [Std.HashSet.contains_ofList, List.contains_iff_mem, Bool.and_eq_true,
    Array.all_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · have hi' : i < QT.N := size_qTree ▸ hi
    have hq : (qTree rs).pts[i] = unpack 24 24 (QT.P i) := by
      rewrite [← getElem!_pos]
      exact pts_qTree hi'
    rewrite [hq]
    have h := MatL.allN_iff.1 kFus i (qN ▸ hi')
    rewrite [MatL.strictB_eq] at h
    generalize getL 0 FW.W i = c at h
    obtain ⟨hlo, hhi⟩ := bIf_split h
    by_cases hc : c < 125
    · left
      rewrite [Nat.eq_of_beq_eq_true (hlo (blt_of_lt hc))]
      exact mem_a0 hc
    · right
      have h2 := hhi (Bool.eq_false_iff.2 fun h' => hc (lt_of_blt h'))
      rewrite [MatL.strictB_eq, MatL.strictB_eq] at h2
      obtain ⟨hy, he⟩ := MatS.bAnd_split h2
      have hy' : (c - 125) / 20 < QT.N := qN ▸ lt_of_blt hy
      have hj : (c - 125) % 20 < 20 := Nat.mod_lt _ (by norm_num)
      rewrite [List.mem_flatMap]
      refine ⟨(c - 125) % 20, List.mem_range.2 hj, ?_⟩
      unfold conjList
      refine List.mem_map.2 ⟨_, pt_mem hy', ?_⟩
      have he' : QT.P i = mulWK (mulWK (QT.P ((c - 125) / 20)) (D.M (73 + (c - 125) % 20)))
          (pwK (QT.P ((c - 125) / 20)) 4) := Nat.eq_of_beq_eq_true he
      rewrite [idxR_get hj, rowAt_rs (by omega), pow_unpack, mul_unpackW, mul_unpackW, ← he']
      rfl
  · have hC := MatL.allN_iff.1 kConj j hj
    rewrite [MatL.strictB_eq] at hC
    obtain ⟨hk, he⟩ := MatS.bAnd_split hC
    obtain ⟨hm, hi⟩ := inv_rs (k := idxC.getD j 0) (by rewrite [idxC_get hj]; omega)
    refine ⟨by rewrite [hm]; exact beq_self_eq_true _, ?_⟩
    rewrite [hi, idxC_get hj, rowAt_rs (by omega), idxR_get hj, rowAt_rs (by omega), mul_unpackW,
      mul_unpackW]
    have e : mulWK (mulWK (D.M (93 + j)) (D.M (73 + j))) (D.MI (93 + j)) = AT (getL 0 FW.C j) :=
      Nat.eq_of_beq_eq_true he
    rewrite [e]
    exact mem_a0 (lt_of_blt hk)

theorem plane_gens (τ : Nat) :
    [a0Row rs (repA.getD τ 0), a0Row rs (repB.getD τ 0)].toArray = gensArr 2 (PG τ) := by
  rewrite [← toArray_gensArr, a0Row_rs, a0Row_rs]
  rfl

theorem plane_tree {τ : Nat} {N : Nat} {P PAR LAB W S : Nat → Nat}
    (hN : Nat.beq N 25 = true) (hK : gtPinK (PG τ) 2 100000 N P PAR LAB W S = true) :
    (let G := [a0Row rs (repA.getD τ 0), a0Row rs (repB.getD τ 0)].toArray
     CFSG.Sporadic.Co1.TwoBNative.gtOK G (CFSG.Sporadic.Co1.TwoBNative.gtBFS G 100000) &&
       (CFSG.Sporadic.Co1.TwoBNative.gtBFS G 100000).pts.size == 25) = true := by
  obtain ⟨hT, hok⟩ := gtBFS_of_K hK
  dsimp only
  rewrite [plane_gens, hT, hok, Bool.true_and, beq_iff_eq, ← Nat.eq_of_beq_eq_true hN]
  simp [bfsTree]

theorem planeOK_true : planeOK rs = true := by
  unfold planeOK
  rewrite [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, kCov⟩, ?_⟩
  · rewrite [List.all_eq_true]
    intro p hp
    rewrite [List.mem_range] at hp
    obtain ⟨hn, hc⟩ := MatS.bAnd_split (MatL.allN_iff.1 kPl p hp)
    unfold conjP at hc
    rewrite [MatL.strictB_eq] at hc
    obtain ⟨hlt, hc⟩ := MatS.bAnd_split hc
    obtain ⟨hα, hβ⟩ := MatS.bAnd_split hc
    have hpc : idxPC.getD p 0 < 137 := lt_of_blt hlt
    obtain ⟨hm, hi⟩ := inv_rs hpc
    dsimp only
    simp only [Bool.and_eq_true]
    simp only [numP, Bool.and_eq_true] at hn
    refine ⟨⟨⟨hn, by rewrite [hm]; exact beq_self_eq_true _⟩, ?_⟩, ?_⟩
    · rewrite [hi, rowAt_rs hpc, a0Row_rs, a0Row_rs, mul_unpackW, mul_unpackW]
      exact beq_unpack_self _ _ (Nat.eq_of_beq_eq_true hα)
    · rewrite [hi, rowAt_rs hpc, a0Row_rs, a0Row_rs, mul_unpackW, mul_unpackW]
      exact beq_unpack_self _ _ (Nat.eq_of_beq_eq_true hβ)
  · rewrite [List.all_eq_true]
    intro τ hτ
    rewrite [List.mem_range] at hτ
    have hr := List.all_eq_true.1 kRep τ (List.mem_range.2 hτ)
    simp only [Bool.and_eq_true] at hr
    dsimp only
    rewrite [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨hr, ?_⟩
    have hN := kPTN
    simp only [Bool.and_eq_true] at hN
    interval_cases τ
    · exact plane_tree hN.1.1 kPT0
    · exact plane_tree hN.1.2 kPT1
    · exact plane_tree hN.2 kPT2

theorem globalOK_eq_true :
    globalOK CFSG.Sporadic.Co1.Native.co1Data.rowsA CFSG.Sporadic.Co1.Native.co1Data.rowsB = true := by
  unfold globalOK
  dsimp only
  rewrite [gDag_eq]
  dsimp only
  rewrite [qOK_true, a0OK_true, fusOK_true, planeOK_true]
  rfl

end CertificateChecks.KernelCo1FiveK

end
