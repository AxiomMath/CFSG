
module

public import Certificates.Kernel.Co1B.PrimM2045
public import Certificates.Kernel.Co1B.PrimT2045
public import Certificates.Kernel.Co1B.Tri2045Base
public import CFSG.Certificates.Kernel.MergeGSound
public import CFSG.Certificates.Kernel.Spor.CBfsKSound
public import CFSG.Certificates.Kernel.Spor.CBLevelSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Prim2045

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.ONSchreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
  CFSG.KS.CB CFSG.KC.MergeR CFSG.KC.MergeG CFSG.Monster.B.Co2
  CertificateChecks.KernelCo1B.Tri2045

theorem ext_size : (twoBStrong.extract 0 2).size = 2 := by
  simp [strong_facts.1]

theorem hG : (twoBStrong.extract 0 2).size = 2 ∧
    ∀ i < 2, (twoBStrong.extract 0 2)[i]! = unpack 1365 11 (RO.S i) := by
  refine ⟨ext_size, fun i hi => ?_⟩
  rw [getElem!_pos _ i (by rw [ext_size]; exact hi),
    ← strong_facts.2 i (by omega), getElem!_pos twoBStrong i (by rw [strong_facts.1]; omega)]
  simp

theorem hGp : ∀ i < 2, ∀ y < 1365, ((twoBStrong.extract 0 2)[i]!)[y]! = pg 11 2047 (RO.S i) y := by
  intro i hi y hy
  rw [hG.2 i hi, unpack_get' hy]
  rfl

theorem mergeCKG_of {n w kG b x Lc S NS TP PP : Nat} {GS RI RU RV A : Nat → Nat}
    (h0 : bAnd(Nat.blt b n, bAnd(Nat.blt x n, bAnd(Nat.blt Lc 4096, bAnd(Nat.blt 0 S,
      Nat.ble Lc (Nat.mul S NS))))) = true)
    (hA : allN n (fun y => Nat.beq (pgW w (A 0) y) (nIf(Nat.beq y x, b, y))) = true)
    (hs : ∀ s < NS, segCG n w kG GS Lc S TP PP A RI RU RV s = true)
    (hT : allN n (fun l => Nat.ble (pgW 12 TP l) Lc) = true)
    (hc : Nat.beq (mergeCnt n w GS Lc S TP PP A RI RU RV) (timedCnt n Lc TP) = true)
    (hf : finalC n w Lc NS TP A = true) :
    mergeCKG n w kG GS b x Lc S NS RI RU RV TP PP A = true := by
  obtain ⟨e1, r1⟩ := CFSG.KC.Pack.band_iff.1 h0
  obtain ⟨e2, r2⟩ := CFSG.KC.Pack.band_iff.1 r1
  obtain ⟨e3, r3⟩ := CFSG.KC.Pack.band_iff.1 r2
  obtain ⟨e4, e5⟩ := CFSG.KC.Pack.band_iff.1 r3
  unfold mergeCKG
  rw [e1, e2, e3, e4, e5, hA, CFSG.KS.PackFld.allN_of_forall hs, hT, hc, hf]

theorem merge_of {l x : Nat} {A : Nat → Nat}
    (hS : searchK 1365 11 2047 15015 2 RO.S 0 x (PD.CNT l) (PD.LP l) = true)
    (hM : mergeCKG 1365 11 2 RO.S 0 x (PD.CNT l) 32 43 (rI l) (rU l) (rV l) (PD.TP l) (PD.PP l)
      A = true) :
    mergeOK 1365 (twoBStrong.extract 0 2) 0 x (mergeSearch 1365 (twoBStrong.extract 0 2) 0 x) =
      true := by
  rw [mergeSearch_eq_of_searchK ext_size hGp hS]
  exact mergeCKG_sound (by norm_num) hG kCan rfl hM

theorem merge0 : mergeOK 1365 (twoBStrong.extract 0 2) 0 1
    (mergeSearch 1365 (twoBStrong.extract 0 2) 0 1) = true :=
  merge_of kS0 (mergeCKG_of kH0 kA0 M0.all kT0 kC0 kF0)

theorem merge1 : mergeOK 1365 (twoBStrong.extract 0 2) 0 5
    (mergeSearch 1365 (twoBStrong.extract 0 2) 0 5) = true :=
  merge_of kS1 (mergeCKG_of kH1 kA1 M1.all kT1 kC1 kF1)

theorem merge2 : mergeOK 1365 (twoBStrong.extract 0 2) 0 83
    (mergeSearch 1365 (twoBStrong.extract 0 2) 0 83) = true :=
  merge_of kS2 (mergeCKG_of kH2 kA2 M2.all kT2 kC2 kF2)

theorem strong0 {j : Nat} (hj : j < 6) : (twoBStrong[j]!)[0]! = pg 11 (mask 11) (RO.S j) 0 := by
  rw [strong_facts.2 j hj, unpack_get' (by norm_num)]

theorem fix_iff {j : Nat} (hj : j < 6) :
    fixesFirst twoBChainBase.toArray twoBStrong[j]! 1 = decide (2 ≤ j) := by
  have h := CFSG.KC.Pack.allN_spec kFix j hj
  have e : fixesFirst twoBChainBase.toArray twoBStrong[j]! 1 = ((twoBStrong[j]!)[0]! == 0) := by
    simp [fixesFirst, allLt, twoBChainBase]
  rw [e, strong0 hj]
  by_cases h2 : 2 ≤ j
  · have e2 : Nat.ble 2 j = true := by rwa [Nat.ble_eq]
    rw [e2] at h
    simp [h2, Nat.eq_of_beq_eq_true h]
  · have e2 : Nat.ble 2 j = false := by
      cases e3 : Nat.ble 2 j
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true e3) h2
    rw [e2] at h
    have h3 : Nat.beq (pg 11 (mask 11) (RO.S j) 0) 0 = false := by
      cases e3 : Nat.beq (pg 11 (mask 11) (RO.S j) 0) 0
      · rfl
      · rw [e3] at h
        exact absurd h (by decide)
    have h4 : pg 11 (mask 11) (RO.S j) 0 ≠ 0 := fun h5 => by
      rw [h5] at h3
      exact absurd h3 (by decide)
    simp [h2, h4]

theorem level_eq : levelIdx twoBStrong twoBChainBase.toArray 1 = [2, 3, 4, 5] := by
  unfold levelIdx
  rw [strong_facts.1, List.filter_congr fun j hj => fix_iff (List.mem_range.1 hj)]
  decide

theorem steps_eq : twoBHSteps = #[twoBStrong[2]!, twoBStrong[3]!, twoBStrong[4]!, twoBStrong[5]!] := by
  unfold twoBHSteps
  rw [level_eq]
  rfl

theorem hst : twoBHSteps.size = 4 ∧ ∀ j < 4, ∀ x < 1365, (twoBHSteps[j]!)[x]! = stp j x := by
  rw [steps_eq]
  refine ⟨rfl, fun j hj x hx => ?_⟩
  have e : ∀ (S : Array (Array Nat)), ∀ j < 4, (#[S[2]!, S[3]!, S[4]!, S[5]!])[j]! = S[j + 2]! := by
    intro S j hj
    interval_cases j <;> rfl
  rw [e twoBStrong j hj, strong_facts.2 (j + 2) (by omega), unpack_get' hx]
  rfl

theorem trees_eq : twoBHTrees = [cbfs 1365 0 twoBHSteps, cbfs 1365 1 twoBHSteps,
    cbfs 1365 5 twoBHSteps, cbfs 1365 83 twoBHSteps] := rfl

@[expose] noncomputable def recT (t : Nat) : CLevel :=
  ⟨Array.ofFn (n := PD.M t) fun k => tPts t k.val, Array.ofFn (n := 1365) fun z => tPos t z.val,
    Array.ofFn (n := PD.M t) fun k => tPar t k.val, Array.ofFn (n := PD.M t) fun k => tLab t k.val⟩

theorem pts_of {t NS : Nat} (hm : PD.M t ≤ NS * 128) (h : ∀ s < NS, ptS t s = true) :
    ∀ k < PD.M t, cbPt 1365 (PD.M t) 4 stp (tPts t) (tPos t) (tPar t) (tLab t) k = true :=
  cbPt_of_range (by norm_num) hm h

theorem pos_of {t : Nat} (ht : t < 4) :
    ∀ z < 1365, cbPos 1365 (PD.M t) (tPts t) (tPos t) z = true :=
  CFSG.KC.Pack.allN_spec (PS.all t ht)

theorem tree_of {t root NS : Nat} (ht : t < 4)
    (hh : cbHead 1365 (PD.M t) root (tPts t) (tPar t) (tLab t) = true)
    (hm : PD.M t ≤ NS * 128) (h : ∀ s < NS, ptS t s = true) :
    cbfs 1365 root twoBHSteps = recT t ∧ clevelOK 1365 root twoBHSteps (recT t) = true :=
  ⟨cbfsK_sound hst hh (pts_of hm h) (pos_of ht), clevelOK_of_cb hst hh (pts_of hm h) (pos_of ht)⟩

theorem tree0 : cbfs 1365 0 twoBHSteps = recT 0 ∧ clevelOK 1365 0 twoBHSteps (recT 0) = true :=
  tree_of (NS := 1) (by norm_num) kHd0 (by have := Nat.eq_of_beq_eq_true kM0; omega) P0.all

theorem tree1 : cbfs 1365 1 twoBHSteps = recT 1 ∧ clevelOK 1365 1 twoBHSteps (recT 1) = true :=
  tree_of (NS := 8) (by norm_num) kHd1 (by have := Nat.eq_of_beq_eq_true kM1; omega) P1.all

theorem tree2 : cbfs 1365 5 twoBHSteps = recT 2 ∧ clevelOK 1365 5 twoBHSteps (recT 2) = true :=
  tree_of (NS := 3) (by norm_num) kHd2 (by have := Nat.eq_of_beq_eq_true kM2; omega) P2.all

theorem tree3 : cbfs 1365 83 twoBHSteps = recT 3 ∧ clevelOK 1365 83 twoBHSteps (recT 3) = true :=
  tree_of (NS := 1) (by norm_num) kHd3 (by have := Nat.eq_of_beq_eq_true kM3; omega) P3.all

theorem tree_eq : twoBHTrees = [recT 0, recT 1, recT 2, recT 3] := by
  rw [trees_eq, tree0.1, tree1.1, tree2.1, tree3.1]

theorem cover : allLt 1365 (fun z => twoBHTrees.any fun L => decide (L.pos[z]! < L.pts.size)) =
    true := by
  rw [tree_eq, allLt_iff]
  intro z hz
  have h := CFSG.KC.Pack.allN_spec kCov z hz
  have hp : ∀ t, (recT t).pos[z]! = tPos t z := fun t => ofFn_get (m := 1365) (tPos t) hz
  have hs : ∀ t, (recT t).pts.size = PD.M t := fun t => Array.size_ofFn
  simp only [List.any_cons, List.any_nil, Bool.or_false, hp, hs, Bool.or_eq_true,
    decide_eq_true_eq]
  obtain ⟨-, h1⟩ := bif_iff.1 h
  by_cases c0 : tPos 0 z < PD.M 0
  · exact Or.inl c0
  · refine Or.inr ?_
    have h1 := h1 (by cases e : Nat.blt (tPos 0 z) (PD.M 0); rfl; exact absurd (lt_of_blt e) c0)
    obtain ⟨-, h2⟩ := bif_iff.1 h1
    by_cases c1 : tPos 1 z < PD.M 1
    · exact Or.inl c1
    · refine Or.inr ?_
      have h2 := h2 (by cases e : Nat.blt (tPos 1 z) (PD.M 1); rfl; exact absurd (lt_of_blt e) c1)
      obtain ⟨-, h3⟩ := bif_iff.1 h2
      by_cases c2 : tPos 2 z < PD.M 2
      · exact Or.inl c2
      · refine Or.inr (lt_of_blt (h3 ?_))
        cases e : Nat.blt (tPos 2 z) (PD.M 2)
        · rfl
        · exact absurd (lt_of_blt e) c2

theorem twoB_prim_check : twoBPrimCheckOf twoBStrong twoBHSteps twoBHTrees twoBSubReps = true := by
  unfold twoBPrimCheckOf
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨by decide, ?_⟩, ?_⟩, ?_⟩, cover⟩
  · rw [List.all_eq_true]
    intro x hx
    have hx' : x = 1 ∨ x = 5 ∨ x = 83 := by simpa [twoBSubReps] using hx
    simp only [Bool.and_eq_true]
    rcases hx' with rfl | rfl | rfl
    · exact ⟨⟨by decide, by decide⟩, merge0⟩
    · exact ⟨⟨by decide, by decide⟩, merge1⟩
    · exact ⟨⟨by decide, by decide⟩, merge2⟩
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 4 := by rwa [hst.1] at hi
    rw [← getElem!_pos twoBHSteps i hi, hst.2 i hi' 0 (by norm_num)]
    have h := CFSG.KC.Pack.allN_spec kFix (i + 2) (by omega)
    have e : Nat.ble 2 (i + 2) = true := by
      rw [Nat.ble_eq]
      omega
    rw [e] at h
    have h' : stp i 0 = 0 := Nat.eq_of_beq_eq_true h
    rw [h']
    rfl
  · rw [tree_eq, List.all_eq_true]
    intro p hp
    have hp' : p = (0, recT 0) ∨ p = (1, recT 1) ∨ p = (5, recT 2) ∨ p = (83, recT 3) := by
      simpa [twoBSubReps] using hp
    rcases hp' with rfl | rfl | rfl | rfl
    · exact tree0.2
    · exact tree1.2
    · exact tree2.2
    · exact tree3.2

end CertificateChecks.KernelCo1B.Prim2045

end
