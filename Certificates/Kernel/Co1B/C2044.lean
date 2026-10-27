module

public import CFSG.Sporadic.Co1Block.TwoACheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoAData
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Kernel.Co1B.Chk2044
public import Certificates.Kernel.Co1B.Iota
public import Certificates.Kernel.Co1B.Fix2041
public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Certificates.Kernel.SporSch.Co1CentSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Certificates.Kernel.Co1FixCount
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C2044

open CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1.InvNative CertificateChecks.KernelSporSch.Co1Packed

theorem iotaA_u : iotaARows = unpack 24 24 IA :=
  CertificateChecks.KernelCo1B.iotaA_eq.trans (unpackR_eq_unpack _)

theorem base_eq : [aR, bR, iotaARows] = (List.range 3).map fun i => unpack 24 24 (D1.M i) := by
  have h := kb
  simp only [Bool.and_eq_true] at h
  have hr : List.range 3 = [0, 1, 2] := rfl
  have ha : PA = CFSG.KD.Co1B.SA := rfl
  have hb : PB = CFSG.KD.Co1B.SB := rfl
  rw [hr, List.map_cons, List.map_cons, List.map_cons, List.map_nil, aR_u, bR_u, iotaA_u,
    Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2, ha, hb]

theorem twoA_cent_check : centCheckOf iotaARows twoAD1 twoABray twoAD2 twoAVBase twoAVGens
    twoAVSizes = true := by
  refine centCheckOf_of_K (P := IA) iotaA_u base_eq kD1 kI kBind kD2 kC ?_ ?_
  · intro i hi
    have : i < 6 := by simpa [twoAVBase] using hi
    interval_cases i <;> decide
  · intro i hi
    have : i < 6 := by simpa [twoAVBase] using hi
    interval_cases i
    · exact ⟨_, _, _, _, _, 512, TW.hd0, TW.hc0, TW.hn0, by decide, TW.hl0, TW.hp0, f0⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd1, TW.hc1, TW.hn1, by decide, TW.hl1, TW.hp1, f1⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd2, TW.hc2, TW.hn2, by decide, TW.hl2, TW.hp2, f2⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd3, TW.hc3, TW.hn3, by decide, TW.hl3, TW.hp3, f3⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd4, TW.hc4, TW.hn4, by decide, TW.hl4, TW.hp4, f4⟩
    · exact ⟨_, _, _, _, _, 512, TW.hd5, TW.hc5, TW.hn5, by decide, TW.hl5, TW.hp5, f5⟩

theorem hN : D2.N = 35 ∧ QT.N = 512 := by
  have h := kN
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem bray_eq : brayElts (brayRows iotaARows twoAD1) twoABray =
    (List.range twoABray.length).map fun i => unpack 24 24 (D2.M i) :=
  brayElts_of_K base_eq kD1 kI kBind

theorem dag₂_eq : dag (brayElts (brayRows iotaARows twoAD1) twoABray) twoAD2 =
    ((List.range D2.N).map fun i => unpack 24 24 (D2.M i),
      (List.range D2.N).map fun i => unpack 24 24 (D2.MI i), true) :=
  dagIK_sound bray_eq kD2

theorem qRows_get {l : Nat} (hl : l < 8) : twoAQRows[l]?.getD #[] = unpack 24 24 (QM l) := by
  rw [CertificateChecks.KernelCo1B.twoAQ_eq, IQK, List.map_map, List.getElem?_map,
    List.getElem?_range hl]
  rw [Option.map_some, Option.getD_some, Function.comp_apply, unpackR_eq_unpack]
  rfl

theorem qRows_len : twoAQRows.length = 8 := by
  rw [CertificateChecks.KernelCo1B.twoAQ_eq, IQK]
  simp

theorem qArr_eq : twoAQRows.toArray = gensArr 8 QM := by
  apply Array.ext (by simp [gensArr, qRows_len])
  intro i h₁ h₂
  have hi : i < 8 := by simpa [qRows_len] using h₁
  have h := qRows_get hi
  rw [List.getElem?_eq_getElem (by simpa using h₁), Option.getD_some] at h
  simp only [List.getElem_toArray, gensArr, Array.getElem_ofFn]
  exact h

theorem gt_eq : gtBFS twoAQRows.toArray 512 = bfsTree QT.N QT.P QT.PAR QT.LAB := by
  rw [qArr_eq]
  exact (gtBFS_of_K kQ).1

theorem mem_of_K {K : Nat} (h : bfsMemK QT.P QT.S QT.N K = true) :
    (bfsTree QT.N QT.P QT.PAR QT.LAB).pts.contains (unpack 24 24 K) = true := by
  obtain ⟨hw, hK⟩ := bfsMemK_sound h
  exact contains_bfsTree hw (by rw [hK])

theorem roots_get {i : Nat} (hi : i < 8) :
    bfsPosK QT.P QT.S QT.N (rowsKey (twoARoots.getD i #[])) < QT.N ∧
      unpack 24 24 (RK i) = twoARoots.getD i #[] := by
  have h := MatL.allN_iff.1 kR i hi
  rw [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
  exact h

theorem roots_len : twoARoots.length = 8 := rfl

theorem root_getD {i : Nat} (hi : i < 8) : twoARoots.getD i (one ()) = unpack 24 24 (RK i) := by
  rw [(roots_get hi).2, List.getD_eq_getElem _ _ (by rw [roots_len]; exact hi),
    List.getD_eq_getElem _ _ (by rw [roots_len]; exact hi)]

@[expose] noncomputable def SL : List Rows := (List.range D2.N).map fun i => unpack 24 24 (D2.M i)

theorem SL_len : SL.length = 35 := by rw [SL, List.length_map, List.length_range, hN.1]

theorem SL_get {j : Nat} (hj : j < 35) : SL.getD j (one ()) = unpack 24 24 (D2.M j) := by
  rw [SL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by rw [hN.1]; exact hj)]
  rfl

theorem inv_of {X Y : Nat} (h : invOKK X Y = true) :
    mul (unpack 24 24 X) (unpack 24 24 Y) = one () ∧ inv (unpack 24 24 X) = unpack 24 24 Y :=
  invOKK_sound h

theorem level_ok {i : Nat} (hi : i < 8) {P PAR LAB W S : Nat → Nat} {N : Nat}
    (h : levelK i P PAR LAB W S N = true) :
    conjLevelOK SL twoARoots twoACGens twoACSizes i = true := by
  unfold levelK at h
  rw [MatL.bAnd_eq, MatL.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, MatL.allN_iff] at h
  obtain ⟨hjs, hgen, hct⟩ := h
  have hjlt : ∀ l (hl : l < (twoACGens.getD i []).length), (twoACGens.getD i [])[l] < 35 :=
    fun l hl => by simpa using List.all_eq_true.1 hjs _ (List.getElem_mem hl)
  have hGM : ∀ l (hl : l < (twoACGens.getD i []).length),
      GM i l = D2.M (twoACGens.getD i [])[l] ∧ GIM i l = D2.MI (twoACGens.getD i [])[l] := by
    intro l hl
    simp only [GM, GIM, List.getD_eq_getElem _ _ hl, and_self]
  have hgen' : ∀ l < (twoACGens.getD i []).length, (mul (unpack 24 24 (GM i l))
      (unpack 24 24 (GIM i l)) = one () ∧ inv (unpack 24 24 (GM i l)) = unpack 24 24 (GIM i l)) ∧
      ∀ k < i, CFSG.KC.Co1B.mulWK (GM i l) (RK k) = CFSG.KC.Co1B.mulWK (RK k) (GM i l) := by
    intro l hl
    have h1 := hgen l hl
    rw [MatL.bAnd_eq, Bool.and_eq_true, MatL.allN_iff] at h1
    exact ⟨inv_of h1.1, fun k hk => Nat.eq_of_beq_eq_true (h1.2 k hk)⟩
  have hG : ((twoACGens.getD i []).map fun j => SL.getD j (one ())).toArray =
      gensArr (twoACGens.getD i []).length (GM i) := by
    apply Array.ext (by simp [gensArr])
    intro l h₁ h₂
    have hl : l < (twoACGens.getD i []).length := by simpa using h₁
    simp only [List.getElem_toArray, List.getElem_map, gensArr, Array.getElem_ofFn]
    rw [SL_get (hjlt l hl), (hGM l hl).1]
  have hGi : (gensArr (twoACGens.getD i []).length (GM i)).map inv =
      gensArr (twoACGens.getD i []).length (GIM i) := by
    apply Array.ext (by simp [gensArr])
    intro l h₁ h₂
    have hl : l < (twoACGens.getD i []).length := by simpa [gensArr] using h₁
    simp only [Array.getElem_map, gensArr, Array.getElem_ofFn]
    exact (hgen' l hl).1.2
  unfold conjLevelOK
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range, beq_iff_eq]
  rw [hG, hGi, root_getD hi]
  refine ⟨⟨?_, ?_⟩, conjAtLeast_of_K hct⟩
  · intro j hj
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hj
    refine ⟨by rw [SL_len]; exact hjlt l hl, fun k hk => ?_⟩
    rw [SL_get (hjlt l hl), root_getD (by omega), ← (hGM l hl).1, mul_unpackW, mul_unpackW,
      (hgen' l hl).2 k hk]
  · intro l hl
    have hl' : l < (twoACGens.getD i []).length := by simpa [gensArr] using hl
    rw [getElem!_pos _ l (by simpa [gensArr] using hl), getElem!_pos _ l (by simpa [gensArr] using hl)]
    simp only [gensArr, Array.getElem_ofFn]
    exact (hgen' l hl').1.1

theorem levels_ok : (List.range twoARoots.length).all (conjLevelOK SL twoARoots twoACGens twoACSizes) =
    true := by
  rw [List.all_eq_true]
  intro i hi
  have hi8 : i < 8 := by simpa [roots_len] using hi
  interval_cases i
  exacts [level_ok (by decide) kL0, level_ok (by decide) kL1, level_ok (by decide) kL2,
    level_ok (by decide) kL3, level_ok (by decide) kL4, level_ok (by decide) kL5,
    level_ok (by decide) kL6, level_ok (by decide) kL7]

theorem qRows_mem {q : Rows} (hq : q ∈ twoAQRows) : ∃ l < 8, q = unpack 24 24 (QM l) := by
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hq
  have hl8 : l < 8 := by rw [qRows_len] at hl; exact hl
  refine ⟨l, hl8, ?_⟩
  have h := qRows_get hl8
  rwa [List.getElem?_eq_getElem hl, Option.getD_some] at h

theorem twoA_q_check : qCheckOf iotaARows twoAD1 twoABray twoAD2 twoAQRows 512 twoARoots
    twoACGens twoACSizes = true := by
  unfold qCheckOf
  simp only
  rw [dag₂_eq, bray_eq, gt_eq]
  have hS : (List.range D2.N).map (fun i => unpack 24 24 (D2.M i)) = SL := rfl
  rw [hS]
  simp only [Bool.and_eq_true, List.all_eq_true]
  have hpin := (gtBFS_of_K kQ).2
  rw [← qArr_eq] at hpin
  refine ⟨⟨⟨hpin, fun r hr => ?_⟩, fun i hi => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hi8 : i < 8 := by rw [roots_len] at hi; exact hi
    have h := roots_get hi8
    rw [← List.getD_eq_getElem _ #[] hi, ← h.2]
    exact contains_bfsTree h.1 rfl
  · exact List.all_eq_true.1 levels_ok i hi
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi8 : i < 8 := by simpa [twoABray] using hi
    have hb := MatL.allN_iff.1 kB i hi8
    rw [MatL.bAnd_eq, Bool.and_eq_true, MatL.allN_iff] at hb
    obtain ⟨h1, h2⟩ := inv_of hb.1
    rw [h2, h1]
    refine ⟨beq_self_eq_true _, ?_⟩
    intro q hq
    obtain ⟨l, hl, rfl⟩ := qRows_mem hq
    have hc : conjRows (unpack 24 24 (D2.M i)) (unpack 24 24 (D2.MI i)) (unpack 24 24 (QM l)) =
        unpack 24 24 (CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.mulWK (D2.M i) (QM l)) (D2.MI i)) := by
      unfold conjRows
      change mul (mul _ _) _ = _
      rw [mul_unpackW, mul_unpackW]
    rw [hc]
    exact mem_of_K (hb.2 l hl)

theorem twoA_misc_check : twoAMiscOf iotaARows twoAQRows = true := by
  have hm := kM
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨hmem, hcomm⟩, hfix⟩, hsq⟩, hne⟩ := hm
  have hcomm' := MatL.allN_iff.1 hcomm
  unfold twoAMiscOf
  rw [gt_eq]
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [iotaA_u]
    exact mem_of_K hmem
  · intro q hq
    obtain ⟨l, hl, rfl⟩ := qRows_mem hq
    rw [iotaA_u, mul_unpackW, mul_unpackW, Nat.eq_of_beq_eq_true (hcomm' l hl)]
  · rw [CertificateChecks.KernelCo1B.iotaA_eq,
      CFSG.KC.Co1F2.tr_sound CertificateChecks.KernelCo1B.trA_chk]
    exact (CFSG.KC.Co1Fix.fixK_sound hfix).1
  · simp [bfsTree, hN.2]
  · rw [iotaA_u, mul_unpackW, Nat.eq_of_beq_eq_true hsq, MatL.unpack_idM]
  · rw [CertificateChecks.KernelCo1B.iotaA_eq]
    exact CFSG.KC.Co1F2.validRows_unpackR _
  · rw [iotaA_u, ← MatL.unpack_idM]
    simpa using hne

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native in
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative in
theorem c2044 : (Native.centCheckOf iotaARows twoAD1 twoABray twoAD2 twoAVBase
      twoAVGens twoAVSizes = true
    )
    ∧ (Native.qCheckOf iotaARows twoAD1 twoABray twoAD2 twoAQRows 512 twoARoots
      twoACGens twoACSizes = true
    )
    ∧ (twoAMiscOf iotaARows twoAQRows = true) :=
  ⟨twoA_cent_check, twoA_q_check, twoA_misc_check⟩

end CertificateChecks.KernelCo1B.C2044

end
