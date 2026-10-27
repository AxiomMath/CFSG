module

public import Certificates.Data.CFSGNative.AS91.M24Syl
import CFSG.Certificates.Kernel.M24G.SylSound
import Certificates.Kernel.M24G.SylChecks
import Certificates.Kernel.M24G.TrioSextsEq

public section

namespace Certificates

open CFSG.KC.M24G CFSG.KC.M24G.SylC CFSG.Quasithin.H13.AS91.M24G

theorem certificate89021_trio0 : (Native.trioList ())[0]! = Native.baseTrio := by
  rw [trioList_eq]
  decide +kernel

open CFSG.Quasithin.H13.AS91.M24G in
theorem certificate89021 :
    (∀ g ∈ Native.s0Tabs, Native.img g 255 = 255 ∧
      Native.imgTrio g Native.baseTrio = Native.baseTrio ∧
      Native.imgSext g Native.baseSext = Native.baseSext ∧
      Native.imgSext g Native.pairPart = Native.pairPart) ∧
    (∃ r : Array (Nat × Nat × Nat) × Array Nat × Array Nat,
      Native.treeValid Native.validTriple (Native.s0Tabs.map Native.imgTriple) (0, 8, 16) r =
        true ∧ 1024 ≤ r.1.size ∧ (r.1.toList.map Native.keyTriple).Nodup) ∧
    (∃ r : Array Native.OSP × Array Nat × Array Nat,
      Native.treeValid Native.validOSP (Native.lTabs.map Native.imgOSP) Native.tup0 r = true ∧
        63 ≤ r.1.size ∧ (r.1.toList.map Native.keyOSP).Nodup) ∧
    ((∀ m < 2048, (∀ a ∈ Native.s0Tabs, Native.toddAct a m = m) → m = 0 ∨ m = 31) ∧
      ∀ a ∈ Native.s0Tabs, Native.toddAct a 31 = 31) ∧
    ((Native.sextList ()).size = 1771 ∧
      (∀ q < 1771, ∀ q' < q, Native.clsOf (Native.sextList ())[q]! ≠
        Native.clsOf (Native.sextList ())[q']!) ∧ Native.clsOf Native.baseSext = 31) ∧
    (∀ p < 3795, (∀ q ∈ Native.sextsThrough (Native.sextList ()) Native.baseTrio,
      Native.trioIn (Native.trioList ())[p]! (Native.sextList ())[q]! = true) → p = 0) ∧
    (Native.sortL (0 :: (Native.sextsThrough (Native.sextList ()) Native.baseTrio).map
      fun q => Native.clsOf (Native.sextList ())[q]!) = Native.v0List ∧
      Native.closedXor Native.v0List = true ∧ Native.closedXor Native.vpList = true) ∧
    (∀ v < 2048, ∀ w < 2048, v ≠ 0 → v ≠ 31 → w ≠ 0 → w ≠ 31 → w ≠ v → w ≠ 31 ^^^ v →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = v) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = 31 ^^^ v) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = w) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = 31 ^^^ w) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = v ^^^ w) →
      (∃ q < 1771, Native.clsOf (Native.sextList ())[q]! = 31 ^^^ v ^^^ w) →
      (Native.sp8 v w).Nodup ∧
      ((∀ a ∈ Native.s0Tabs, Native.toddAct a v ∈ Native.sp8 v w ∧
          Native.toddAct a w ∈ Native.sp8 v w) →
        Native.sortL (Native.sp8 v w) = Native.v0List ∨
          Native.sortL (Native.sp8 v w) = Native.vpList)) ∧
    (∃ r : Array (List Nat) × Array Nat × Array Nat,
      Native.treeValid Native.validSp (Native.genTabs.map Native.stepSp) Native.vpList r = true ∧
        3796 ≤ r.1.size ∧ (r.1.toList.map Native.keySp).Nodup) :=
  ⟨syl_s0Fix_of s0Fix_ok,
    syl_tripleOrbit_of triple_ok (Nat.le_of_eq tripleLen_ok.symm) tripleValid_ok,
    syl_tupleOrbit_of tuple_ok (Nat.le_of_eq tupleLen_ok.symm) tupleValid_ok,
    syl_fixed_of fixed_ok,
    syl_cls_of sextList_eq cls_ok,
    syl_trioDet_of trioSexts_eq certificate89021_trio0 trioDet_ok,
    syl_v0_of sextList_eq trioSexts_eq certificate89021_trio0 v0_ok,
    syl_span_of sextList_eq SextC.length span_ok,
    syl_spaceOrbit_of space_ok (Nat.le_of_eq spaceLen_ok.symm) spaceValid_ok⟩

end Certificates
