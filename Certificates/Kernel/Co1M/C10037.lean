
module

public import CFSG.Monster.GMS.S365CosetSpecBase
public import CFSG.Monster.GMS.S365CentBasic
public import CFSG.Monster.GMS.S365Facts
public import Certificates.Data.CFSGNative.Co1.S365CentPath
public import CFSG.Monster.GMS.S365CentPathSpecInputs
public import Certificates.Kernel.Co1M.C10041
public import Certificates.Kernel.Co1M.Cen10037
public import CFSG.Certificates.Kernel.Co1M.GmsPathSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.GmsPath CFSG.KC.Co1M CFSG.KC.VecK CFSG.KC.M1F2 CFSG.KD.Co1M Finset
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs
  CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365CentNative
  CFSG.Monster.GMS.S365

theorem basis37 : CFSG.KC.GmsPath.basisK QP PM PI MX MY = true := by quickRfl

theorem qRows_rows : ∀ j < 24, qRows[j]?.getD 0 = rowF 24 QP j := by decide +kernel

theorem strictB_eq37 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sorted37 : ∀ i, i + 1 < 98280 →
    lk CertificateChecks.KernelVec.Co1.S 32 i < lk CertificateChecks.KernelVec.Co1.S 32 (i + 1) := by
  intro i hi
  have hn : (CFSG.Sporadic.Co1.Native.co1Data ()).n = 98280 := rfl
  have h := cmHsort i (by rw [hn]; omega)
  unfold sortAt at h
  rw [strictB_eq37] at h
  simp only [andB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq, hn] at h
  rcases h.2.2.2 with h' | h'
  · omega
  · exact h'

theorem countBelow_card (p : Nat → Bool) (n acc : Nat) :
    countBelow p n acc = acc + ((range n).filter fun i => p i = true).card := by
  induction n generalizing acc with
  | zero => simp [countBelow]
  | succ n ih =>
    rw [countBelow, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p n = true
    · simp only [hp, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp [hp]

theorem lab_eq (w : Nat) :
    (tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w == 1) =
      lab1 (qK QP) (orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17) w := by
  have e : inPtsN (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
    cm_orb_inPts w
  have eq : parity24N (vecMulN 24 qRows w &&& w) = qK QP w := by
    rw [vecMulN_eq_vmF qRows_rows, parity24N_eq]
    rfl
  unfold tyLabN lab1
  rw [eq, e]
  by_cases h0 : w = 0
  · simp [h0]
  · cases qK QP w <;> cases orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w <;>
      simp [h0]

theorem pat4_eq (v : Nat) :
    pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 v =
      allK (lab1 (qK QP) (orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17)) v := by
  have h24 : (2 : Nat) ^^^ 4 = 6 := by norm_num
  unfold pat4 allK
  rw [lab_eq, lab_eq, lab_eq, lab_eq, Nat.xor_assoc, h24]

theorem count37 :
    countBelow (pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4)
      16777216 0 = 1995840 := by
  rw [countBelow_card, Nat.zero_add]
  have h := count_of_checks basis37 (lk CertificateChecks.KernelVec.Co1.S 32) (n := 98280)
    (b := 17) (C := 103356) (by norm_num) (by norm_num) sorted37 cen37All
  have e : (16777216 : Nat) = 2 ^ 24 := by norm_num
  have hf : ((range (2 ^ 24)).filter fun v =>
      pat4 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 v = true) =
      (range (2 ^ 24)).filter fun v =>
        allK (lab1 (qK QP) (orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17)) v =
          true :=
    Finset.filter_congr fun v _ => by rw [pat4_eq]
  rw [e, hf]
  omega

theorem unpackR_get (M j : Nat) (hj : j < 24) :
    (CFSG.KC.Co1F2.unpackR 24 M)[j]?.getD 0 = rowF 24 M j := by
  simp only [CFSG.KC.Co1F2.unpackR, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
  change M / 2 ^ (24 * j) % 2 ^ 24 = (M >>> (j * 24)) &&& (1 <<< 24 - 1)
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.mul_comm j 24]

theorem getElem_three (a b c l : Nat) (hl : l < 3) :
    ([a, b, c].map (CFSG.KC.Co1F2.unpackR 24)).toArray[l]! =
      CFSG.KC.Co1F2.unpackR 24 (CFSG.KC.Co1F2.getL 0 [a, b, c] l) := by
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl <;> rfl

theorem vec_unpack (M v : Nat) : vecMulN 24 (CFSG.KC.Co1F2.unpackR 24 M) v = vmF 24 M v :=
  vecMulN_eq_vmF (fun j hj => unpackR_get M j hj) v

theorem applyPath_eq (path : List Nat) (hp : ∀ l ∈ path, l < 3) (v : Nat) :
    applyPath ([CT0, CT1, CT2].map (CFSG.KC.Co1F2.unpackR 24)).toArray path v =
      path.foldl (fun acc l => vmF 24 (CFSG.KC.Co1F2.getL 0 [CT0, CT1, CT2] l) acc) v := by
  unfold applyPath
  induction path generalizing v with
  | nil => rfl
  | cons l p ih =>
    rw [List.foldl_cons, List.foldl_cons, getElem_three _ _ _ l (hp l (by simp)), vec_unpack]
    exact ih (fun l' h' => hp l' (List.mem_cons_of_mem _ h')) _

theorem c10037_path : pathCheck = true := by
  unfold pathCheck
  have h1 : ∀ l ∈ pathE1, l < 3 := by decide
  have h2 : ∀ l ∈ pathE2, l < 3 := by decide
  have h12 : ∀ l ∈ pathE12, l < 3 := by decide
  rw [count37, cosetRowsT_eq, List.all_toArray, applyPath_eq _ h1, applyPath_eq _ h2,
    applyPath_eq _ h12]
  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, isFixedN, vec_unpack]
  quickRfl

theorem c10037_neg :
    (!CFSG.KC.GmsPath.basisK QP (PM ^^^ 2) PI MX MY && !CFSG.KC.GmsPath.basisK QP PM PI (MX ^^^ 1) MY &&
      !Nat.beq (sumS 19968 256 cen37) 417) = true := by
  quickRfl

open Certificates in
open CFSG.Monster.GMS.S365 in
theorem c10037 :
    pathCheck = true := c10037_path

end CertificateChecks.KernelCo1M

end
