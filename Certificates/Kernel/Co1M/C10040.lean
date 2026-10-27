module

public import CFSG.Monster.GMS.S365CentPathSpec
public import CFSG.Monster.GMS.S365CentRootSpec
public import CFSG.Monster.GMS.S365CentDefs
public import Certificates.Data.CFSGNative.Co1.S365CentWit
public import CFSG.Monster.GMS.S365CentWitSpecInputs
public import Certificates.Kernel.Co1M.C10037
public import Certificates.Kernel.Co1M.Wit10040
public import Certificates.Kernel.Co1M.Data10040
public import CFSG.Certificates.Kernel.Co1M.GmsWitSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.GmsPath CFSG.KC.Co1M CFSG.KC.M1F2 CFSG.KD.Co1M Finset
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs
  CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365CentNative
  CFSG.Monster.GMS.S365

theorem dual40 : dualK CM DM GS = true := by quickRfl

theorem mask40 : maskK QP (orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17)
    CM M2 M4 = true := by quickRfl

theorem shift40 : shiftK M4 SH = true := by quickRfl

theorem pair40 : pairK M2 M4 SH = true := by quickRfl

theorem gs_eq : rootGs = GS := by decide +kernel

theorem gs_len : 16 ≤ GS.length := by decide

theorem lab1_eq (w : Nat) :
    (tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w == 1) =
      l1K QP (orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17) w := by
  have e : inPtsN (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
    cm_orb_inPts w
  have eq : parity24N (vecMulN 24 qRows w &&& w) = qK QP w := by
    rw [vecMulN_eq_vmF qRows_rows, parity24N_eq]
    rfl
  unfold tyLabN l1K
  rw [eq, e, andB_eq, andB_eq, notB_eq, notB_eq, notB_eq, beq_dec]
  by_cases h0 : w = 0
  · simp [h0]
  · cases qK QP w <;> cases orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w <;>
      simp [h0]

theorem lab3_eq (w : Nat) :
    (tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w == 3) =
      l3K QP (orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17) w := by
  have e : inPtsN (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
    cm_orb_inPts w
  have eq : parity24N (vecMulN 24 qRows w &&& w) = qK QP w := by
    rw [vecMulN_eq_vmF qRows_rows, parity24N_eq]
    rfl
  unfold tyLabN l3K
  rw [eq, e, andB_eq, andB_eq, notB_eq, notB_eq, beq_dec]
  by_cases h0 : w = 0
  · simp [h0]
  · cases qK QP w <;> cases orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w <;>
      simp [h0]

theorem xor_eq' (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem pat0_eq (v : Nat) :
    pat0 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40 v =
      pat0K QP (orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17) v := by
  unfold pat0 pat0K
  simp only [lab1_eq, lab3_eq, andB_eq, xor_eq', Nat.xor_assoc, Nat.reduceXor]
  simp only [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

theorem killed_eq (path : List Nat) (hp : ∀ l ∈ path, l < 3) (v : Nat) :
    killed qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40 cosetRowsT
      path v = killedK QP (orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17)
        [CT0, CT1, CT2] path v := by
  have aux : ∀ (P : Nat → Bool) (w : Nat), (decide (w < 16777216) && w != 0 && !P w) =
      CFSG.KLie.CT.andB (Nat.blt w (CFSG.KLie.CT.pw2 24))
        (CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (Nat.beq w 0)) (CFSG.KLie.CT.notB (P w))) := by
    intro P w
    rw [andB_eq, andB_eq, notB_eq, notB_eq, blt_dec, beq_dec, pw2_eq]
    by_cases h1 : w < 16777216 <;> by_cases h0 : w = 0 <;> simp [h1, h0]
  unfold killed killedK
  rw [cosetRowsT_eq, applyPath_eq _ hp, strictB_eq, ← applyK_eq]
  simp only [pat0_eq]
  exact aux _ _

theorem wordA_lt40 : ∀ l ∈ CFSG.Monster.GMS.S365.wordA, l < 3 := by decide

theorem wordB_lt40 : ∀ l ∈ CFSG.Monster.GMS.S365.wordB, l < 3 := by decide

theorem countBelow_zero_of (p : Nat → Bool) (n : Nat) (h : ∀ v < n, p v = false) :
    countBelow p n 0 = 0 := by
  have key : ∀ m acc, m ≤ n → countBelow p m acc = acc := by
    intro m
    induction m with
    | zero => intro acc _; rfl
    | succ m ih =>
      intro acc hm
      rw [countBelow, h m (by omega)]
      exact ih acc (by omega)
  exact key n 0 le_rfl

theorem wcount : countBelow (fun v =>
    pat0 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40 v &&
      v != 1 &&
      !(killed qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40
          cosetRowsT CFSG.Monster.GMS.S365.wordA v ||
        killed qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40
          cosetRowsT CFSG.Monster.GMS.S365.wordB v)) 16777216 0 = 0 := by
  refine countBelow_zero_of _ _ fun v hv => Bool.eq_false_iff.2 fun hbad => ?_
  have hv' : v < 2 ^ 24 := lt_of_lt_of_eq hv (by norm_num)
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, bne_iff_ne, ne_eq] at hbad
  obtain ⟨⟨hpat, hv1⟩, hkA, hkB⟩ := hbad
  rw [pat0_eq] at hpat
  rw [killed_eq _ wordA_lt40] at hkA
  rw [killed_eq _ wordB_lt40] at hkB
  have hp := hpat
  unfold pat0K at hp
  simp only [andB_eq, Bool.and_eq_true] at hp
  obtain ⟨h6, -, h1, h2, -⟩ := hp
  rw [l3K_true] at h6 h2
  rw [l1K_true] at h1
  obtain ⟨j, hj, hSj⟩ := exists_of_orbMemK (by norm_num) h2.2.2
  have hw := wit40All j hj
  unfold wit40 witAt at hw
  rw [strictB_eq, strictB_eq, hSj] at hw
  have hvv : Nat.xor (Nat.xor v 2) 2 = v := by
    change (v ^^^ 2) ^^^ 2 = v
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hvv] at hw
  obtain ⟨-, -, -, hmx, hmy, -, -, hq2, hq4, -⟩ := basisK_spec basis37
  have hp24 : v ^^^ 2 < 2 ^ 24 := Nat.xor_lt_two_pow hv' (by norm_num)
  have hX : parF (Nat.land (Nat.xor v 2) MX) = false := by
    have e := qK_xor QP (v ^^^ 2) 2
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, hmx _ hp24, hq2] at e
    have e1 : qK QP v = false := h1.2.1
    have e2 : qK QP (v ^^^ 2) = false := h2.2.1
    rw [e1, e2] at e
    simpa using e.symm
  have hY : parF (Nat.land (Nat.xor v 2) MY) = false := by
    have e := qK_xor QP (v ^^^ 2) 4
    rw [Nat.xor_assoc, hmy _ hp24, hq4] at e
    have e6 : qK QP (v ^^^ (2 ^^^ 4)) = false := h6.2.1
    have e2 : qK QP (v ^^^ 2) = false := h2.2.1
    rw [e6, e2] at e
    simpa using e.symm
  have hb : Nat.blt (Nat.xor v 2) (CFSG.KLie.CT.pw2 24) = true := by
    rw [pw2_eq, Nat.blt_eq]
    exact hp24
  have hb1 : Nat.beq v 1 = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
    exact hv1
  rw [hb, hX, hY, hpat, hb1, hkA, hkB] at hw
  simp [andB_eq, orB_eq, notB_eq] at hw

theorem c10040_wit : witCheckRef = true := by
  unfold witCheckRef witCheck
  rw [wcount, cosetRowsT_eq, applyPath_eq _ wordA_lt40, applyPath_eq _ wordB_lt40]
  quickRfl

theorem orth_of (u : Nat) (h : orthAllN rootGs u = true) : ∀ g ∈ GS, parF (u &&& g) = false := by
  rw [gs_eq] at h
  unfold orthAllN at h
  intro g hg
  have := List.all_eq_true.1 h g hg
  rw [parity24N_eq] at this
  simpa using this

theorem c10040_nopat : noPatRef = true := by
  unfold noPatRef noPat
  dsimp only
  rw [List.all_eq_true]
  intro a ha
  rw [mem_collectLt] at ha
  simp only [List.not_mem_nil, or_false] at ha
  rw [Bool.or_eq_true]
  by_cases h3a : (tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 a
      == 3) = true
  swap
  · left
    simpa using h3a
  right
  rw [List.all_eq_true]
  intro b hb
  rw [mem_collectLt] at hb
  simp only [List.not_mem_nil, or_false] at hb
  rw [Bool.or_eq_true, Bool.or_eq_true]
  by_cases h3b : (tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 b
      == 3) = true
  swap
  · left
    left
    simpa using h3b
  by_cases h3ab : (tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      (a ^^^ b) == 3) = true
  swap
  · left
    right
    simpa using h3ab
  right
  rw [List.all_eq_true]
  intro om hom
  rw [mem_collectLt] at hom
  simp only [List.not_mem_nil, or_false] at hom
  rw [Bool.not_eq_true']
  by_contra hc
  rw [Bool.not_eq_false, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  rw [lab3_eq] at h3a h3b h3ab
  rw [lab1_eq] at c1 c2 c3 c4
  have h24 : (16777216 : Nat) = 2 ^ 24 := by norm_num
  obtain ⟨ka, xa⟩ := dual_spec dual40 gs_len (h24 ▸ ha.1) (orth_of a ha.2)
  obtain ⟨kb, xb⟩ := dual_spec dual40 gs_len (h24 ▸ hb.1) (orth_of b hb.2)
  obtain ⟨kg, xg⟩ := dual_spec dual40 gs_len (h24 ▸ hom.1) (orth_of om hom.2)
  set α := vmF 24 DM a >>> 16
  set β := vmF 24 DM b >>> 16
  set γ := vmF 24 DM om >>> 16
  have lt8 : ∀ {x y : Nat}, x < 256 → y < 256 → x ^^^ y < 256 := fun hx hy =>
    Nat.xor_lt_two_pow (n := 8) hx hy
  have m := fun {c : Nat} (hc : c < 256) => mask_spec mask40 hc
  refine pair_spec shift40 pair40 ka kb kg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [(m ka).1, xa]
    exact h3a
  · rw [(m kb).1, xb]
    exact h3b
  · rw [(m (lt8 ka kb)).1, Xc_xor, xa, xb]
    exact h3ab
  · rw [(m kg).2, xg]
    exact c1
  · rw [(m (lt8 kg ka)).2, Xc_xor, xg, xa]
    exact c2
  · rw [(m (lt8 kg kb)).2, Xc_xor, xg, xb]
    exact c3
  · rw [(m (lt8 (lt8 kg ka) kb)).2, Xc_xor, Xc_xor, xg, xa, xb]
    exact c4

open Certificates in
open CFSG.Monster.GMS.S365 in
theorem c10040 :
    (witCheckRef = true)
    ∧ (noPatRef = true) := ⟨c10040_wit, c10040_nopat⟩

end CertificateChecks.KernelCo1M

end
