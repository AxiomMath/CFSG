module

public import Certificates.Kernel.Co1M.C16956
public import Certificates.Kernel.Co1M.C16956M
public import Certificates.Kernel.Co1M.C16956S0
public import Certificates.Kernel.Co1M.C16956S1
public import Certificates.Kernel.Co1M.C16956S2
public import Certificates.Kernel.Co1M.C16956S3
public import Certificates.Kernel.Co1M.G16954
public import CFSG.Certificates.Kernel.Co1M.C16956Glue

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2 CFSG.KC.Co1M
  CFSG.KC.VecK CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KD.Co1Thirteen CFSG.KD.C16956
  CertificateChecks.KernelVec.Co1 CertificateChecks.KernelCo1Cover

theorem scan16956_pt : ∀ p < 98280, CFSG.KC.M1F2.strictB (lk Pt 32 p) (fun w =>
    orB (notB (tauK (orbMemK 98280 (lk S 32) 17) TS16956 w)) (memL Q16956 w)) = true := by
  refine allS_cover (S := 256) (ns := 384) (fun s hs => ?_) (by norm_num)
  have e : ∀ s, scanSl (orbMemK 98280 (lk S 32) 17) (lk Pt 32) TS16956 Q16956 s = true →
      allS (Nat.mul s 256) (sliceN 98280 256 s) (fun p => CFSG.KC.M1F2.strictB (lk Pt 32 p)
        (fun w => orB (notB (tauK (orbMemK 98280 (lk S 32) 17) TS16956 w)) (memL Q16956 w))) =
        true := fun _ h => h
  apply e
  by_cases h1 : s < 96
  · exact Scan16956a.all s h1
  by_cases h2 : s < 192
  · have hb : s - 96 < 96 := by omega
    have := Scan16956b.all (s - 96) hb
    have es : Nat.add (s - 96) 96 = s := Nat.sub_add_cancel (by omega)
    unfold sc16956b at this
    rwa [es] at this
  by_cases h3 : s < 288
  · have hb : s - 192 < 96 := by omega
    have := Scan16956c.all (s - 192) hb
    have es : Nat.add (s - 192) 192 = s := Nat.sub_add_cancel (by omega)
    unfold sc16956c at this
    rwa [es] at this
  · have hb : s - 288 < 96 := by omega
    have := Scan16956d.all (s - 288) hb
    have es : Nat.add (s - 288) 288 = s := Nat.sub_add_cancel (by omega)
    unfold sc16956d at this
    rwa [es] at this

theorem scan16956 :
    ∀ w < 2 ^ 24, toVecD 24 w ∈ certX → tauK (orbMemK 98280 (lk S 32) 17) TS16956 w = true →
      w ∈ Q16956 := by
  intro w hw hX ht
  have hm := (mem_certX_iff hw).2 hX
  rw [← cm_orb_inPts, ← orb2_eq, inPts2_iff] at hm
  obtain ⟨i, hi, e⟩ := hm
  rw [pts2 hi] at e
  have h := scan16956_pt i hi
  have hs : ∀ (y : Nat) (k : Nat → Bool), CFSG.KC.M1F2.strictB y k = k y := fun y k => by
    cases y <;> rfl
  rw [e, hs] at h
  rw [ht, CFSG.KC.Co1ThirteenGlue.orB_eq, CFSG.KC.Co1ThirteenGlue.notB_eq] at h
  exact (CFSG.KC.Co1ThirteenGlue.memL_iff w Q16956).1 h

theorem rep_M0_16956 :
    MRep (unpackR 24 (getL 0 M16956 0)) A₁ := by
  have h := c16956_base
  rw [Bool.and_eq_true, ← CFSG.KC.Co1B.beq_unpack, ← CFSG.KC.Co1B.beq_unpack, beq_iff_eq,
    beq_iff_eq] at h
  rw [h.1]
  exact rep_R0

theorem rep_M1_16956 :
    MRep (unpackR 24 (getL 0 M16956 1)) A₂ := by
  have h := c16956_base
  rw [Bool.and_eq_true, ← CFSG.KC.Co1B.beq_unpack, ← CFSG.KC.Co1B.beq_unpack, beq_iff_eq,
    beq_iff_eq] at h
  rw [h.2]
  exact rep_R1

theorem co1_thirteen_k
    (x : CFSG.Blueprint.NativeSporadic.Co1) (hx : orderOf x = 13) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) = 156 ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1),
        ∀ z ∈ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1),
          orderOf z = 3 → g * z * g⁻¹ ∈ Subgroup.zpowers z → g ^ 39 = 1 := by
  have hm := c16956_mem
  rw [Bool.and_eq_true] at hm
  exact CFSG.KC.Co1ThirteenGlue.co1_thirteen_of_check c16956_ok rep_M0_16956 rep_M1_16956
    (fun _ hw => mem_certX_iff hw) scan16956 hm.1 hm.2 x hx

end CertificateChecks.KernelCo1M

end
