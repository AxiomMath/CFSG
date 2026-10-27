
module

public import CFSG.Sporadic.Co1Block.IotaCheckInputs
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Schreier.TextCheck
public meta import CFSG.Sporadic.Co2Cert.Cert
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Certificates.Kernel.Co1B.Iota
public import Certificates.Kernel.SporSch.Co2M.Local
public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C2042

open CFSG.KS.MatRep CFSG.KS.Co2M CFSG.RankThree.Native.F2 CertificateChecks.KernelSporSch.Co2M
  CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co2Cert

@[expose] noncomputable def ET : List (ℕ × ℕ) := extP mmK I22 aT iotaDerivs

theorem words_ok : (extOK 2 iotaDerivs && extWordsOK 2 iotaDerivs) = true := by quickRfl

theorem chk : (Nat.beq ET.length 52 && Nat.beq (ET.getD 23 (0, 0)).1 zP.1 &&
    Nat.beq (ET.getD 51 (0, 0)).1 (cmpP (sT.getD 8 (0, 0)) (sT.getD 0 (0, 0))).1 &&
    Nat.blt 8 sT.length && Nat.beq qT.length 8 &&
    (List.range 8).all fun k => Nat.beq (ET.getD (36 + k) (0, 0)).1 (qT.getD k (0, 0)).1) = true := by
  quickRfl

theorem ERep : RepT 22 co2PackedVecs (extendArrs aArrs iotaDerivs) ET := by
  have h := words_ok
  simp only [Bool.and_eq_true] at h
  exact repT_extend good V_size mmK_eq I22_eq _ aRep h.1

theorem eq_of_rep {a b : Array ℕ} {M M' N N' : ℕ} (ha : Rep 22 co2PackedVecs a M M')
    (hb : Rep 22 co2PackedVecs b N N') (h : M = N) : a = b := by
  rw [ha.1, hb.1, h]

theorem allInv_E : allInv (extendArrs aArrs iotaDerivs) = true := by
  unfold allInv
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro j hj
  have hj' : j < ET.length := by rw [← ERep.1]; exact hj
  have hr := ERep.2 j hj'
  have hi := rep_invCand good hr
  rw [V_size] at hi
  rw [hi.1, hr.1]
  have h := isInvA_permOfMat good.hd good.nodup good.lt hr.2
  rwa [V_size] at h

theorem iota_check : iotaCheckOf CFSG.Sporadic.Co1Schreier.Native.hRows0
    CFSG.Sporadic.Co1Schreier.Native.hRows1 aArrs zArr uArr qArrs = true := by
  have hc := chk
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq,
    Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨⟨hlen, h23⟩, h51⟩, hs⟩, hq⟩, hk⟩ := hc
  have hw := words_ok
  simp only [Bool.and_eq_true] at hw
  have hdag : (CFSG.Sporadic.Co1Schreier.Native.dag [CFSG.Sporadic.Co1Schreier.Native.hRows0,
      CFSG.Sporadic.Co1Schreier.Native.hRows1] iotaDerivs).2.2 = true := by
    rw [hRows_eq.1, hRows_eq.2]
    exact congrArg (fun p => p.2.2) (CFSG.KC.Co1B.dag_sound dag_chk)
  have hz : (extendArrs aArrs iotaDerivs)[23]! = zArr :=
    eq_of_rep (ERep.2 23 (by omega)) zRep h23
  have hu : (extendArrs aArrs iotaDerivs)[51]! = uArr := by
    have h8 := sRep.2 8 hs
    have h0 := sRep.2 0 (by omega)
    have hc := rep_cmp h8 h0
    exact eq_of_rep (ERep.2 51 (by omega)) hc h51
  have hqk : ∀ k < 8, (extendArrs aArrs iotaDerivs)[36 + k]! = qArrs[k]! := fun k hk' =>
    eq_of_rep (ERep.2 (36 + k) (by omega)) (qRep.2 k (by omega)) (hk k hk')
  unfold iotaCheckOf
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hdag, hw.2⟩, allInv_E⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hz]
    exact CFSG.KS.Raw.eqA_self _
  · rw [hu]
    exact CFSG.KS.Raw.eqA_self _
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk'
    rw [hqk k hk']
    exact CFSG.KS.Raw.eqA_self _

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Schreier in
theorem c2042 : iotaCheckOf CFSG.Sporadic.Co1Schreier.Native.hRows0
    CFSG.Sporadic.Co1Schreier.Native.hRows1 aArrs zArr uArr qArrs = true := iota_check

end CertificateChecks.KernelCo1B.C2042

end
