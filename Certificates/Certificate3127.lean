module

public import CFSG.Monster.B.TwoA.Unitary.TransvSwitchInputs
public import Certificates.Certificate3175
public import Certificates.Certificate3081
public import Certificates.Kernel.MonsterB.Sw3127Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Fischer.F4

public section

open CFSG.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA Matrix
open CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT CFSG.KC.F4M CFSG.KC.U6G CFSG.KC.Loop
open CertificateChecks.Orb14 CertificateChecks.Batch3124 CertificateChecks.Batch3175
open CertificateChecks.Sw3127 CertificateChecks.Fix3081

namespace CertificateChecks.Batch3127

open CFSG.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA Matrix
open CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT CFSG.KC.F4M CFSG.KC.U6G CFSG.KC.Loop
open CertificateChecks.Orb14 CertificateChecks.Batch3124 CertificateChecks.Batch3175
open CertificateChecks.Sw3127 CertificateChecks.Fix3081

set_option maxRecDepth 100000

theorem swGRows_tau : Native.actD 22 swGRows 60 = 6144 := by decide +kernel

theorem mul_inv_list : (Co2Inv.rowsMul swGRows swGInvRows).toList = Co2Inv.idRows.toList := by
  decide +kernel

theorem swG_mul_inv_rows : Co2Inv.rowsMul swGRows swGInvRows = Co2Inv.idRows :=
  Array.toList_inj.1 mul_inv_list

theorem swQRows_sigma : Native.actD 22 swQRows 6144 = 6144 := by decide +kernel

@[expose] noncomputable def SWP : Nat := nat_lit 1181546740355545710597

theorem kQ : andB (shapeL 22 (pw2 22) [swQRows]) (Nat.beq (packL 22 swQRows.toList) SQ) = true := by
  quickRfl

theorem kNd : nodupM n6VecArr.toList 0 = true := by quickRfl

@[expose] noncomputable def swK (Q V S : Nat) : Bool :=
  allN 891 fun j => andB (Nat.blt (fget S j 10) 891)
    (Nat.beq (actK Q (fget V j 22)) (fget V (fget S j 10) 22))

theorem kSw : swK SQ V891 SI = true := by quickRfl

@[expose] noncomputable def swMatK (M : Nat) : Bool :=
  andB (Nat.beq (det M) 1) (gramOK fun r => fget M r 12)

theorem kSwMat : swMatK SWP = true := by quickRfl

@[expose] noncomputable def swPlK (PL I S M : Nat) : Bool :=
  allN 891 fun j => allN 3 fun a =>
    (fun y => Nat.beq (expK (rowP PL (fget I (fget S j 10) 10)) y) y)
      (imK true (fun r => fget M r 12) (rowP PL (fget I j 10) a))

theorem kSwPl : swPlK PLP ISO SI SWP = true := by quickRfl

theorem neg_sw : notB (swK SQ V891 (Nat.xor SI 1)) = true := by quickRfl

theorem neg_mat : notB (swMatK (Nat.xor SWP 1)) = true := by quickRfl

theorem neg_pl : notB (swPlK PLP ISO (Nat.xor SI (pw2 (nat_lit 20))) SWP) = true := by quickRfl

theorem rows6 : ∀ i : Fin 6, swRows6[(i : ℕ)]! = fget SWP i 12 := by decide +kernel

theorem swMat_eq : swMat = Matrix.of fun r : Fin 6 => vec6 (fget SWP r 12) := by
  unfold swMat
  exact congrArg Matrix.of (funext fun r => by rw [rows6])

theorem swMat_dec : swMat = decM SWP := by
  rw [swMat_eq]
  rfl

theorem swMat_det : swMat.det = 1 := by
  have h := kSwMat
  unfold swMatK at h
  rw [andB_eq, Bool.and_eq_true, beq_true_iff] at h
  rw [swMat_dec, det_sound, h.1]
  rfl

theorem swMat_gram : swMat * hGram * (barM swMat)ᵀ = hGram := by
  have h := kSwMat
  unfold swMatK at h
  rw [andB_eq, Bool.and_eq_true] at h
  rw [swMat_eq]
  exact gram_of_gramOK (M := fun r => fget SWP r 12) h.2

theorem q_spec : swQRows.size = 22 ∧ ∀ x ∈ swQRows.toList, x < 2 ^ 22 := by
  have h := andB_eq_true.1 kQ
  have := (shapeL_iff 22 (pw2 22) _).1 h.1 swQRows (List.mem_singleton_self _)
  exact ⟨this.1, fun x hx => (this.2 x hx).trans_eq (pw2_eq 22)⟩

theorem actQ (v : ℕ) : Native.actD 22 swQRows v = actK SQ v := by
  rw [actD_eq_actK q_spec.1 q_spec.2, Nat.eq_of_beq_eq_true (andB_eq_true.1 kQ).2]

theorem sw_spec {j : ℕ} (hj : j < 891) : fget SI j 10 < 891 ∧
    actK SQ (fget V891 j 22) = fget V891 (fget SI j 10) 22 := by
  have h := kSw
  unfold swK at h
  rw [allN_iff] at h
  have h' := h j hj
  rw [andB_eq_true, Nat.blt_eq, beq_true_iff] at h'
  exact h'

theorem swIdx_val (j : Fin 891) : (swIdx j : ℕ) = fget SI j 10 := by
  obtain ⟨hlt, heq⟩ := sw_spec j.2
  change n6VecArr.toList.idxOf (Native.actD 22 swQRows n6VecArr[(j : ℕ)]!) % 891 = _
  rw [actQ, Batch3081.vec_eq j.2, heq, ← Batch3081.vec_eq hlt]
  have hsz : (fget SI j 10) < n6VecArr.toList.length := by
    rw [Array.length_toList, Batch3081.kSizes.1]
    exact hlt
  have hget : n6VecArr.toList[fget SI j 10] = n6VecArr[fget SI j 10]! := by
    rw [Array.getElem_toList]
    exact (getElem!_pos n6VecArr _ (by rw [Batch3081.kSizes.1]; exact hlt)).symm
  rw [← hget, List.Nodup.idxOf_getElem (nodupM_spec _ _ kNd).1 _ hsz, Nat.mod_eq_of_lt hlt]

theorem pl_spec' (j : ℕ) (hj : j < 891) (a : ℕ) (ha : a < 3) :
    (fun y => Nat.beq (expK (rowP PLP (fget ISO (fget SI j 10) 10)) y) y)
      (imK true (fun r => fget SWP r 12) (rowP PLP (fget ISO j 10) a)) = true := by
  have h := kSwPl
  unfold swPlK at h
  rw [allN_iff] at h
  have h' := h j hj
  rw [allN_iff] at h'
  exact h' a ha

theorem swIdx_ok : ∀ j : Fin 891,
    n6VecArr[(swIdx j : ℕ)]! = Native.actD 22 swQRows n6VecArr[(j : ℕ)]! ∧
    ∀ a : Fin 3, expand (b6Iso (swIdx j)) (barV (planeRow (b6Iso j) a) ᵥ* swMat) =
      barV (planeRow (b6Iso j) a) ᵥ* swMat := by
  intro j
  obtain ⟨hlt, heq⟩ := sw_spec j.2
  refine ⟨?_, fun a => ?_⟩
  · rw [swIdx_val, actQ, Batch3081.vec_eq j.2, heq, Batch3081.vec_eq hlt]
  · have h := beq_true_iff.1 (pl_spec' j j.2 a a.2)
    have hrow : barV (planeRow (b6Iso j) a) ᵥ* swMat =
        vec6 (imK true (fun r => fget SWP r 12) (rowP PLP (fget ISO j 10) a)) := by
      rw [imK_eq]
      have e : b6Iso j = ⟨fget ISO j 10, iso_lt j j.2⟩ := Fin.ext (Batch3175.b6Iso_val j)
      rw [e, planeRow_eq, swMat_eq]
      rfl
    have hp : b6Iso (swIdx j) = ⟨fget ISO (fget SI j 10) 10, iso_lt _ hlt⟩ := by
      apply Fin.ext
      rw [Batch3175.b6Iso_val, swIdx_val]
    rw [hrow, hp, expand_eq, ← expK_eq, h]

end CertificateChecks.Batch3127

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA Matrix in
theorem certificate3127 : (Native.actD 22 swGRows 60 = 6144)
    ∧ (Co2Inv.rowsMul swGRows swGInvRows = Co2Inv.idRows)
    ∧ (Native.actD 22 swQRows 6144 = 6144)
    ∧ (swMat.det = 1)
    ∧ (swMat * hGram * (barM swMat)ᵀ = hGram)
    ∧ (∀ j : Fin 891,
       n6VecArr[(swIdx j : ℕ)]! = Native.actD 22 swQRows n6VecArr[(j : ℕ)]! ∧
       ∀ a : Fin 3, expand (b6Iso (swIdx j)) (barV (planeRow (b6Iso j) a) ᵥ* swMat) =
         barV (planeRow (b6Iso j) a) ᵥ* swMat) := by
  exact ⟨CertificateChecks.Batch3127.swGRows_tau, CertificateChecks.Batch3127.swG_mul_inv_rows, CertificateChecks.Batch3127.swQRows_sigma,
    CertificateChecks.Batch3127.swMat_det, CertificateChecks.Batch3127.swMat_gram, CertificateChecks.Batch3127.swIdx_ok⟩

end Certificates
