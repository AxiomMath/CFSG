
module

public import Certificates.Certificate3080Base
import all Certificates.Certificate3080Base

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsInputs
public import Certificates.Kernel.MonsterB.Orb14GlueBase
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Fischer.F4
public import Certificates.Kernel.MonsterB.Orb14Glue

public section

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT
open CFSG.Monster.B.Classical.UnitarySix (bar)
open CertificateChecks.Orb14

namespace CertificateChecks.Batch3080

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT
open CFSG.Monster.B.Classical.UnitarySix (bar)
open CertificateChecks.Orb14

set_option maxRecDepth 100000

theorem singVec_inj {i j : Fin 693} (h : singVec i = singVec j) : i = j := by
  unfold singVec at h
  rw [sing_get i.2, sing_get j.2] at h
  have e := vec6_inj (fget12_lt _ _) (fget12_lt _ _) h
  apply Fin.ext
  rcases lt_trichotomy (i : ℕ) j with hl | hl | hl
  · exact absurd e (ne_of_lt (sing_inc.2 i i.2 j j.2 hl))
  · exact hl
  · exact absurd e (ne_of_gt (sing_inc.2 j j.2 i i.2 hl))

theorem pt_spec (i : Fin 693) : singVec i ≠ 0 ∧ hU (singVec i) (singVec i) = 0 ∧
    singVec i (piv (singVec i)) = 1 := by
  have h := kPts
  unfold ptsOK at h
  rw [allN_iff] at h
  have h' := h i i.2
  simp only [andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at h'
  have e : singVec i = vec6 (fget SGL i 12) := by
    unfold singVec
    rw [sing_get i.2]
  rw [e, hU_self_eq_zero, ← isoK_eq, vec6_ne_zero_iff (fget12_lt _ _), ← leadK_iff]
  exact ⟨h'.1, h'.2.1, h'.2.2⟩

theorem singVec_ok : ∀ i : Fin 693, singVec i ≠ 0 ∧ hU (singVec i) (singVec i) = 0 :=
  fun i => ⟨(pt_spec i).1, (pt_spec i).2.1⟩

theorem singVec_distinct : ∀ i j : Fin 693, ∀ c : F4, singVec i = c • singVec j → i = j := by
  intro i j c h
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact (pt_spec i).1 h
  have hp : piv (singVec i) = piv (singVec j) := by rw [h, piv_smul hc]
  have h1 := (pt_spec i).2.2
  rw [hp, h, Pi.smul_apply, smul_eq_mul, (pt_spec j).2.2, mul_one] at h1
  rw [h1, one_smul] at h
  exact singVec_inj h

end CertificateChecks.Batch3080

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Unitary CFSG.Fischer in

theorem certificate3080 : (∀ i : Fin 693, singVec i ≠ 0 ∧ hU (singVec i) (singVec i) = 0)
    ∧ (∀ i j : Fin 693, ∀ c : F4, singVec i = c • singVec j → i = j)
    ∧ (∀ v : V6, v ≠ 0 → hU v v = 0 → v = v (piv v) • singVec (singLook v))
    ∧ (∀ (k : Fin 17) (i : Fin 693),
       b6Map k (singVec i) ≠ 0 ∧ hU (b6Map k (singVec i)) (b6Map k (singVec i)) = 0) := by
  exact ⟨CertificateChecks.Batch3080.singVec_ok, CertificateChecks.Batch3080.singVec_distinct, CertificateChecks.Batch3080.singLook_ok,
    CertificateChecks.Batch3080.b6Map_singVec_ok⟩

end Certificates
