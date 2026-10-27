module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin

public section

open CFSG.EvenSporadicStandard.TwoHS Matrix

namespace CertificateChecks.Batch26420

open CFSG.EvenSporadicStandard.TwoHS Matrix

set_option maxHeartbeats 0

theorem shat_sub : ∀ s ∈ shatList, s ∈ q0List := by decide +kernel

theorem fix_t : ∀ A ∈ q0List, A *ᵥ tVec = tVec := by decide +kernel

theorem f_zero : (0 : V4) ∈ fVecs := by decide +kernel

theorem f_add : ∀ u ∈ fVecs, ∀ v ∈ fVecs, u + v ∈ fVecs := by decide +kernel

theorem f_two : ∀ v ∈ fVecs, v + v = 0 := by decide +kernel

theorem om_f : ∀ v : V4, v + v = 0 → v ∈ fVecs ∨ v - tVec ∈ fVecs := by decide +kernel

theorem om_card : (Finset.univ.filter fun v : V4 => v + v = 0).card = 16 := by decide +kernel

theorem om_list : ∀ v ∈ omList, v + v = 0 := by decide +kernel

theorem om_sq : ∀ v : V4, v + v = 0 → ∃ w, w + w = v := by decide +kernel

theorem zm_mem : zmVec ∈ fVecs := by decide +kernel

theorem zp_eq : zpVec = tVec + zmVec := by decide +kernel

theorem t_two : tVec + tVec = 0 := by decide +kernel

theorem zm_trans : ∀ w ∈ fVecs, w ≠ 0 → ∃ A ∈ q0List, A *ᵥ zmVec = w := by decide +kernel

theorem reps_mem : ∀ r ∈ reps, r ∈ q0List := by decide +kernel

theorem reps_spec : ∀ w ∈ fVecs, w ≠ 0 → ∃ r ∈ reps, r *ᵥ zpVec = tVec + w := by
  decide +kernel

theorem two_f : fVec + fVec = tVec := by decide +kernel

theorem neg_f : -fVec ≠ fVec := by decide +kernel

theorem sq_coset : ∀ v : V4, (∃ u ∈ fVecs, v + v = tVec + u) →
    ∃ u ∈ fVecs, (v - fVec) + (v - fVec) = u := by
  decide +kernel

end CertificateChecks.Batch26420

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26420 : Q0Facts :=
  { shat_sub := CertificateChecks.Batch26420.shat_sub, fix_t := CertificateChecks.Batch26420.fix_t,
    f_zero := CertificateChecks.Batch26420.f_zero, f_add := CertificateChecks.Batch26420.f_add, f_two := CertificateChecks.Batch26420.f_two,
    om_f := CertificateChecks.Batch26420.om_f, om_card := CertificateChecks.Batch26420.om_card, om_list := CertificateChecks.Batch26420.om_list,
    om_sq := CertificateChecks.Batch26420.om_sq, zm_mem := CertificateChecks.Batch26420.zm_mem, zp_eq := CertificateChecks.Batch26420.zp_eq,
    t_two := CertificateChecks.Batch26420.t_two, zm_trans := CertificateChecks.Batch26420.zm_trans,
    reps_mem := CertificateChecks.Batch26420.reps_mem, reps_spec := CertificateChecks.Batch26420.reps_spec,
    two_f := CertificateChecks.Batch26420.two_f, neg_f := CertificateChecks.Batch26420.neg_f, sq_coset := CertificateChecks.Batch26420.sq_coset }

end Certificates
