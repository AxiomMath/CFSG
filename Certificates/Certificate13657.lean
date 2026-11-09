module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData

public section

open CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace CertificateChecks.Batch13657

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg

set_option maxHeartbeats 0 in
theorem sc_orbit : orbitCheck3 .E6 e6ThreeReps e6ThreeOrbit = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sc_stab0 : (e6ThreeStab0.check e6Certificate &&
    (e6ThreeStab0.passing e6Certificate).all fun t =>
      t == List.range Tag.E6.rank || e6ScTest e6Certificate e6ThreeStab0.vec t) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sc_stab1 : (e6ThreeStab1.check e6Certificate &&
    (e6ThreeStab1.passing e6Certificate).all fun t =>
      t == List.range Tag.E6.rank || e6ScTest e6Certificate e6ThreeStab1.vec t) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sc_stab2 : (e6ThreeStab2.check e6Certificate &&
    (e6ThreeStab2.passing e6Certificate).all fun t =>
      t == List.range Tag.E6.rank || e6ScTest e6Certificate e6ThreeStab2.vec t) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sc_stab3 : (e6ThreeStab3.check e6Certificate &&
    (e6ThreeStab3.passing e6Certificate).all fun t =>
      t == List.range Tag.E6.rank || e6ScTest e6Certificate e6ThreeStab3.vec t) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sc_stab4 : (e6ThreeStab4.check e6Certificate &&
    (e6ThreeStab4.passing e6Certificate).all fun t =>
      t == List.range Tag.E6.rank || e6ScTest e6Certificate e6ThreeStab4.vec t) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sc_stab5 : (e6ThreeStab5.check e6Certificate &&
    (e6ThreeStab5.passing e6Certificate).all fun t =>
      t == List.range Tag.E6.rank || e6ScTest e6Certificate e6ThreeStab5.vec t) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sc_stab6 : (e6ThreeStab6.check e6Certificate &&
    (e6ThreeStab6.passing e6Certificate).all fun t =>
      t == List.range Tag.E6.rank || e6ScTest e6Certificate e6ThreeStab6.vec t) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sc_stab7 : (e6ThreeStab7.check e6Certificate &&
    (e6ThreeStab7.passing e6Certificate).all fun t =>
      t == List.range Tag.E6.rank || e6ScTest e6Certificate e6ThreeStab7.vec t) = true := by
  decide +kernel

private theorem e6_three_sc_check_0 : e6ThreeScCheck () = true := by
  unfold e6ThreeScCheck e6ThreeStabs
  simp only [List.all_cons, List.all_nil, sc_orbit, sc_stab0, sc_stab1, sc_stab2, sc_stab3, sc_stab4, sc_stab5, sc_stab6,
    sc_stab7, Bool.and_true, Bool.true_and, Bool.and_self]

end CertificateChecks.Batch13657

namespace Certificates

open CertificateChecks

theorem certificate13657 : CFSG.HardMathSupport.Timmesfeld.CrossChar.e6ThreeScCheck () = true := by
  exact CertificateChecks.Batch13657.e6_three_sc_check_0

end Certificates
