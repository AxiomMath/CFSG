module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBChecks
import CFSG.Certificates.Kernel.M3BFib.WordSound
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

namespace CertificateChecks.Batch136200

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF CFSG.KC.M3BF

private theorem chkA : (compK LpM (powK LpM DaK 55) DaK == oneK) = true := by quickRfl

private theorem chkB : (compK LpM (powK LpM DbK 21) DbK == oneK) = true := by quickRfl

private theorem adEq_of_toD {D D' : _root_.Timmesfeld.M3B.AD} (h : toD D = toD D') :
    _root_.Timmesfeld.M3B.adEq D D' = true := by
  unfold _root_.Timmesfeld.M3B.adEq _root_.Timmesfeld.M3B.eeq
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine ⟨fun i _ => ⟨fun j _ => ?_, ?_⟩, toZ_injective h2⟩
  · have hi := congrArg Prod.fst (congrFun h1 i)
    exact toZ_injective (congrFun hi j)
  · have hi := congrArg Prod.snd (congrFun h1 i)
    exact toZ_injective hi

private theorem letter_inv {D : PD} {E : _root_.Timmesfeld.M3B.AD} (h : GoodPD D ∧ dK D = toD E)
    (k : ℕ) (hk : (compK LpM (powK LpM D k) D == oneK) = true) :
    _root_.Timmesfeld.M3B.adEq (_root_.Timmesfeld.M3B.comp (_root_.Timmesfeld.M3B.B0 ())
      (_root_.Timmesfeld.M3B.adPow (_root_.Timmesfeld.M3B.B0 ()) E k) E)
      _root_.Timmesfeld.M3B.adOne = true := by
  refine adEq_of_toD ?_
  rw [← (comp_sound (pow_sound h k) h).2, beq_iff_eq.mp hk, one_sound.2]

private theorem check_certificate : letterInvCheck () = true := by
  unfold letterInvCheck
  rw [LA_getD_two, LA_getD_three, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · exact letter_inv a_sound 55 chkA
  · exact letter_inv b_sound 21 chkB

end CertificateChecks.Batch136200

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF in
theorem certificate136200 : letterInvCheck () = true := by
  exact CertificateChecks.Batch136200.check_certificate

end Certificates
