
module

public import Certificates.Certificate946008Base
import all Certificates.Certificate946008Base

import CFSG.Certificates.Kernel.P946008.Sound
import Certificates.Kernel.P946008.Checks

public section

public section

namespace Certificates

open Certificates CFSG.KC.P946008 CFSG.RankThree.GF2n.Parrott

open CFSG.RankThree.GF2n.Parrott in
theorem certificate946008 : ExtraspecialFacts := by
  have h1 := ch946008s1
  have h2 := ch946008s2
  have h3 := ch946008s3
  have h4 := ch946008s4
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2 h3 h4
  have f1 := liftFacts_of ch946008m1a ch946008m1b ch946008m1c h1.1
  have f2 := liftFacts_of ch946008m2a ch946008m2b ch946008m2c h2.1
  have f3 := liftFacts_of ch946008m3a ch946008m3b ch946008m3c h3.1
  have f4 := liftFacts_of ch946008m4a ch946008m4b ch946008m4c h4.1.1.1
  refine ⟨f1, f2, f3, f4, f1.noncomm, f2.noncomm, ?_, f3.noncomm, f4.noncomm, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [fixedCentral_eq]
    exact h3.2
  · rw [invMaskCount_eq]
    exact h4.1.1.2
  · rw [fixedCentreCard_eq]
    exact h4.1.2
  · rw [fixedOrderFour_eq]
    exact h1.2
  · rw [fixedOrderFour_eq]
    exact h2.2
  · rw [fixedOrderFour_eq]
    exact h4.2

end Certificates
