
module

public import CFSG.Sporadic.J4.QT2LocX0KCheckBase

public import CFSG.Sporadic.J4.QT2LocX0KNative
public meta import CFSG.Sporadic.J4.QT2LocX0KNative
public import Certificates.Certificate4013
public import Certificates.Certificate4013Base

public section

namespace CFSG.Sporadic.J4.QT2

set_option maxHeartbeats 0 in
theorem chkKAll_true : chkKAll = true :=
  Certificates.certificate4013

theorem chkKGens_true : chkKGens = true := by
  have h := chkKAll_true
  simp only [chkKAll, Bool.and_eq_true] at h
  exact h.1.1.1

theorem chkKOrb_true : chkKOrb = true := by
  have h := chkKAll_true
  simp only [chkKAll, Bool.and_eq_true] at h
  exact h.1.1.2

theorem chkKComm_true : chkKComm = true := by
  have h := chkKAll_true
  simp only [chkKAll, Bool.and_eq_true] at h
  exact h.1.2

theorem chkEStab_true : chkEStab = true := by
  have h := chkKAll_true
  simp only [chkKAll, Bool.and_eq_true] at h
  exact h.2

end CFSG.Sporadic.J4.QT2
