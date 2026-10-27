module

public import CFSG.Sporadic.J4.QT2LocVLNative
public meta import CFSG.Sporadic.J4.QT2LocVLNative
public import Certificates.Certificate4011
public meta import Std.Data.HashSet
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.J4.QT2

set_option maxHeartbeats 0 in
theorem chkVlAll_true : chkVlAll = true :=
  Certificates.certificate4011

theorem chkVlLifts_true : chkVlLifts = true := by
  have h := chkVlAll_true
  simp only [chkVlAll, Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem chkVlLiftWf_true : chkVlLiftWf = true := by
  have h := chkVlAll_true
  simp only [chkVlAll, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem chkVlEta_true : chkVlEta = true := by
  have h := chkVlAll_true
  simp only [chkVlAll, Bool.and_eq_true] at h
  exact h.1.1.2

theorem chkVlGroups_true : chkVlGroups = true := by
  have h := chkVlAll_true
  simp only [chkVlAll, Bool.and_eq_true] at h
  exact h.1.2

end CFSG.Sporadic.J4.QT2
