module

public import CFSG.Sporadic.J4.QT2LocHNative
public meta import CFSG.Sporadic.J4.QT2LocHNative
public import Certificates.Certificate4007
public meta import Std.Data.HashSet
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.J4.QT2

set_option maxHeartbeats 0 in
theorem chkAll_true : chkAll = true :=
  Certificates.certificate4007

theorem chkIset_true : chkIset = true := by
  have h := chkAll_true
  simp only [chkAll, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1

theorem chkDuad_true : chkDuad = true := by
  have h := chkAll_true
  simp only [chkAll, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.2

theorem chkV_true : chkV = true := by
  have h := chkAll_true
  simp only [chkAll, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.2

theorem chkLines_true : chkLines = true := by
  have h := chkAll_true
  simp only [chkAll, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem chkCaseI_true : ∀ k ∈ [1, 2, 3, 4], chkCaseI k = true := by
  have h := chkAll_true
  simp only [chkAll, Bool.and_eq_true] at h
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact h.1.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.1.2
  · exact h.1.1.1.1.1.2
  · exact h.1.1.1.1.2

theorem chkCaseII_true : ∀ k ∈ [1, 2, 3, 4], chkCaseII k = true := by
  have h := chkAll_true
  simp only [chkAll, Bool.and_eq_true] at h
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact h.1.1.1.2
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

end CFSG.Sporadic.J4.QT2
