module

public import CFSG.Sporadic.J4.QT2LocX0Native
public meta import CFSG.Sporadic.J4.QT2LocX0Native
public import CFSG.Sporadic.J4.QT2LocX0CheckInputs
public import Certificates.Certificate4027

public section

namespace CFSG.Sporadic.J4.QT2

theorem chkX0All_true : chkX0All = true :=
  Certificates.certificate4027

theorem chkX0Gens_true : chkX0Gens = true := by
  have h := chkX0All_true
  simp only [chkX0All, Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem chkX0Orb_true : chkX0Orb = true := by
  have h := chkX0All_true
  simp only [chkX0All, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem chkX0Conj_true : chkX0Conj = true := by
  have h := chkX0All_true
  simp only [chkX0All, Bool.and_eq_true] at h
  exact h.1.1.2

theorem chkX0Invs_true : chkX0Invs = true := by
  have h := chkX0All_true
  simp only [chkX0All, Bool.and_eq_true] at h
  exact h.1.2

theorem chkX0Pts_true : chkX0Pts = true := by
  have h := chkX0All_true
  simp only [chkX0All, Bool.and_eq_true] at h
  exact h.2

end CFSG.Sporadic.J4.QT2
