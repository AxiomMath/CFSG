module

public import Certificates.Data.CFSGNative.Th.Certificate
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.Sporadic.Th

open Native

@[expose] noncomputable def alphaT : Table := tblOfBytes (thBFS ()).count (thBFS ()).alpha

@[expose] noncomputable def betaT : Table := tblOfBytes (thBFS ()).count (thBFS ()).beta

@[expose] noncomputable def gplT : Table := tblOfBytes (thBFS ()).count (thBFS ()).par

@[expose] noncomputable def betaInvT : Table := invT (thBFS ()).count betaT

theorem thCertificate_parts {c : ℕ} (h : thCertificate c = true) :
    (thBFS ()).count = thN ∧ orbitOK (tblA ()) (tblB ()) wKey (thBFS ()) c = true ∧
      deltaOK (thBFS ()) = true ∧ invoOK (thBFS ()).count alphaT = true ∧
      order3OK (thBFS ()).count betaT = true ∧ invOK (thBFS ()).count betaT betaInvT = true ∧
      ap alphaT 0 = 1 ∧ ap betaT 0 = 2 ∧
      tableChecks (thBFS ()).count alphaT betaT betaInvT gplT c = true := by
  unfold thCertificate at h
  dsimp only at h
  split at h
  · exact absurd h Bool.false_ne_true
  · rename_i hc
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨hc.1.1, hc.1.2, hc.2, h1, h2, h3, h4, h5, h6⟩

end CFSG.Sporadic.Th

namespace CFSG.Sporadic.Th

open Native

@[expose] noncomputable def nT : ℕ := (thBFS ()).count

@[expose] noncomputable def mxT : Table := wordT nT (wordLetters alphaT betaT betaInvT) xWord

@[expose] noncomputable def myT : Table := wordT nT (wordLetters alphaT betaT betaInvT) yWord

@[expose] noncomputable def myiT : Table := invT nT myT

@[expose] noncomputable def mz0T : Table := wordT nT (wordLetters mxT myT myiT) zWord0

@[expose] noncomputable def mz1T : Table := wordT nT (wordLetters mxT myT myiT) zWord1

@[expose] noncomputable def mz0iT : Table := invT nT mz0T

@[expose] noncomputable def mz1iT : Table := invT nT mz1T

@[expose] noncomputable def q0T : Table × Table × Table := localBFS nT 1 mxT myT

@[expose] noncomputable def q1T : Table × Table := smallBFS 2 q1Size mz0T mz1T

@[expose] noncomputable def chainT : Chain :=
  ⟨q0T.2.1, q0T.2.2, letters mxT myiT, q1T.1, q1T.2, letters mz0iT mz1iT⟩

@[expose] noncomputable def compsT : Comps := components nT mxT myT

structure TableFacts (c : ℕ) : Prop where
  xInvo : invoOK nT mxT = true
  yOrd3 : order3OK nT myT = true
  x0 : ap mxT 0 = 0
  y0 : ap myT 0 = 0
  yInv : invOK nT myT myiT = true
  z0Inv : invOK nT mz0T mz0iT = true
  z1Inv : invOK nT mz1T mz1iT = true
  z01 : ap mz0T 1 = 1
  z11 : ap mz1T 1 = 1
  q0size : q0T.1.size = q0Size
  q1size : q1T.1.size = q1Size
  q0tree : treeOK nT q0Size 1 q0T.1 q0T.2.1 (ap q0T.2.2) mxT myT = true
  q1tree : treeOK nT q1Size 2 q1T.1 q1T.2 (findPt q1T.1) mz0T mz1T = true
  levelTwo : allIn 0 q1Size (fun k => levelTwoTest chainT (letters mz0T mz1T) 1 k &&
    levelTwoTest chainT (letters mz0T mz1T) 2 k) = true
  levelOne : parAll q0Size c (fun k =>
    (!reqTwo q0T.2.1 (fun j => ap q0T.2.2 (ap mxT (ap q0T.1 j))) 1 k ||
      levelOneTest q0T.1 chainT (letters mxT myT) 1 k) &&
    (!reqThree q0T.2.1 (fun j => ap q0T.2.2 (ap myT (ap q0T.1 j))) 2 k ||
      levelOneTest q0T.1 chainT (letters mxT myT) 2 k)) = true
  reps : compsT.reps.size = 11
  comp : compOK nT compsT mxT myT = true
  counts : (countLabels nT 11 compsT).toList = suborbitSizes
  global : globalChecks nT alphaT betaT betaInvT gplT chainT c = true

theorem tableChecks_parts {c : ℕ} (h : tableChecks nT alphaT betaT betaInvT gplT c = true) :
    TableFacts c := by
  unfold tableChecks at h
  dsimp only at h
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h1
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h2
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h3
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h4
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at h1 h2 h3 h4 h
  obtain ⟨⟨⟨hx, hy⟩, hx0⟩, hy0⟩ := h1
  obtain ⟨⟨⟨⟨hyi, hz0⟩, hz1⟩, hz01⟩, hz11⟩ := h2
  obtain ⟨⟨⟨hs0, hs1⟩, ht0⟩, ht1⟩ := h3
  obtain ⟨htwo, hone⟩ := h4
  obtain ⟨⟨⟨hreps, hcomp⟩, hcounts⟩, hglob⟩ := h
  exact ⟨hx, hy, hx0, hy0, hyi, hz0, hz1, hz01, hz11, hs0, hs1, ht0, ht1, htwo, hone, hreps, hcomp,
    hcounts, hglob⟩

end CFSG.Sporadic.Th
