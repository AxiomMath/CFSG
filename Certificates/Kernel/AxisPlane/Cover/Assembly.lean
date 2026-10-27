module

public import Certificates.Kernel.AxisPlane.Cover.R0
public import Certificates.Kernel.AxisPlane.Cover.R3
public import Certificates.Kernel.AxisPlane.Cover.R6
public import Certificates.Kernel.AxisPlane.Cover.R9
public import Certificates.Kernel.AxisPlane.Cover.W0
public import Certificates.Kernel.AxisPlane.Cover.W3
public import Certificates.Kernel.AxisPlane.Cover.W6
public import Certificates.Kernel.AxisPlane.Cover.W9
public import CFSG.Certificates.Kernel.AxisPlane.Two

public section

namespace CertificateChecks.KernelAP.Cover

open CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Cert CFSG.Monster.AxisCount.Native
  CFSG.KC.AxisPlane

@[expose] def CoverStmt (i : Fin 12) : Prop :=
  ((UA i).all Gen.isVis && (UB i).all Gen.isVis && (List.range (nW i)).all fun r =>
      (hW i r).all Gen.isVis && Cover.l2Word (hW i r) (lamW i r) == 63) = true ∧
    ∀ r < nW i,
      natOrbit #[Cover.wordRows (UA i), Cover.wordRows (UB i)] (lamW i r) ⊆ Set.Iio (2 ^ 24) ∧
      (natOrbit #[Cover.wordRows (UA i), Cover.wordRows (UB i)] (lamW i r)).ncard = sizeW i r ∧
      ∀ r' < nW i, r ≠ r' →
        Disjoint (natOrbit #[Cover.wordRows (UA i), Cover.wordRows (UB i)] (lamW i r))
          (natOrbit #[Cover.wordRows (UA i), Cover.wordRows (UB i)] (lamW i r'))

theorem cover_of {i : Fin 12} {rA rB lams sizes Ls Qs : List Nat} {opss Rss : List (List Nat)}
    (hw : (Cover.wordRows (UA i) == rA.toArray && Cover.wordRows (UB i) == rB.toArray &&
      ((UA i).all Gen.isVis && (UB i).all Gen.isVis && (List.range (nW i)).all fun r =>
        (hW i r).all Gen.isVis && Cover.l2Word (hW i r) (lamW i r) == 63)) = true)
    (C : PlanesChk opss [rA, rB] Ls Qs Rss lams sizes) (hm : opss.length = 2)
    (hl : (List.range (nW i)).map (lamW i) = lams)
    (hs : (List.range (nW i)).map (sizeW i) = sizes) : CoverStmt i := by
  rw [Bool.and_eq_true, Bool.and_eq_true] at hw
  obtain ⟨⟨hA, hB⟩, h2⟩ := hw
  exact ⟨h2, orbits_two C hm (eq_of_beq hA) (eq_of_beq hB) hl hs⟩

theorem cover0 : CoverStmt 0 := cover_of words0 R0.chk rfl lams0_eq sizes0_eq
theorem cover1 : CoverStmt 1 := cover_of words1 R1.chk rfl lams1_eq sizes1_eq
theorem cover2 : CoverStmt 2 := cover_of words2 R2.chk rfl lams2_eq sizes2_eq
theorem cover3 : CoverStmt 3 := cover_of words3 R3.chk rfl lams3_eq sizes3_eq
theorem cover4 : CoverStmt 4 := cover_of words4 R4.chk rfl lams4_eq sizes4_eq
theorem cover5 : CoverStmt 5 := cover_of words5 R5.chk rfl lams5_eq sizes5_eq
theorem cover6 : CoverStmt 6 := cover_of words6 R6.chk rfl lams6_eq sizes6_eq
theorem cover7 : CoverStmt 7 := cover_of words7 R7.chk rfl lams7_eq sizes7_eq
theorem cover8 : CoverStmt 8 := cover_of words8 R8.chk rfl lams8_eq sizes8_eq
theorem cover9 : CoverStmt 9 := cover_of words9 R9.chk rfl lams9_eq sizes9_eq
theorem cover10 : CoverStmt 10 := cover_of words10 R10.chk rfl lams10_eq sizes10_eq
theorem cover11 : CoverStmt 11 := cover_of words11 R11.chk rfl lams11_eq sizes11_eq

end CertificateChecks.KernelAP.Cover

end
