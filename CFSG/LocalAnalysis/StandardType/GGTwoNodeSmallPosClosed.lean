module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosFactsC
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeyl
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyT
public import Certificates.Data.CFSGNative.TwoNodeSmall.CheckPos
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyK

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem verifyPos_elim {Q : SPt}
    [Fact Q.pt.p.Prime] {w : PWitness} (h : verifyPos Q w = true) {C : Prop}
    (hF : Q.pt.AlphaFixed → C) (hS : ¬ Q.pt.WF → C) (hT : (∃ g ∈ Q.pt.group, IsTransv g) → C)
    (hC : Q.pt.CycleAt Q.s → C) (hO : Q.pt.bound < Nat.card Q.pt.group → C)
    (hW : CFSG.StandardType.ZS.LinWeyl Q.pt.p Q.pt.group → C) : C := by
  cases w with
  | fixed => exact hF (verifyF_sound h)
  | self_ => exact hS (verifyS_sound h)
  | transv t =>
    simp only [verifyPos, Bool.and_eq_true] at h
    exact hT (verifyT_sound (wfCheck_sound h.1) h.2)
  | cycle c =>
    simp only [verifyPos, Bool.and_eq_true] at h
    exact hC (verifyC_sound (wfCheck_sound h.1) h.2)
  | order o =>
    simp only [verifyPos, Bool.and_eq_true] at h
    exact hO (verifyO_sound (wfCheck_sound h.1) h.2)
  | weyl c =>
    simp only [verifyPos, Bool.and_eq_true] at h
    exact hW (verifyWPos_sound (wfCheck_sound h.1) h.2)

theorem check1Pos_elim {Q : SPt}
    [Fact Q.pt.p.Prime] (h : check1Pos Q = true) {C : Prop}
    (hF : Q.pt.AlphaFixed → C) (hS : ¬ Q.pt.WF → C) (hT : (∃ g ∈ Q.pt.group, IsTransv g) → C)
    (hC : Q.pt.CycleAt Q.s → C) (hO : Q.pt.bound < Nat.card Q.pt.group → C)
    (hW : CFSG.StandardType.ZS.LinWeyl Q.pt.p Q.pt.group → C) : C := by
  unfold check1Pos at h
  split at h
  · exact verifyPos_elim h hF hS hT hC hO hW
  · exact absurd h (by simp)

theorem verifyExcl_elim {Q : SPt} [Fact Q.pt.p.Prime] {w : PWitness} (h : verifyExcl Q w = true) {C : Prop}
    (hF : Q.pt.AlphaFixed → C) (hS : ¬ Q.pt.WF → C) (hT : (∃ g ∈ Q.pt.group, IsTransv g) → C)
    (hC : Q.pt.CycleAt Q.s → C) : C := by
  cases w with
  | fixed => exact hF (verifyF_sound h)
  | self_ => exact hS (verifyS_sound h)
  | transv t =>
    simp only [verifyExcl, verifyPos, Bool.and_eq_true] at h
    exact hT (verifyT_sound (wfCheck_sound h.1) h.2)
  | cycle c =>
    simp only [verifyExcl, verifyPos, Bool.and_eq_true] at h
    exact hC (verifyC_sound (wfCheck_sound h.1) h.2)
  | order o => simp [verifyExcl] at h
  | weyl c => simp [verifyExcl] at h

theorem check1Excl_elim {Q : SPt} [Fact Q.pt.p.Prime] (h : check1Excl Q = true) {C : Prop}
    (hF : Q.pt.AlphaFixed → C) (hS : ¬ Q.pt.WF → C) (hT : (∃ g ∈ Q.pt.group, IsTransv g) → C)
    (hC : Q.pt.CycleAt Q.s → C) : C := by
  unfold check1Excl at h
  split at h
  · exact verifyExcl_elim h hF hS hT hC
  · exact absurd h (by simp)

@[expose] def SPt.ClosedPosB (Q : SPt) [Fact Q.pt.p.Prime] : Prop :=
  Q.pt.AlphaFixed ∨ ¬ Q.pt.WF ∨ (∃ g ∈ Q.pt.group, IsTransv g) ∨ Q.pt.CycleAt Q.s ∨
    Q.pt.bound < Nat.card Q.pt.group ∨ CFSG.StandardType.ZS.LinWeyl Q.pt.p Q.pt.group

@[expose] def SPt.ClosedExcl (Q : SPt) [Fact Q.pt.p.Prime] : Prop :=
  Q.pt.AlphaFixed ∨ ¬ Q.pt.WF ∨ (∃ g ∈ Q.pt.group, IsTransv g) ∨ Q.pt.CycleAt Q.s

theorem check1Pos_closed {Q : SPt}
    [Fact Q.pt.p.Prime] (h : check1Pos Q = true) : Q.ClosedPosB :=
  check1Pos_elim h Or.inl (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h)))
    (fun h => Or.inr (Or.inr (Or.inr (Or.inl h)))) (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem check1Excl_closed {Q : SPt} [Fact Q.pt.p.Prime] (h : check1Excl Q = true) : Q.ClosedExcl :=
  check1Excl_elim h Or.inl (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h)))
    (fun h => Or.inr (Or.inr (Or.inr h)))

theorem posBCheck_iff : posBCheck () = true ↔ ∀ Q ∈ posBPts (), check1Pos Q = true := by
  simp [posBCheck, List.all_eq_true]

theorem exclCheck_iff : exclCheck () = true ↔ ∀ Q ∈ exclPts (), check1Excl Q = true := by
  simp [exclCheck, List.all_eq_true]

end CFSG.TwoNodeSmall
