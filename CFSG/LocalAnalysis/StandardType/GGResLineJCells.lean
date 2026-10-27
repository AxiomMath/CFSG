module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResLineJCell (T : GGResLineJType) (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G), GGResHyp 3 B Bs x L D J y K → ∀ [Fact (Nat.Prime 3)],
    GGResLineJDatum 3 Bs J T → GGInnerDiagOnLabel (fun _ lab => S lab) 3 Bs J →
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel T lab ∧
        GGHasLabel lab (J ⧸ Subgroup.center J)

theorem ggInnerDiagOnLabel_mono_lambda2 {G : Type} [Group G]
    {S S' : LargeEvenLabel → Prop} {Bs J : Subgroup G}
    (hS : ∀ lab, LargeEvenInLambda2 lab → S lab → S' lab)
    (h : GGInnerDiagOnLabel (fun _ lab => S lab) 3 Bs J) :
    GGInnerDiagOnLabel (fun _ lab => S' lab) 3 Bs J := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  exact ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun R _ I F hP => by
      obtain ⟨hs, hna, θ, hcont⟩ := hP
      exact ⟨hs, hna, θ, ⟨hS lab hlab hcont.1, hcont.2⟩⟩) hraw⟩

theorem GGResLineJCell.mono {T : GGResLineJType} {S S' : LargeEvenLabel → Prop}
    (h : GGResLineJCell T S) (hS : ∀ lab, LargeEvenInLambda2 lab → S' lab → S lab) :
    GGResLineJCell T S' := by
  intro G _ _ B Bs x L D J y K hH _ hD hM
  exact h G B Bs x L D J y K hH hD (ggInnerDiagOnLabel_mono_lambda2 hS hM)

theorem GGResLineJCell.at {T : GGResLineJType} {S : LargeEvenLabel → Prop}
    (h : GGResLineJCell T S) {lab0 : LargeEvenLabel} (hS : S lab0) :
    GGResLineJCell T fun lab => lab = lab0 :=
  h.mono fun lab _ hlab => by rw [show lab = lab0 from hlab]; exact hS

theorem GGResLineJCell.of_forall_eq {T : GGResLineJType} {S : LargeEvenLabel → Prop}
    (h : ∀ lab0, LargeEvenInLambda2 lab0 → S lab0 → GGResLineJCell T fun lab => lab = lab0) :
    GGResLineJCell T S := by
  intro G _ _ B Bs x L D J y K hH _ hD hM
  obtain ⟨hperf, lab0, hlab0, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
  refine h lab0 hlab0 hP.1 G B Bs x L D J y K hH hD ⟨hperf, lab0, hlab0, ?_⟩
  exact largeEvenRawDatum_mono (fun R _ I F hQ => by
    obtain ⟨hs, hna, θ, hcont⟩ := hQ
    exact ⟨hs, hna, θ, ⟨rfl, hcont.2⟩⟩) hraw

theorem ggResLineJCell_of_label (T : GGResLineJType) :
    GGResLineJCell T (ggResLineJLabel T) := by
  intro G _ _ B Bs x L D J y K hH _ hD hM
  obtain ⟨-, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
  refine ⟨lab, hlab, hP.1, ?_⟩
  refine largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F ⟨-, -, θ, -⟩
  exact ⟨θ⟩

@[expose] def ggResLineJOpenA2 (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1

end CFSG.StandardType

end
