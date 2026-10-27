module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGRCCaseI
public import CFSG.LocalAnalysis.StandardType.GGRCCaseII

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tablePRow_of_resHyp {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hTP : GGNbrTablePConfig p B Bs x L D J)
    (hH : GGResHyp p B Bs x L D J y K) {labJ labK : LargeEvenLabel}
    (hJ : LargeEvenInLambda2 labJ) (hK : LargeEvenInLambda2 labK)
    (hlJ : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hlK : GGHasLabel labK (K ⧸ Subgroup.center K)) :
    ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
      GGTablePRow p labJ' labK' ∧ GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧
      GGHasLabel labK' (K ⧸ Subgroup.center K) :=
  hTP hH.1 hH.2.2.1 y K hH.2.2.2.2.1 labJ labK hJ hK hlJ hlK

theorem tablePRow_E6_field {p : ℕ} {J X : LargeEvenLabel} (h : GGTablePRow p J X)
    (hJ : J.tag = .A ∨ J.tag = .twA) (hJr : J.rank = 5) (hX : X.tag = .E6 ∨ X.tag = .twE6) :
    X.n = J.n ∨ (J.tag = .twA ∧ X.tag = .twE6 ∧ 3 * X.n = J.n) := by
  obtain ⟨tJ, rJ, nJ⟩ := J
  obtain ⟨tX, rX, nX⟩ := X
  simp only at hJ hJr hX ⊢
  subst hJr
  simp only [GGTablePRow, LargeEvenLabel.mk.injEq] at h
  rcases hJ with rfl | rfl <;> rcases hX with rfl | rfl <;> simp_all <;> omega

end CFSG.StandardType
