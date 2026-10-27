module

public import CFSG.LocalAnalysis.StandardType.GGDepED4PrimeJ
public import CFSG.LocalAnalysis.StandardType.GGTWZKLinear
public import CFSG.LocalAnalysis.StandardType.GGTWZKUnitary
public import CFSG.LocalAnalysis.StandardType.GGTWRowData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem not_ggResSideDatum_of_linear_of_label_D4
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hp : p = 3) (hH : GGResHyp p B Bs x L D J y K) (hr : 4 ≤ r)
    (hpq : p ∣ 2 ^ f - 1) (hKΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hKHas : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJHas : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .D) (hJrank : labJ.rank = 4)
    (hSide : GGResSideDatum p Bs K J) : False := by
  subst p
  have hJK := J_le_K_of_label_D4 hLB hH hJΛ hJtag hJrank hJHas
  obtain ⟨hJlinear, hΛlinear⟩ :=
    ggHasLabel_typeA_of_large_linear_side hRig hH hr hpq hKΛ hKHas hJK hSide
  have hiso := hRig labJ ⟨.A, r - 1, f⟩ _ hJΛ hΛlinear hJHas hJlinear
  have hcanon : labJ = ⟨.D, 4, labJ.n⟩ := by
    cases labJ
    simp_all
  have heq := ggTWR_iso_eq_D4 hiso hcanon
  have htag := congrArg LargeEvenLabel.tag heq
  simp only [hJtag, LargeEvenLabel.tag] at htag
  cases htag

theorem not_ggResSideDatum_of_unitary_of_label_D4
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hp : p = 3) (hH : GGResHyp p B Bs x L D J y K)
    (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hKΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hKHas : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJHas : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .D) (hJrank : labJ.rank = 4)
    (hSide : GGResSideDatum p Bs K J) : False := by
  subst p
  have hJK := J_le_K_of_label_D4 hLB hH hJΛ hJtag hJrank hJHas
  obtain ⟨hJunitary, hΛunitary⟩ :=
    ggHasLabel_twA_of_large_unitary_side hRig hH hr hr5 hpq hpd hKHas hKΛ hSide hJK
  have hiso := hRig labJ ⟨.twA, r - 1, f⟩ _ hJΛ hΛunitary hJHas hJunitary
  have hcanon : labJ = ⟨.D, 4, labJ.n⟩ := by
    cases labJ
    simp_all
  have heq := ggTWR_iso_eq_D4 hiso hcanon
  have htag := congrArg LargeEvenLabel.tag heq
  simp only [hJtag, LargeEvenLabel.tag] at htag
  cases htag

theorem not_ggResSideDatum_of_unitary_six_of_label_D4
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {f : ℕ} (hH : GGResHyp 3 B Bs x L D J y K) (hpq : 3 ∣ 2 ^ f + 1)
    (hKΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hKHas : GGHasLabel ⟨.twA, 5, f⟩ (K ⧸ Subgroup.center K))
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJHas : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .D) (hJrank : labJ.rank = 4)
    (hSide : GGResSideDatum 3 Bs K J) : False := by
  have hpJ3 := three_dvd_card_of_hasLabel_D4 hJΛ hJtag hJrank hJHas
  have hiso := ggLabelIso_twA_of_unitary_six_side
    hRig hLB hH hKHas hKΛ hpq hpJ3 hJΛ hJHas hSide
  have hcanon : labJ = ⟨.D, 4, labJ.n⟩ := by
    cases labJ
    simp_all
  have heq := ggTWR_iso_eq_D4 hiso hcanon
  have htag := congrArg LargeEvenLabel.tag heq
  simp only [hJtag, LargeEvenLabel.tag] at htag
  cases htag

end CFSG.StandardType

end
