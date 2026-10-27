module

public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.KGCenterCoprime
public import CFSG.LocalAnalysis.StandardType.GGOddCenterPrimeLabel
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTWZKPrimeJ
public import CFSG.LocalAnalysis.StandardType.GGTWZKLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem not_ggResHyp_of_smallRank_label
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {labK : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 labK) (hLab : GGHasLabel labK (K ⧸ Subgroup.center K))
    (hsmall : GGRootGenSmallRankLabel p labK) : False := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hInn := ggInnerDiagOn_relabel hRig (hH.2.2.1.2 y K hH.2.2.2.2.1) hΛ hLab
  have hInn' : GGInnerDiagOnLabel (fun _ lab => lab = labK) p Bs K := hInn
  have hmk : GGInnerDiagOnLabel GGRootGenSmallRankLabel p Bs K :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => by
      obtain ⟨heq, hN, hact⟩ := hP
      exact ⟨heq.symm ▸ hsmall, hN, hact⟩) hInn'
  exact not_largeEvenMarking_smallRank hp hp2
    (ggInnerDiagOnLabel_nbr_pRank_ge_three hH.1 hH.2.2.2.2.1 hmk)

theorem GGResHyp.J_le_K_of_typeA
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {labJ : LargeEvenLabel}
    (hJΛ : LargeEvenInLambda2 labJ) (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .A ∨ labJ.tag = .twA) (hpJ : p ∣ labJ.rank + 3) : J ≤ K := by
  exact le_of_ggNbr hLB hH.1.1 hH.1.2.2
    (card_J_dvd_of_ggResHyp hH hJΛ hJLab hJtag hpJ) hH.2.2.2.2.1

theorem not_ggResSideDatum_of_linear_centerPrime
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hr : 4 ≤ r)
    (hpq : p ∣ 2 ^ f - 1) (hpd : p ∣ r + 1)
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .A ∨ labJ.tag = .twA) (hpJ : p ∣ labJ.rank + 3)
    (hSide : GGResSideDatum p Bs K J) : False := by
  exact not_ggResSideDatum_of_linear_centerPrime_of_le hRig hH hr hpq hpd hΛ hLab
    hJΛ hJLab hpJ (hH.J_le_K_of_typeA hLB hJΛ hJLab hJtag hpJ) hSide

section Certs

theorem not_dvd_card_center_of_resHyp_of_not_oddCenterPrimeLabel
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hLab : GGHasLabel lab (K ⧸ Subgroup.center K))
    (h : ¬ GGOddCenterPrimeLabel p lab) : ¬ p ∣ Nat.card (Subgroup.center K) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hperf : commutator K = ⊤ := (hH.2.2.1.2 y K hH.2.2.2.2.1).1
  exact not_dvd_card_center_of_torsBound_eq_one (Fact.out : p.Prime) hΛ hperf hLab
    (torsBound_mark_eq_one_of_not_oddCenterPrimeLabel (Fact.out : p.Prime) hp2 h)

theorem oddCenterPrimeLabel_of_resHyp_of_dvd_card_center
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (hLab : GGHasLabel lab (K ⧸ Subgroup.center K))
    (hd : p ∣ Nat.card (Subgroup.center K)) : GGOddCenterPrimeLabel p lab := by
  by_contra h
  exact not_dvd_card_center_of_resHyp_of_not_oddCenterPrimeLabel hH hΛ hLab h hd

end Certs

end CFSG.StandardType

end
