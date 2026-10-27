module

public import CFSG.LieType.SemisimpleCentralizers.RegularARawTransport
public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers

theorem largeEvenLabelAll_A_fullFixedSolvable
    {lab : LargeEvenLabel} (htag : lab.tag = .A)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsPGroup p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E) := by
  have hlabel : (⟨.A, lab.rank, lab.n⟩ : LargeEvenLabel) = lab := by
    cases lab
    simpa using htag.symm
  have hdonor := largeEvenLabelAll_A_commonFixed_isSolvable
    (m := lab.rank) (n := lab.n) hp hpq
  rw [hlabel] at hdonor
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ (hdonor Q hQ)
  rintro R _ I F ⟨hQ, hsolv⟩
  refine ⟨hQ, ?_⟩
  intro E hEI hE hNPC
  apply hsolv E hEI hE
  have h := CFSG.hasNormalPComplement_of_equiv p
    ((_root_.commutator ↥(ggFixedSubgroup E)).equivMapOfInjective
      (ggFixedSubgroup E).subtype (ggFixedSubgroup E).subtype_injective) hNPC
  rwa [Subgroup.map_subtype_commutator] at h

theorem isSolvable_inf_centralizer_of_regular_A_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab.tag = .A ∧ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsPGroup p (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .A ∧ p ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsPGroup p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun _ _ hs => largeEvenLabelAll_A_fullFixedSolvable hs.1 hp hs.2)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hN, hEI, hE⟩, hrow⟩ := hP
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end CFSG.StandardType
