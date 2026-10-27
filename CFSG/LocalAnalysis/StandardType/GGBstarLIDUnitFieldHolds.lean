module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaEq
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitField
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Subsets

theorem ggBstarInnerDiagLInputOn_of_le_unitDvdField {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvdFieldLabel p lab) : GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  by_cases hinn : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G)
  · exact ggInnerDiagOnLab_bstar_of_fieldInn
      (fun _ _ hp hlab hs => largeEvenLabelAll_unitDvdField_fieldInn hp hlab (hS _ _ hs)) hC hM hinn
  · obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
      (S := fun lab => S p lab)
      (P' := fun R _ I _ => (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ GGOutdiagOdd p R I)
      (fun lab hlab hs => largeEvenLabelAll_unitDvdField_torus_outdiag hp hlab (hS p lab hs))
      (fun _ _ _ _ _ _ hP => hP.1) hM
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, ⟨r, hr2, hlift⟩, hOD⟩ :=
      largeEvenRawDatum_exists hraw
    have hnc := UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift
    obtain ⟨-, -, -, -, -, hβ, hS', hst⟩ := hC.1
    rcases ggInnLocal_or_delta hp hβ.2.1 hS' hnc hL θ hBN h3 hOD hst.2.1 with hU | hT₀
    · exact absurd hU hinn
    · exact ggInnerDiagOnLab_bstar_of_moved hC hnc hM hT₀

theorem ggBstarInnerDiagLInputOn_of_le_unitDvdCoprimeN {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvdCoprimeNLabel p lab) : GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => S p lab)
    (P' := fun R _ _ _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R)
    (fun lab hlab hs => by
      have hs' := hS p lab hs
      intro Q hQ
      obtain ⟨hn, hd5, hpd, hpq, h63, hdq⟩ := unitDvdLabel_arith hp hlab hs'.1
      obtain ⟨⟨⟨ht, -, -, -⟩, -⟩, -⟩ := hs'
      obtain ⟨t, l, n⟩ := lab
      dsimp only at ht hn hd5 hpd hpq h63 hdq
      subst ht
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
      have hr2 : 2 ≤ ggUnitaryTorusRank p (l + 1) := by
        simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
        omega
      exact ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank p (l + 1), hr2,
        ggTorusLift_unitary hK hn (by omega) hdq hp hpq⟩⟩)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, -, r, hr2, hlift⟩ := largeEvenRawDatum_exists hraw
  exact CorFourTwoOpen.ggInnerDiagOnLab_bstar_of_pow
    (fun _ lab hp hlab hs => largeEvenLabelAll_pow_mem_vac hp hlab
      ⟨TableBU.ne_two_of_dvd_two_pow_add_one hlab.1 (hS _ _ hs).1.1.2.2.1,
        Or.inr (Or.inr ⟨Or.inl (hS _ _ hs).1.1.1, (hS _ _ hs).2⟩)⟩)
    hC (UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift) hM

theorem ggBstarInnerDiagLInputOn_of_not_unitDvdNo63 {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagLInputOn fun p lab => S p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) :
    GGBstarInnerDiagLInputOn S := by
  have hF := ggBstarInnerDiagLInputOn_of_le_unitDvdField
    (S := fun p lab => S p lab ∧ GGUnitDvdFieldLabel p lab) fun _ _ h => h.2
  have hN := ggBstarInnerDiagLInputOn_of_le_unitDvdCoprimeN
    (S := fun p lab => S p lab ∧ GGUnitDvdCoprimeNLabel p lab) fun _ _ h => h.2
  have h' := (hF.or hN).or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases hl : GGUnitDvdLabelNo63 p lab
    · rcases (ggUnitDvdLabelNo63_iff p lab).mp hl with hc | hf
      · exact Or.inl (Or.inr ⟨hlab, hc⟩)
      · exact Or.inl (Or.inl ⟨hlab, hf⟩)
    · exact Or.inr ⟨hlab, hl⟩
  · rcases hlab with (h1 | h1) | h1
    · exact h1.1
    · exact h1.1
    · exact h1.1

end Subsets

end CFSG.StandardType
