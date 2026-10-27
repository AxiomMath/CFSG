module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63R
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Act

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Certs

theorem largeEvenLabelAll_unitDvd63Field_fieldInn {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvd63FieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R ∧ GGFieldInnR p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩, -⟩ := h
  dsimp only at ht hpn hl5 hp3
  subst ht hl5 hp3
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (5 + 1, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hr : ggUnitaryTorusRank 3 (5 + 1) = 3 := by norm_num [ggUnitaryTorusRank]
  refine ⟨K, i1, i2, hK, ⟨hQ', 3, by norm_num, ?_, LID63.ggFieldInnR_unitary_63 hK hn hpn⟩⟩
  rw [← hr]
  exact ggTorusLift_unitary hK hn (by omega) hdq Nat.prime_three hpn

theorem largeEvenLabelAll_unitDvd63Field_torus_outdiag {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvd63FieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ GGOutdiagOdd p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩, -⟩ := h
  dsimp only at ht hpn hl5 hp3
  subst ht hl5 hp3
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (5 + 1, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hr : ggUnitaryTorusRank 3 (5 + 1) = 3 := by norm_num [ggUnitaryTorusRank]
  refine ⟨K, i1, i2, hK, ⟨hQ', ⟨3, by norm_num, ?_⟩,
    InndiagSU.ggOutdiagOdd_unitary hK hn (by omega) (fun ⟨h1, h2⟩ => hdq (by rw [h1, h2])) 3⟩⟩
  rw [← hr]
  exact ggTorusLift_unitary hK hn (by omega) hdq Nat.prime_three hpn

theorem ggBstarInnerDiagLInputOn_of_le_unitDvd63Field {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvd63FieldLabel p lab) : GGBstarInnerDiagLInputOn S := by
  intro G _ _ p B Bs x L D J hC hM
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  by_cases hinn : ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G)
  · exact ggInnerDiagOnLab_bstar_of_fieldInn
      (fun _ _ _ hlab hs => largeEvenLabelAll_unitDvd63Field_fieldInn hlab (hS _ _ hs)) hC hM hinn
  · obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
      (S := fun lab => S p lab)
      (P' := fun R _ I _ => (∃ r, 2 ≤ r ∧ GGTorusLift p r R) ∧ GGOutdiagOdd p R I)
      (fun lab hlab hs => largeEvenLabelAll_unitDvd63Field_torus_outdiag hlab (hS p lab hs))
      (fun _ _ _ _ _ _ hP => hP.1) hM
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBN, h3⟩, ⟨r, hr2, hlift⟩, hOD⟩ :=
      largeEvenRawDatum_exists hraw
    have hnc := UnitTB.exists_noncyclic_of_torusLift hp hr2 hL θ hlift
    obtain ⟨-, -, -, -, -, hβ, hS', hst⟩ := hC.1
    rcases ggInnLocal_or_delta hp hβ.2.1 hS' hnc hL θ hBN h3 hOD hst.2.1 with hU | hT₀
    · exact absurd hU hinn
    · exact ggInnerDiagOnLab_bstar_of_moved hC hnc hM hT₀

theorem ggBstarInnerDiagLInputOn_unitDvd63Field_holds :
    GGBstarInnerDiagLInputOn GGUnitDvd63FieldLabel :=
  ggBstarInnerDiagLInputOn_of_le_unitDvd63Field fun _ _ h => h

theorem ggTableBCxInputOn_of_not_unitDvd63_holds {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63Label p lab) :
    GGTableBCxInputOn S :=
  ggTableBCxInputOn_of_not_unitDvd63 ggBstarInnerDiagLInputOn_unitDvd63Field_holds h

theorem ggTableBModuleInputOn_of_not_unitDvd63_holds {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63Label p lab) :
    GGTableBModuleInputOn S :=
  ggTableBModuleInputOn_of_not_unitDvd63 ggBstarInnerDiagLInputOn_unitDvd63Field_holds h

theorem ggTableBActionInputOn_of_not_unitDvd63_holds {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63Label p lab) :
    GGTableBActionInputOn S :=
  ggTableBActionInputOn_of_not_unitDvd63 ggBstarInnerDiagLInputOn_unitDvd63Field_holds h

end Certs

end CFSG.StandardType

end
