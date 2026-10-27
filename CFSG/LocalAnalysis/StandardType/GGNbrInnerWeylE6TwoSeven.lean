module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoSevenFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Main

theorem largeEvenLabelAll_noLine_e6_two_seven {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLine 7 0 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn1⟩ := h
  dsimp only at htag hn1
  subst htag
  subst hn1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa only [pow_one] using hK
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  intro hs hna
  exact ggTorusNoLine_of_scNoLine Nat.prime_seven (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK hφ)
    (ggCenterPrime_recipe_E6_two hK2 Nat.prime_seven)
    (ggSCNoLine_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
      (ggSCNoLine_adjoint_E6_two_seven hK2 0))

theorem largeEvenLabelAll_noLine_e6_two_seven_or {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift 7 r R ∨ r = 0) ∧ GGTorusNoLine 7 r R I :=
  (largeEvenLabelAll_noLine_e6_two_seven hlab h).mono fun _ _ _ _ hn hs hna =>
    ⟨0, Or.inr rfl, hn hs hna⟩

end Main

end CFSG.StandardType

end
