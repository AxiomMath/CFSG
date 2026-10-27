module

public import CFSG.OddTranspositions.PartThree.Nine.FinalMinus
public import CFSG.OddTranspositions.PartThree.Nine.FinalUnitary

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}


theorem minus_of_wcl_abelian (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hs : IsSimpleGroup (commutator G)) (h3 : Conclusion9_3 D hC)
    {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
    (h4 : Conclusion9_4 D hC T S) (h5 : Conclusion9_5 D hC T S)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    {U : Subgroup G} (hU : DeltaSetup hC T S U) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (hW : IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl z)) :
    ∃ f : ℕ, 2 ≤ f ∧
      Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSL2Model f) ∧
      Nonempty (↥(commutator G) ≃* PSL2Model (2 * f)) ∧ (commutator G).index = 2 := by
  rcases minus_or_unitary_of_wcl_abelian hC hH hs h3 h4 h5 hQ hU hzU hz1 hzS hW with
    h | ⟨n, hn, ⟨eH⟩, ⟨eK⟩, -, huK⟩
  · exact h
  · exact (false_of_commutator_mulEquiv_psu3 h3 h4 h5 hU hQ (by omega) eH eK huK).elim

end CFSG.OddTranspositions.PartThree.Nine
