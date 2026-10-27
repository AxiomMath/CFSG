module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Eight
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Nine
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418PSL2
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418SylowCenter
public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421Holds
public import CFSG.Quasithin.Background.F6W16Wreath
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418CharTwo

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace Insp15418

theorem dihedral_four_central : ∀ a b : DihedralGroup 4, (∀ x, a * x = x * a) →
    (∀ x, b * x = x * b) → a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b := by
  decide

theorem wreath_central : ∀ a : F6.WreathRes.Z4WrZ2, (∀ x, a * x = x * a) → a ^ 2 = 1 →
    a = 1 ∨ a = ⟨fun _ => Multiplicative.ofAdd 2, 1⟩ := by
  decide

theorem wreath_central_unique : ∀ a b : F6.WreathRes.Z4WrZ2, (∀ x, a * x = x * a) →
    (∀ x, b * x = x * b) → a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b := by
  intro a b ha hb ha2 hb2 ha1 hb1
  rcases wreath_central a ha ha2 with h | h
  · exact absurd h ha1
  rcases wreath_central b hb hb2 with h' | h'
  · exact absurd h' hb1
  rw [h, h']

end Insp15418

open Insp15418

namespace InspectionData15418

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ S T Z : Subgroup G}
  (d : InspectionData15418 I G₁ G₂ S T Z)
include d

theorem commInf_of_not_charTwo (hc : ¬ CharTwo I) (hF618 : F6.TheoremF618Cat)
    (hN1 : SylowCenterCyclic15418) (hN2 : ComponentIndexTwo15418)
    (hN3 : InvolutionCentralizer15418) :
    CommInf ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) := by
  set H₁ := (G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) with hH₁
  set H₂ := (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) with hH₂
  have hT : IsGoldschmidtTriple H₁ H₂ := d.isGoldschmidtAmalgam.2.toIsGoldschmidtTriple
  have eT₁₂ : ↥(H₁ ⊓ H₂) ≃* ↥(H₂ ⊓ H₁) := MulEquiv.subgroupCongr (inf_comm H₁ H₂)
  have hcenter : (∀ Q : Sylow 2 (↥I ⧸ CFSG.pPrimeCore 3 ↥I),
      IsCyclic ↥(Subgroup.center ↥(Q : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I)))) → False := by
    intro h
    obtain ⟨Q, hQ⟩ := hT.sylow
    have hQc := h Q
    rw [hQ] at hQc
    exact d.false_of_isCyclic_center hc hQc
  rcases d.f618 hF618 with h | h
  · rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · exact commInf_of_caseOne h1
    · exact commInf_of_caseTwo hT h2
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨e⟩, -⟩ := h3
      exact (d.false_of_mulEquiv hc e Insp15418.dihedral_four_central).elim
    · exact commInf_of_caseFour h4
    · obtain ⟨-, ⟨e⟩, -⟩ := h5
      exact (d.false_of_mulEquiv hc e Insp15418.dihedral_four_central).elim
    · obtain ⟨-, ⟨e⟩, -⟩ := h6
      exact (d.false_of_mulEquiv hc e Insp15418.dihedral_four_central).elim
    · obtain ⟨-, ⟨e⟩, -⟩ := h7
      exact (d.false_of_mulEquiv hc e Insp15418.dihedral_four_central).elim
    · obtain ⟨hD, ⟨eT⟩, ⟨e₁⟩, -⟩ := h8
      exact (d.false_of_caseEight hN2 hc hD eT e₁).elim
    · obtain ⟨hD, -⟩ := h9
      exact (d.false_of_caseNine hN2 hN3 hc hD).elim
    · obtain ⟨-, ⟨e⟩, -⟩ := h10
      exact (d.false_of_mulEquiv hc e Insp15418.wreath_central_unique).elim
    · obtain ⟨⟨p, hp, hD⟩, -⟩ := h11
      exact (hcenter fun Q => hN1 _ (Or.inr (Or.inr ⟨p, hp, hD⟩)) Q).elim
    · obtain ⟨hD, -⟩ := h12
      exact (hcenter fun Q => hN1 _ (Or.inl hD) Q).elim
    · obtain ⟨hD, -⟩ := h13
      exact (hcenter fun Q => hN1 _ (Or.inr (Or.inl hD)) Q).elim
  · rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · exact commInf_comm.mpr (commInf_of_caseOne h1)
    · exact commInf_of_caseTwo hT h2
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨e⟩, -⟩ := h3
      exact (d.false_of_mulEquiv hc (eT₁₂.trans e) Insp15418.dihedral_four_central).elim
    · exact commInf_comm.mpr (commInf_of_caseFour h4)
    · obtain ⟨-, ⟨e⟩, -⟩ := h5
      exact (d.false_of_mulEquiv hc (eT₁₂.trans e) Insp15418.dihedral_four_central).elim
    · obtain ⟨-, ⟨e⟩, -⟩ := h6
      exact (d.false_of_mulEquiv hc (eT₁₂.trans e) Insp15418.dihedral_four_central).elim
    · obtain ⟨-, ⟨e⟩, -⟩ := h7
      exact (d.false_of_mulEquiv hc (eT₁₂.trans e) Insp15418.dihedral_four_central).elim
    · obtain ⟨hD, ⟨eT⟩, -, ⟨e₁⟩⟩ := h8
      exact (d.false_of_caseEight hN2 hc hD (eT₁₂.trans eT) e₁).elim
    · obtain ⟨hD, -⟩ := h9
      exact (d.false_of_caseNine hN2 hN3 hc hD).elim
    · obtain ⟨-, ⟨e⟩, -⟩ := h10
      exact (d.false_of_mulEquiv hc (eT₁₂.trans e) Insp15418.wreath_central_unique).elim
    · obtain ⟨⟨p, hp, hD⟩, -⟩ := h11
      exact (hcenter fun Q => hN1 _ (Or.inr (Or.inr ⟨p, hp, hD⟩)) Q).elim
    · obtain ⟨hD, -⟩ := h12
      exact (hcenter fun Q => hN1 _ (Or.inl hD) Q).elim
    · obtain ⟨hD, -⟩ := h13
      exact (hcenter fun Q => hN1 _ (Or.inr (Or.inl hD)) Q).elim

end InspectionData15418

theorem inspection15418_of_comparison (hCC : ComponentComparison15421)
    (hF618 : F6.TheoremF618Cat) (hN1 : SylowCenterCyclic15418) (hN2 : ComponentIndexTwo15418)
    (hN3 : InvolutionCentralizer15418) : Inspection15418 := by
  intro G _ _ I G₁ G₂ S T Z d
  by_cases hc : CharTwo I
  · exact d.commutator_le_of_charTwo hc hCC
  · exact d.commutator_le_of_commInf (d.commInf_of_not_charTwo hc hF618 hN1 hN2 hN3)

theorem inspection15418_of_b56
    (h56 : AsB56) (hF618 : F6.TheoremF618Cat) (hSL : SylowCenterCyclicSLEps3) :
    Inspection15418 :=
  inspection15418_of_comparison (componentComparison15421_of_b56 h56 hF618) hF618
    (sylowCenterCyclic15418_of hSL) componentIndexTwo15418_holds involutionCentralizer15418_holds

end CFSG.Quasithin.EmptyFaithfulMultiple
