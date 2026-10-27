module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KcMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Y1Main

public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

namespace CFSG.Quasithin.S15223P4.D1

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

omit [Finite G] in
theorem isLnTwoQuot_of_quotEquiv (ψ : OTwoQuot X ≃* SL3F2) : IsLnTwoQuot X 3 :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥X 2)).trans ψ).trans
    (statedSL_equiv_SL3F2 (F := ZMod 2) (ZMod.card 2)).symm⟩

theorem false_of_caseG_one (hcover : AsA36NoOddCover) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h12 : He12.StageLemma15212W)
    (h21 : ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      Lemma15221ConclW T Mc M H H₁ H₂ B₀ I)
    (h22 : StageLemma15222Canon) (c : P4Ctx T Mc M H B₀ I X) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2)
    (e : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)))
    (hpar : IsMaxParabolic2 (autOn X (P4V M I X)) (autOn (M ⊓ I ⊓ X) (P4V M I X)))
    (hnot : ¬ X ≤ Mc) : False := by
  have hpre := p4N1pre_of hcover c hF e hpar hnot
  obtain ⟨ψ⟩ := exists_quotEquiv hcover c hF e
  have hXI := normal_of_pre c hpre ψ h37 h38
  have hN : P4N1 T Mc M H B₀ I X := ⟨hpre, hXI⟩
  have hq := isLnTwoQuot_of_quotEquiv ψ
  obtain ⟨he, hred, H₁, H₂, hP, hK2, hXK2⟩ := K.exists_pair_K2 c hXI hq h21
  have h3 := Kc.isThreePrimeGroup_cv c hN hq he hred h21 h12
  exact Y1.false_of_Y1 c hN h3 hred hP hK2 hXK2 h22

end CFSG.Quasithin.S15223P4.D1
