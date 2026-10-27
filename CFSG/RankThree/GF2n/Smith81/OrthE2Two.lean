module

public import CFSG.RankThree.GF2n.Smith81.OrthE2MinusTwo
public import CFSG.RankThree.GF2n.Smith81.OrthFour

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def Smith24ActE2PlusTwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), SmithOrthCfg M Q Z B →
    CtxD4 M Q Z B t → CaseE2Plus M Q Z B t 2 →
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ),
      GlobalModelData M Q Z γ M₀ ∧ ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (qU : QuadraticForm K (ι → K)) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))

theorem smith24ActE2Two_of (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hG : StrothGenByBStatement) (hPlus : Smith24ActE2PlusTwoStatement) :
    Smith24ActE2TwoStatement := by
  intro G _ _ M Q Z B t hc ht hE
  rcases (caseE2_iff M Q Z B t 2).mp hE with hE | hE
  · exact hPlus G M Q Z B t hc ht hE
  · exact smith24ActE2MinusTwo_of h34 h310 hG hc ht hE

end CFSG.RankThree.GF2n.Smith81
