module

public import CFSG.RankThree.GF2n.Smith81.OrthE2Frame

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def Smith23E1LgenStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), Cfg M Q Z B →
    CtxD4 M Q Z B t →
    (CaseE1Plus M Q Z B t → QuotSat (Lgen M (LB M Q B)) Q
      (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaPlus 2 (Nat.card Z)))) ∧
    (CaseE1Minus M Q Z B t → QuotSat (Lgen M (LB M Q B)) Q
      (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaMinus 2 (Nat.card Z))))

variable {G : Type} [Group G] [Finite G]

theorem caseE2_two_of_caseE1 (h : Smith23E1LgenStatement) {M Q Z B : Subgroup G} {t : G}
    (hc : Cfg M Q Z B) (ht : CtxD4 M Q Z B t) (hE : CaseE1 M Q Z B t) : CaseE2 M Q Z B t 2 := by
  rw [caseE2_iff]
  rcases (caseE1_iff M Q Z B t).mp hE with hE | hE
  · exact Or.inl ⟨le_rfl, hE.1, hE.2.1, hE.2.2, (h G M Q Z B t hc ht).1 hE⟩
  · exact Or.inr ⟨le_rfl, hE.1, hE.2.1, hE.2.2, (h G M Q Z B t hc ht).2 hE⟩

@[expose] def Smith24ActE2TwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G), SmithOrthCfg M Q Z B →
    CtxD4 M Q Z B t → CaseE2 M Q Z B t 2 →
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ),
      GlobalModelData M Q Z γ M₀ ∧ ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (qU : QuadraticForm K (ι → K)) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))

theorem smith24ActFour_of (h23 : Smith23E1LgenStatement) (h2 : Smith24ActE2TwoStatement) :
    Smith24ActFourStatement := by
  intro G _ _ M Q Z B hc ⟨t, ht, hE⟩
  rcases hE with hE | hE
  · exact h2 G M Q Z B t hc ht (caseE2_two_of_caseE1 h23 hc.toCfg ht hE)
  · exact h2 G M Q Z B t hc ht hE

end CFSG.RankThree.GF2n.Smith81
