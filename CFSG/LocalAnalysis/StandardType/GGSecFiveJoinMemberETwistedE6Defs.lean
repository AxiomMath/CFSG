module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinDCell
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLang
public import Certificates.Certificate13659
public import Certificates.Certificate13660

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


@[expose] def GGSecFiveTwistedE6E7MemberInput : Prop :=
      GGTBFixInput → GGNbrInnerWeylInput →
    GGSecFiveL1PhanInput → GGSecFiveRk1PhanInput → GGSecFiveGenPhanInput →
    GGSecFiveOrbPhanInput → GGSecFiveL2PhanInput → GGSecFivePhanPairInput →
    GGSecFiveNonSplitNbrInput →
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)),
      GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ¬ GGSecFivePhanARow p B Bs x L D J →
      ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι)
        (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        (∃ σ : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex σ) →
        ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
          GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L →
          ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e ∧
            ∃ (t' : StatedLieTag) (n' f' : ℕ) (lambda : (ggU t' n' f').K →* G),
              StatedLieAdmissible t' n' 2 f' ∧ 2 ≤ (ggU t' n' f').D.rank ∧
              lambda.ker ≤ Subgroup.center (ggU t' n' f').K ∧ lambda.range = L ∧
              ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
                (delta : Fin (ggU t' n' f').D.rank → ℤ)
                (model : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k delta),
                (lambda.comp model.phi).range = ggRankOnePerf Bs r₀

end CFSG.StandardType

end
