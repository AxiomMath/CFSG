module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem case148Seven_of_pgl_data {A Y : Subgroup G} [(ker148 A Y).Normal]
    {LB : Subgroup G → Subgroup G} {e e' : G} {K K' Le Le' : Subgroup G}
    {p₁ f₁ e₁ p₂ f₂ e₂ : ℕ} [Fact p₁.Prime] [Fact p₂.Prime]
    (heΩ : Subgroup.zpowers e ∈ omegaA A) (he'Ω : Subgroup.zpowers e' ∈ omegaA A)
    (hLe : Le ∈ lA A e) (hLe' : Le' ∈ lA A e') (hKLe : K ≤ Le) (hKY : K ≤ Y)
    (hK'Le' : K' ≤ Le') (hK'Y : K' ≤ Y)
    (hX : img148 A Y (deltaZero A LB Y) = img148 A Y K ⊔ img148 A Y K')
    (hK'C : img148 A Y K' ≤
      Subgroup.centralizer (img148 A Y K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))
    (hZ : img148 A Y K ⊓
      Subgroup.centralizer (img148 A Y K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) = ⊥)
    (hf₁ : 1 ≤ f₁) (he₁ : 1 ≤ e₁) (hf₂ : 1 ≤ f₂) (he₂ : 1 ≤ e₂)
    (hpgl₁ : IsZ3PGLThreeAt ↥(img148 A Y (K ⊔ A)) p₁ f₁)
    (hpgl₂ : IsZ3PGLThreeAt ↥(img148 A Y (K' ⊔ A)) p₂ f₂)
    (hL₁ : Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p₁ (f₁ * e₁))
    (hL₂ : Sec4.IsoLThreePi (↥Le' ⧸ aschbacherSolvableCore 3 ↥Le') p₂ (f₂ * e₂)) :
    Case148Seven A LB Y := by
  refine ⟨e, e', Le, Le', K, K', p₁, f₁, e₁, p₂, f₂, e₂, inferInstance, inferInstance, heΩ, he'Ω,
    hLe, hLe', le_inf hKLe hKY, le_inf hK'Le' hK'Y, hX.symm, ?_, ?_, hf₁, he₁, hf₂, he₂, hpgl₁,
    hpgl₂, hL₁, hL₂⟩
  · exact le_bot_iff.mp ((inf_le_inf_left _ hK'C).trans hZ.le)
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hK'C hy) x hx

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
