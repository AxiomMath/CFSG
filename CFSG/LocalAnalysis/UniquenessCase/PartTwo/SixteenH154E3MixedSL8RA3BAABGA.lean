module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

private theorem s16h_sup_zpowers_noncyclic_of_prime {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {u v : X} (hu : u ^ p = 1) (hv : v ^ p = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hcomm : ∀ x ∈ Subgroup.zpowers u, ∀ y ∈ Subgroup.zpowers v, x * y = y * x)
    (hdisj : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥) :
    IsPGroup p ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧
      ¬ IsCyclic ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : Nat.card (Subgroup.zpowers u) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu hu1]
  have hT : Nat.card (Subgroup.zpowers v) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hv hv1]
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers u) (Subgroup.zpowers v) hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one, hS, hT] at hcard
  have hcardE : Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) = p ^ 2 := by
    rw [hcard]; ring
  have hEel : IsElemAbelian p (Subgroup.zpowers u ⊔ Subgroup.zpowers v) :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (p := p) hu)
      (CFSG.Open.isElemAbelian_zpowers (p := p) hv) hcomm
  refine ⟨IsPGroup.of_card (n := 2) hcardE, ?_⟩
  exact s16c7_not_isCyclic_of_elemAbelian (G := X) hp hEel (le_of_eq hcardE.symm)

private theorem s16h_normalizer_inf_le_normalizer_sup {X : Type} [Group X]
    {A B : Subgroup X} :
    Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) ≤
      Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  have hA : A.map (MulAut.conj g).toMonoidHom = A :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg.1
  have hB : B.map (MulAut.conj g).toMonoidHom = B :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg.2
  have hmap : (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hA, hB]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo