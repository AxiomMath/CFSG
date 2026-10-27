module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOmPPairB
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.B4Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Matrix

private theorem s16k_finish {K : Type} [Field K] {m : ℕ}
    {u w : Fin m ⊕ Fin m → K} {F : Subgroup (GL (Fin m ⊕ Fin m) K)}
    (hF : F ≤ StatedOmega (StatedQuadPlus m K)) (hFp : IsPGroup 3 ↥F) (hFc : ¬ IsCyclic ↥F)
    (hfix : ∀ f ∈ F, (f : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u ∧
      (f : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w = w)
    (a b : Multiplicative (Fin m ⊕ Fin m → K)) (hau : u = Multiplicative.toAdd a)
    (hbw : w = Multiplicative.toAdd b) :
    ∃ B : Subgroup ↥(StatedOmega (StatedQuadPlus m K)), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
      natAct (StatedOmega (StatedQuadPlus m K)) g a = a ∧
        natAct (StatedOmega (StatedQuadPlus m K)) g b = b := by
  refine ⟨F.subgroupOf (StatedOmega (StatedQuadPlus m K)), ?_, ?_, ?_⟩
  · exact hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hF).symm
  · intro hcyc
    exact hFc ((Subgroup.subgroupOfEquivOfLe hF).isCyclic.mp hcyc)
  · intro g hg
    have hgF : ((g : ↥(StatedOmega (StatedQuadPlus m K))) : GL (Fin m ⊕ Fin m) K) ∈ F := hg
    have h1 := (hfix _ hgF).1
    have h2 := (hfix _ hgF).2
    refine ⟨?_, ?_⟩
    · rw [natAct, ← hau, h1, hau, ofAdd_toAdd]
    · rw [natAct, ← hbw, h2, hbw, ofAdd_toAdd]

theorem s16k_omegaPlus_pair_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 4 ≤ m) (a b : Multiplicative (Fin m ⊕ Fin m → K)) (hab : a ≠ 1 ∨ b ≠ 1) :
    ∃ B : Subgroup ↥(StatedOmega (StatedQuadPlus m K)), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
      natAct (StatedOmega (StatedQuadPlus m K)) g a = a ∧
        natAct (StatedOmega (StatedQuadPlus m K)) g b = b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 := by rwa [Nat.card_eq_fintype_card] at hK
    exact charP_of_card_eq_prime (p := 2) hcard
  set av : Fin m ⊕ Fin m → K := Multiplicative.toAdd a with hav
  set bv : Fin m ⊕ Fin m → K := Multiplicative.toAdd b with hbv
  have hmain : av ≠ 0 ∨ bv ≠ 0 := by
    rcases hab with ha | hb
    · left; intro h; rw [hav] at h; exact ha (toAdd_eq_zero.mp h)
    · right; intro h; rw [hbv] at h; exact hb (toAdd_eq_zero.mp h)
  rcases hmain with ha0 | hb0
  · obtain ⟨F, hFΓ, hFp, hFc, hFfix⟩ := s16k_fix_two hm (u := av) (z := bv) ha0
    exact s16k_finish hFΓ hFp hFc hFfix a b hav hbv
  · obtain ⟨F, hFΓ, hFp, hFc, hFfix⟩ := s16k_fix_two hm (u := bv) (z := av) hb0
    exact s16k_finish hFΓ hFp hFc
      (fun f hf => ⟨(hFfix f hf).2, (hFfix f hf).1⟩) a b hav hbv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
