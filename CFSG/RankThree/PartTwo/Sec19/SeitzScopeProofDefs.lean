module

public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenBase

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

@[expose] def IsLThreePiIndex (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d = .A 2 q ∨ d = .twistedA 2 q

@[expose] def IsSeitz441Index (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d = .A 3 q ∨ d = .twistedA 3 q ∨ d = .B 2 q) ∨ IsG2Index d ∨
    IsReeF4Index d

@[expose] def SeitzThreeLThreePi : Prop :=
  SeitzPlanes fun d p _ => p = 3 ∧ IsLThreePiIndex d.1

@[expose] def SeitzThreeLThreePiField : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ ¬ NarrowScope p E ∧ p = 3 ∧ IsLThreePiIndex d.1

@[expose] def SeitzThreeTriality : Prop :=
  SeitzPlanes fun d p _ => p = 3 ∧ IsTrialityIndex d.1

namespace SeitzScopeProof

open TauCeti CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

theorem closure_fixSet_eq_top_of_seitzPlanes
    {S : ∀ d : ValidLieTypeIndex, ℕ → Subgroup (MulAut (Cat d)) → Prop} (hS : SeitzPlanes S)
    {X : Type} [Group X] {d : ValidLieTypeIndex} (hchar : 3 ≠ d.1.characteristic)
    (hexc : ¬ IsD2SeitzException 3 d.1) (ι : X ≃* (CFSGIndex.lie d).Group)
    (F : Subgroup (MulAut X)) (hF : CFSG.Open.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hs : S d 3 (mapAut ι F)) : Subgroup.closure (fixSet F) = ⊤ := by
  have hE := hS d 3 Nat.prime_three (by norm_num) hchar hexc (mapAut ι F)
    (isElemAbelian_mapAut hF ι) (by rw [card_mapAut, hF9]; norm_num) hs
  exact (closure_fixSet_mapAut_eq_top_iff ι F).mp hE

end SeitzScopeProof

end CFSG.RankThree.PartTwo.Sec19
