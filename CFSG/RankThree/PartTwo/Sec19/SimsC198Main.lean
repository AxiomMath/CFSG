module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG

@[expose] def MainCensus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], RankHyp X →
    ∀ (c : X ⧸ Subgroup.center X) (L : Subgroup (X ⧸ Subgroup.center X))
      (𝒟 : Subgroup (MulAut (X ⧸ Subgroup.center X))),
      AutDatum (X ⧸ Subgroup.center X) c L 𝒟 →
        (∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
          Nonempty (X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)) ∧
        ∃ φ ∈ 𝒟, φ ∉ (MulAut.conj : X ⧸ Subgroup.center X →* MulAut (X ⧸ Subgroup.center X)).range

end CFSG.RankThree.PartTwo.Sec19.SimsC198
