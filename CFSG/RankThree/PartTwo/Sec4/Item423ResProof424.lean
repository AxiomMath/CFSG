module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof424

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def K424Pairing : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46 X → IsQuasisimple X → Subgroup.center X = ⊥ →
    ¬ IsSLThreePiAny X → IsList424 X →
    ∀ (D : Subgroup X) (c d : X) (K : Subgroup X), InnerConfig424 X D c d K →
      (((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
            Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
          ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
            Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
        Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6)) ∨
      ((Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
          Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.He)) ∧
        Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 1)) ∧
        Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6))

theorem k424InnerFull_of_census (hC : K424InnerCensus) (hP : K424Pairing) : K424InnerFull :=
  fun X _ _ hX hq hZ hSL D c d K h =>
    hP X hX hq hZ hSL (hC X hX hq hZ hSL D c d K h).1 D c d K h

end CFSG.RankThree.PartTwo.Sec4
