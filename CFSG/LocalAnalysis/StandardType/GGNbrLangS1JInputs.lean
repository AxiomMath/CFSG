module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
public import CFSG.LocalAnalysis.StandardType.GGL45NtClUni

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGBstarAbelianPreimageJUniS1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d m : ℕ),
        (p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5) → p ∣ 2 ^ m + 1 →
        ∀ (E : Type) [Field E] (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m E)
          (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))),
          IsMulCommutative
            ((((ggBsAut hN).range).map (kgInducedAut θ)).comap
              (CFSG.HardMathSupport.C14Cl.uniConj hE d))

@[expose] def GGBstarAbelianPreimageJS1Input : Prop :=
  GGBstarAbelianPreimageJLinInput ∧ GGBstarAbelianPreimageJUniS1Input

end CFSG.StandardType
