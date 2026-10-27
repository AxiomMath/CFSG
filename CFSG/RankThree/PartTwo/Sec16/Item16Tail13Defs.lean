module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)

@[expose] noncomputable def KS1613Inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Concl1611 A c L →
      ∀ D : Subgroup G, D ≤ A ⊓ L → Nat.card D = 3 →
        ∃ t ∈ L, ∀ x ∈ D, t * x * t⁻¹ = x⁻¹

@[expose] noncomputable def KS1613Fix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Concl1611 A c L →
      ∀ D : Subgroup G, D ≤ A ⊓ L → Nat.card D = 3 →
        ∀ T ∈ invariantPiSubgroups L A (piOf 2),
          ⁅T, D⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L

@[expose] def KSPGLProper : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K], Sec4.PiField π p f K →
    Sec4.ModThree π (p ^ f) →
      projImage (Sec4.slPi π 3 (p ^ f) K) ≠ projImage (Sec4.glPi π 3 (p ^ f) K)

@[expose] noncomputable def KS1613Fus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) →
    Nat.card (A ⊓ L : Subgroup G) = 9 →
      ∀ y ∈ A ⊓ L, y ≠ 1 → ∀ z ∈ A ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z

end CFSG.RankThree.PartTwo.Sec16
