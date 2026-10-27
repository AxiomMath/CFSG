module

public import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofU
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] def Step162UJComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∃ J ∈ scriptY0 A (lB A),
        J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) ∧
          ¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n

@[expose] def Step162UJA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∀ J ∈ scriptY0 A (lB A),
        J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) →
        Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) → False

theorem step162UJ_of (hC : Step162UJComp) (hA5 : Step162UJA5) : Step162UJ := by
  intro G _ _ A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt
  obtain ⟨J, hJ, hJK, hJL⟩ := hC G A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt
  exact ⟨J, hJ, hJK, Or.inl ⟨hJL,
    ⟨fun φ => hA5 G A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J hJ hJK ⟨φ⟩⟩⟩⟩

end CFSG.RankThree.PartTwo.Sec16
