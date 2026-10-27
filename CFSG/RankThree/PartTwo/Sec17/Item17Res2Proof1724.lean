module

public import CFSG.RankThree.PartTwo.Sec17.Item17ResProof1724

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Item1724LocNSpec : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      (∀ D ∈ scriptQPi A (lB A) ⊤ (piOf p), D ≠ ⊥ →
        ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (D : Set G)) (piOf p),
        ∀ T' ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (D : Set G)) (piOf p),
          IsConjIn (xA A ⊓ Subgroup.normalizer (D : Set G)) S' T') ∧
      (∀ a ∈ A, a ≠ 1 →
        (Subgroup.zpowers a ∈ omegaA A ∨ ∃ B, IsHyperplane A B ∧ a ∈ B ∧ lB A B ≠ ⊥) →
        ∀ S' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf p),
        ∀ T' ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf p),
          IsConjIn (xA A ⊓ Subgroup.centralizer ({a} : Set G)) S' T')

@[expose] def Claim1724DeltaMeet : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Y₀ = (Y₀ ⊓ Subgroup.centralizer
          ((Q ⊓ Subgroup.normalizer (Y₀ : Set G) : Subgroup G) : Set G)) ⊔
        CFSG.Open.pCoreOf 2 Y₀

@[expose] def Claim1724DeltaMax : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ R : Subgroup G, Maximal (fun R : Subgroup G => R ∈ scriptQPi A (lB A) ⊤ (piOf p) ∧
          R ≠ ⊥ ∧ Y₀ = (Y₀ ⊓ Subgroup.centralizer (R : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀) R →
        R ∈ scriptQPiStar A (lB A) ⊤ (piOf p)

theorem claim1724Delta_of (h1721 : Item1721) (hmeet : Claim1724DeltaMeet)
    (hmax : Claim1724DeltaMax) : Claim1724Delta := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h hQM
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  set D := Q ⊓ Subgroup.normalizer (Y₀ : Set G) with hD
  have hAM : A ≤ Subgroup.normalizer ((Subgroup.normalizer (Y₀ : Set G) : Subgroup G) : Set G) :=
    h.toSec17Std.le_normalizer_y0.trans Subgroup.le_normalizer
  have hDmem : D ∈ scriptQPi A (lB A) ⊤ (piOf p) :=
    mem_scriptQPi_of_le h.mem_qStar_G.prop inf_le_left
      (le_normalizer_inf h.mem_qStar_G.prop.1.1.1.2.2 hAM)
  obtain ⟨R, hDR, hR⟩ := Finite.exists_le_maximal (p := fun R : Subgroup G =>
      R ∈ scriptQPi A (lB A) ⊤ (piOf p) ∧ R ≠ ⊥ ∧
        Y₀ = (Y₀ ⊓ Subgroup.centralizer (R : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀)
    ⟨hDmem, hQM, hmeet G A c L Y₀ Y₁ S p P w Q h hJ⟩
  exact ⟨R, hmax G A c L Y₀ Y₁ S p P w Q h hJ R hR, hR.prop.2.2⟩

end CFSG.RankThree.PartTwo.Sec17
