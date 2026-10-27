module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase
public import CFSG.Quasithin.Background.F6Cat

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace F6

@[expose] def WalterModelsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (P : Sylow 2 G), IsMulCommutative (P : Subgroup G) →
      (∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.LieModel G .PSL 2 2 f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ CFSG.Blueprint.LieModel G .PSL 2 p f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.LieModel G .twistedG2 0 3 f) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J1

@[expose] def WreathedRecognitionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    (∃ (S : Sylow 2 G) (n : ℕ), 2 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* CFSG.Open.WreathedTwoGroup n)) →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
        CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
        CFSG.Open.StatedClassicalModel G .PSU 3 p f)

@[expose] def Z2D8SylowListFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.Milestones.SQTKSimpleList S → ∀ P : Sylow 2 S,
    ¬ Nonempty (↥(P : Subgroup S) ≃* Multiplicative (ZMod 2) × DihedralGroup 4)

@[expose] def WreathIndexTwoSylowFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ (P : Sylow 2 S) (H : Subgroup (Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2))),
      H.index = 2 → Nonempty (↥(P : Subgroup S) ≃* ↥H) → IsMulCommutative ↥(P : Subgroup S)

@[expose] def L28AutFact : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 8 →
    Nat.card (MulAut (StatedProj (StatedSL 2 K))) = 3 * Nat.card (StatedProj (StatedSL 2 K))

@[expose] def PGammaL2InspectionFact : Prop :=
  ∀ (p : ℕ) (K : Type) [Field K] [Finite K], p.Prime → Nat.card K = p ^ 2 →
    (p % 8 = 3 ∨ p % 8 = 5) →
    (∀ H : Subgroup (CFSG.GorensteinWalter.PGammaL2 K),
      CFSG.GorensteinWalter.pGammaL2PSLRange K ≤ H →
      (CFSG.GorensteinWalter.pGammaL2PSLRange K).relIndex H = 2 →
      (∃ P : Sylow 2 ↥H,
        Nonempty (↥(P : Subgroup ↥H) ≃* Multiplicative (ZMod 2) × DihedralGroup 4)) →
      H = PSigmaL2 K) ∧
    ∀ P : Sylow 2 (CFSG.GorensteinWalter.PGammaL2 K),
      ¬ Nonempty (↥(P : Subgroup (CFSG.GorensteinWalter.PGammaL2 K)) ≃*
        Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2))

@[expose] def SLEps3CoverFact : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → IsPGroup 3 (Subgroup.center L) →
    Subgroup.center L ≠ ⊥ → ∀ p : ℕ, p.Prime → p ≠ 2 →
      (StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 p 1 →
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ∧
          Nonempty (L ≃* ↥(StatedSL 3 K))) ∧
      (StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 p 1 →
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ 2 ∧
          Nonempty (L ≃* ↥(StatedSU 3 p K)))

end F6

end CFSG.Quasithin
