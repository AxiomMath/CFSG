module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.Open.GriessG2FourRootInvolutions
import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
import CFSG.LieType.Simplicity.LieModelFinite
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.LieType.Steinberg.CentralExt.GriessG2FourRootLifts
import CFSG.LieType.Steinberg.CentralExt.GriessCentralCoverRows
import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoMultiplierRow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

universe u v w

namespace CFSG.Open

open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_griess_schur_multipliers_lie_type
    (p k n : ℕ) [Fact p.Prime] (hk : 0 < k) (hn : 2 ≤ n) (hsmall : n = 2 → 4 ≤ p ^ k) :
    commutator PSL(n, GaloisField p k) = ⊤ ∧
      Nonempty (griessHopfMultiplier PSL(n, GaloisField p k) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ k - 1)) ×
          ZMod (griessPSLExceptional n (p ^ k)).1 × ZMod (griessPSLExceptional n (p ^ k)).2)) :=
  CFSG.LieType.Steinberg.CentralExt.SLClosed.griess_psl p k n hk hn hsmall

end CFSG.Open

namespace CFSG.Milestones

open Blueprint.Multiplier CFSG.Open

open CFSG.LieType.Steinberg.CentralExt in
theorem cl_lit_griess_schur_multipliers_all_models
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Models.LieModel X t n p f) :
    commutator X = ⊤ ∧
      Nonempty (griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f) :=
  GriessTwistedE6Two.griess_all_models_of_twistedE6_two TwistedE6TwoCover.twistedE6TwoMultiplier
    t n p f hmodel

theorem cl_lit_griess_schur_multipliers_all_models_statement :
    GriessAllModelsStatement :=
  fun X _ t n p f hmodel => cl_lit_griess_schur_multipliers_all_models X t n p f hmodel

theorem cl_lit_griess_schur_multipliers_central_covers
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Models.LieModel X t n p f) :
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S ≤ 2) →
      ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S = 2) →
      ∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
        IsQuasisimple L → IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  have hquasi (L : Type) [Group L] : Open.IsQuasisimple L ↔ CFSG.IsQuasisimple L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1.symm
  simpa only [hquasi] using CFSG.RankThree.PerfectCover.hopf_central_cover_consequences X

theorem cl_lit_griess_schur_multipliers_all_native_models
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Blueprint.LieModel X t n p f) :
    commutator X = ⊤ ∧
      Nonempty (griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f) :=
  CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6Two.griess_native_models_of_twistedE6_two
    CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover.twistedE6TwoMultiplier t n p f hmodel

theorem cl_lit_griess_schur_multipliers_native_central_covers
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (_hmodel : Blueprint.LieModel X t n p f) :
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S ≤ 2) →
      ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S = 2) →
      ∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
        IsQuasisimple L → IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  have hquasi (L : Type) [Group L] : Open.IsQuasisimple L ↔ CFSG.IsQuasisimple L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1.symm
  simpa only [hquasi] using CFSG.RankThree.PerfectCover.hopf_central_cover_consequences X

theorem cl_lit_griess_schur_multipliers_central_covers_z2
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Models.LieModel X t n p f)
    (ht : t = .PSp ∧ n = 3 ∧ p = 2 ∧ f = 1 ∨ t = .G2 ∧ n = 0 ∧ p = 2 ∧ f = 2 ∨
      t = .F4 ∧ n = 0 ∧ p = 2 ∧ f = 1) :
    Nonempty (griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) ∧
    (∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    (∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
        IsQuasisimple L → IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) :=
  CFSG.LieType.Steinberg.CentralExt.GriessCentralCovers.central_covers_z2 hmodel ht

theorem cl_lit_griess_schur_multipliers_native_central_covers_z2
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Blueprint.LieModel X t n p f)
    (ht : t = .PSp ∧ n = 3 ∧ p = 2 ∧ f = 1 ∨ t = .G2 ∧ n = 0 ∧ p = 2 ∧ f = 2 ∨
      t = .F4 ∧ n = 0 ∧ p = 2 ∧ f = 1) :
    Nonempty (griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) ∧
    (∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    (∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
        IsQuasisimple L → IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) :=
  CFSG.LieType.Steinberg.CentralExt.GriessCentralCovers.native_central_covers_z2 hmodel ht

theorem cl_lit_griess_schur_multipliers_native_central_covers_unrestricted
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Blueprint.LieModel X t n p f) :
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S ≤ 2) →
      ∀ (L : Type) [Group L], CFSG.IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S = 2) →
      ∀ (L L' : Type) [Group L] [Group L'],
        CFSG.IsQuasisimple L → CFSG.IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  have : Finite X := CFSG.LieType.Simplicity.finite_of_native_lieModel hmodel
  exact CFSG.RankThree.PerfectCover.hopf_central_cover_consequences_unrestricted X

theorem cl_lit_griess_schur_multipliers_native_central_covers_z2_unrestricted
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (hmodel : Blueprint.LieModel X t n p f)
    (ht : t = .PSp ∧ n = 3 ∧ p = 2 ∧ f = 1 ∨ t = .G2 ∧ n = 0 ∧ p = 2 ∧ f = 2 ∨
      t = .F4 ∧ n = 0 ∧ p = 2 ∧ f = 1) :
    Nonempty (griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) ∧
    (∀ (L : Type) [Group L], CFSG.IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    (∀ (L L' : Type) [Group L] [Group L'],
        CFSG.IsQuasisimple L → CFSG.IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L')) := by
  have : Finite X := CFSG.LieType.Simplicity.finite_of_native_lieModel hmodel
  obtain ⟨hM, hbound, hunique⟩ :=
    cl_lit_griess_schur_multipliers_native_central_covers_z2 X t n p f hmodel ht
  refine ⟨hM, ?_, ?_⟩
  · intro L _ hL he
    obtain ⟨e⟩ := he
    have : Finite L :=
      CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hL e
    exact hbound L hL ⟨e⟩
  · intro L L' _ _ hL hL' hZ hZ' he he'
    obtain ⟨e⟩ := he
    obtain ⟨e'⟩ := he'
    have : Finite L :=
      CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hL e
    have : Finite L' :=
      CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hL' e'
    exact hunique L L' hL hL' hZ hZ' ⟨e⟩ ⟨e'⟩

theorem cl_lit_griess_schur_multipliers_g2_four_root_lifts
    (L : Type) [Group L] (hL : IsQuasisimple L) (hZ : Nat.card (Subgroup.center L) = 2)
    (hmodel : Blueprint.LieModel (L ⧸ Subgroup.center L) .G2 0 2 2) :
    (∀ x : L, IsG2FourLongRootInvolution (x : L ⧸ Subgroup.center L) → orderOf x = 2) ∧
      (∀ x : L, IsG2FourShortRootInvolution (x : L ⧸ Subgroup.center L) → orderOf x = 4) :=
  CFSG.LieType.Steinberg.CentralExt.G2Four.g2_four_root_lifts L
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1.1 hL) hZ hmodel

end CFSG.Milestones
