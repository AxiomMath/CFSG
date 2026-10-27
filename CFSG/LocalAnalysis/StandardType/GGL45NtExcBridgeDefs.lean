module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcAbs
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Ree.Endo
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] noncomputable def ratPts (τ : Tag) (L : Type) [Field L] (Φ : ModGL τ L →* ModGL τ L) :
    Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓ Φ.eqLocus (MonoidHom.id _)

@[expose] def IsExcBridge (p : ℕ) {R : Type} [Group R] (I F : Set (MulAut R)) (τ : Tag) (L : Type)
    [Field L] (F₀ : ModGL τ L →* ModGL τ L) : Prop :=
  (∀ g ∈ adjointGroup τ L, F₀ g ∈ adjointGroup τ L) ∧
  ∃ (ρ : R →* ModGL τ L) (Θ : ratPts τ L (endPow F₀ p) →* MulAut R),
    Function.Injective ρ ∧ (∀ r, ρ r ∈ ratPts τ L (endPow F₀ p)) ∧ Function.Injective Θ ∧
    (∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) ∧ (∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹) ∧
    ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPow F₀ j) (ρ r)

@[expose] def excTagOf : LargeEvenLieTag → Tag
  | .G2 => .G2
  | .F4 => .F4
  | .twF4 => .F4
  | .E6 => .E6
  | .twE6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .triD4 => .D4
  | _ => .G2

@[expose] def ExcBridgeCont (p : ℕ) (L : Type) [Field L] [CharP L 2] (t : LargeEvenLieTag) :
    LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ f ∈ F, orderOf f = p) →
    ∃ (e : ℕ) (Q : ModGL (excTagOf t) L),
      1 ≤ e ∧ IsDiagramTwistMatrix (excTagOf t) L Q ∧
      IsExcBridge p I F (excTagOf t) L (frobTwistGL (excTagOf t) L 2 e Q) ∧
      IsSteinbergEnd (excTagOf t) L ((2 ^ e) ^ p) (endPow (frobTwistGL (excTagOf t) L 2 e Q) p) ∧
      Finite ↥(ratPts (excTagOf t) L (endPow (frobTwistGL (excTagOf t) L 2 e Q) p))

@[expose] def IsExcBridgeSub (p : ℕ) {R : Type} [Group R] (I F : Set (MulAut R)) (τ : Tag) (L : Type)
    [Field L] (F₀ : adjointGroup τ L →* adjointGroup τ L) : Prop :=
  ∃ (ρ : R →* adjointGroup τ L)
    (Θ : (endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup τ L)) →* MulAut R),
    Function.Injective ρ ∧ (∀ r, endPow F₀ p (ρ r) = ρ r) ∧
    Function.Injective Θ ∧ (∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) ∧
    (∀ g r, ρ (Θ g r) = (g : adjointGroup τ L) * ρ r * (g : adjointGroup τ L)⁻¹) ∧
    ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPow F₀ j) (ρ r)

theorem endPow_comm_apply {Γ : Type*} [Group Γ] (F₀ : Γ →* Γ) (n : ℕ) (x : Γ) :
    endPow F₀ n (F₀ x) = F₀ (endPow F₀ n x) := by
  rw [endPow_apply, endPow_apply]
  exact (Function.iterate_succ_apply F₀ n x).symm.trans (Function.iterate_succ_apply' F₀ n x)

theorem ratPts_fix {τ : Tag} {L : Type} [Field L] {Φ : ModGL τ L →* ModGL τ L} {g : ModGL τ L}
    (hg : g ∈ ratPts τ L Φ) : Φ g = g :=
  hg.2

theorem IsExcBridge.absBridge {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)} {τ : Tag}
    {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L} (h : IsExcBridge p I F τ L F₀) :
    AbsBridge p I F (ratPts τ L (endPow F₀ p)) F₀ :=
  h.2

theorem IsExcBridge.stab {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)} {τ : Tag}
    {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L} (h : IsExcBridge p I F τ L F₀) :
    ∀ g ∈ ratPts τ L (endPow F₀ p), F₀ g ∈ ratPts τ L (endPow F₀ p) := by
  intro g hg
  refine ⟨h.1 g hg.1, ?_⟩
  show endPow F₀ p (F₀ g) = F₀ g
  rw [endPow_comm_apply, ratPts_fix hg]

theorem IsExcBridgeSub.absBridge {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)} {τ : Tag}
    {L : Type} [Field L] {F₀ : adjointGroup τ L →* adjointGroup τ L}
    (h : IsExcBridgeSub p I F τ L F₀) :
    AbsBridge p I F ((endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup τ L))) F₀ :=
  h

theorem eqLocus_endPow_stab {Γ : Type*} [Group Γ] (F₀ : Γ →* Γ) (p : ℕ) :
    ∀ g ∈ (endPow F₀ p).eqLocus (MonoidHom.id Γ), F₀ g ∈ (endPow F₀ p).eqLocus (MonoidHom.id Γ) := by
  intro g hg
  have hg' : endPow F₀ p g = g := hg
  show endPow F₀ p (F₀ g) = F₀ g
  rw [endPow_comm_apply, hg']

end CFSG.HardMathSupport.C14Exc
