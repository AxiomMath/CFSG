module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenAltProof
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
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
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

@[expose] noncomputable def ratPoints {τ : Tag} {L : Type} [Field L]
    (Φ : ModGL τ L →* ModGL τ L) : Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓ Φ.eqLocus (MonoidHom.id _)

@[expose] def rootsTrivialOn {τ : Tag} {L : Type} [Field L] (A : Subgroup (ModGL τ L)) :
    Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ A → rootChar a γ = 1}

@[expose] noncomputable def centConn
    {τ : Tag} {L : Type} [Field L] (A : Subgroup (ModGL τ L)) : Subgroup (ModGL τ L) :=
  torusGroup τ L ⊔ rootSpan τ L (rootsTrivialOn A)

@[expose] noncomputable def jointChar {τ : Tag} {L : Type} [Field L] (a₁ a₂ : Fin τ.rank → Lˣ) :
    Multiplicative (Fin τ.rank → ℤ) →* Lˣ × Lˣ :=
  (rootCharHom a₁).prod (rootCharHom a₂)

@[expose] def ratOrbit {τ : Tag} (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ) :=
  {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ Ψ ∧ γ = ρ^[k] δ}

@[expose] noncomputable def ratComp
    {τ : Tag} {L : Type} [Field L] (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (Γ : Subgroup (ModGL τ L)) (Ψ : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ L) :=
  ⁅rootSpan τ L (ratOrbit ρ Ψ) ⊓ Γ, rootSpan τ L (ratOrbit ρ Ψ) ⊓ Γ⁆

theorem rationalComponent_eq_ratComp
    {τ : Tag} {L : Type} [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Γ : Subgroup (ModGL τ L))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ) :
    rationalComponent ρ Γ χ i = ratComp (fun u => ρ u) Γ (componentRoots χ i) := rfl

@[expose] def IsSteinbergEndZ (τ : Tag) (L : Type) [Field L] (q : ℕ)
    (Φ : ModGL τ L →* ModGL τ L) : Prop :=
  ∃ Fr : L →+* L, (∀ c, Fr c = c ^ q) ∧ ∃ P : ModGL τ L, IsDiagramTwistMatrix τ L P ∧
    ∀ g, Φ g = P * Units.map (entrywiseHom Fr) g * P⁻¹

theorem isSteinbergEndZ_of_isSteinbergEnd {τ : Tag} {L : Type} [Field L] {q : ℕ}
    {Φ : ModGL τ L →* ModGL τ L} (h : IsSteinbergEnd τ L q Φ) : IsSteinbergEndZ τ L q Φ := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := h
  refine ⟨Fr, hFr, P, ?_, hΦ⟩
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · exact Or.inl rfl
  · subst ht
    exact Or.inr ⟨t, 1, rfl, by simp [diagramAt]⟩

theorem isSteinbergEndZ_frobTwistGL {τ : Tag} {L : Type} [Field L] (p : ℕ) [Fact p.Prime]
    [CharP L p] (e : ℕ) {P : ModGL τ L} (hP : IsDiagramTwistMatrix τ L P) :
    IsSteinbergEndZ τ L (p ^ e) (frobTwistGL τ L p e P) :=
  ⟨iterateFrobenius L p e, fun c => iterateFrobenius_def p e c, P, hP, fun _ => rfl⟩

@[expose] noncomputable def langDatumOfPosition
    {τ : Tag} {L : Type} [Field L] {q : ℕ}
    {Φ : ModGL τ L →* ModGL τ L} (hΦ : IsSteinbergEnd τ L q Φ) (w : WeylGroup τ) (g : ModGL τ L)
    (hg : g ∈ adjointGroup τ L) (hlang : Φ g = g * canonicalRep (coxeterSystem τ) L w) :
    LangDatum τ L where
  Φ := Φ
  q := q
  n := canonicalRep (coxeterSystem τ) L w
  g0 := g
  steinberg := hΦ
  n_weyl := ⟨w, rfl⟩
  g0_mem := hg
  lang := hlang

@[expose] def IsExcTag (τ : Tag) : Prop :=
  τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .D4

theorem isExcTag (τ : Tag) : IsExcTag τ := by
  cases τ <;> simp [IsExcTag]

@[expose] def nontoralMinRank (τ : Tag) (p : ℕ) : ℕ :=
  match τ with
  | .F4 => if p = 3 then 3 else 1000
  | .E6 => if p = 3 then 2 else 1000
  | .E7 => if p = 3 then 3 else 1000
  | .E8 => if p = 3 then 3 else if p = 5 then 3 else 1000
  | _ => 1000

@[expose] def GGLieToralPosition :
    Prop :=
  ∀ (τ : Tag), IsExcTag τ → ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    (letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) → ∀ (f : ℕ),
    1 ≤ f → ∀ (Φ : ModGL τ L →* ModGL τ L), IsSteinbergEndZ τ L (2 ^ f) Φ →
    Finite ↥(ratPoints Φ) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ A : Subgroup (ModGL τ L), A ≤ ratPoints Φ →
      IsElemAbelian p A → Nat.card A < p ^ nontoralMinRank τ p → IsToralSubgroup τ L A

@[expose] def GGLieLangPosition :
    Prop :=
  ∀ (τ : Tag), IsExcTag τ → ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (f : ℕ),
    1 ≤ f → ∀ (Φ : ModGL τ L →* ModGL τ L), IsSteinbergEndZ τ L (2 ^ f) Φ →
    Finite ↥(ratPoints Φ) →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ A : Subgroup (ModGL τ L), A ≤ ratPoints Φ →
      IsElemAbelian p A → IsToralSubgroup τ L A →
      ∃ (w : WeylGroup τ) (g : ModGL τ L), g ∈ adjointGroup τ L ∧
        Φ g = g * canonicalRep (coxeterSystem τ) L w ∧
        A.map (MulAut.conj g⁻¹).toMonoidHom ≤ twistedTorusOf (canonicalRep (coxeterSystem τ) L w) Φ

end CFSG.StandardType.LieCore
