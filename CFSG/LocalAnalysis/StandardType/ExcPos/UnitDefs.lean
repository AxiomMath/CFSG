module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRoots
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.LocalAnalysis.StandardType.GGSixExcPosRangeDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

abbrev ExcOmega (f : ℕ) : Type := GGFinModel.GGL

@[expose] def excCurve
    {τ : CFSG.Blueprint.Chevalley.Tag} {K : Type} [Field K] (α : Fin τ.rank → ℤ)
    (w : ModGL τ K) : Subgroup (ModGL τ K) :=
  (rootSubgroup τ K α).map (MulAut.conj w).toMonoidHom

structure ExcPacket
    (τ : CFSG.Blueprint.Chevalley.Tag) {X : Type} [Group X] (f p : ℕ)
    (G₀ B₁ D J : Subgroup X) (x : X) (R Rm : Subgroup X) : Type where
  one_le_f : 1 ≤ f
  Fr : ExcOmega f →+* ExcOmega f
  hFr : ∀ c : ExcOmega f, Fr c = c ^ Nat.card (GaloisField 2 f)
  diag : ModGL τ (ExcOmega f)
  hdiag : diag = 1 ∨ ∃ h : TwistTag.E6.tag = τ, diag = diagramAt τ (ExcOmega f) .E6 h
  Δ : LangDatum τ (ExcOmega f)
  hΦ : ∀ g, Δ.Φ g = diag * Units.map (entrywiseHom Fr) g * diag⁻¹
  hq : Δ.q = Nat.card (GaloisField 2 f)
  ρ : Equiv.Perm (Fin τ.rank → ℤ)
  frob : FrobRootMap Δ ρ
  finite : Finite Δ.model
  η : ↥G₀ →* ModGL τ (ExcOmega f)
  ker_η : η.ker ≤ Subgroup.center ↥G₀
  range_η : η.range = Δ.Γ
  Θ : ↥B₁ →* ModGL τ (ExcOmega f)
  Θ_mem : ∀ b, Θ b ∈ Δ.model
  Θ_eq_one : ∀ b : ↥B₁, Θ b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X)
  η_conj : ∀ (b : ↥B₁) (g g' : ↥G₀), (g' : X) = b * g * (b : X)⁻¹ →
    η g' = Θ b * η g * (Θ b)⁻¹
  coord : X → Fin τ.rank → (ExcOmega f)ˣ
  Θ_eq_coord : ∀ b : ↥B₁, (b : X) ∈ D → Θ b = rootDiagUnit τ (coord b)
  coord_pow : ∀ e ∈ D, ∀ i, coord e i ^ p = 1
  coord_torus : ∀ e ∈ D, rootDiagUnit τ (coord e) ∈ Δ.torus
  d : X
  d_mem : d ∈ D
  closure_eq : Subgroup.closure ({x, d} : Set X) = D
  iJ : KernelComponent (LieCore.jointChar (coord x) (coord d))
  map_J_le : (J.subgroupOf G₀).map η ≤ rootSpan τ (ExcOmega f)
    (LieCore.ratOrbit ρ (componentRoots (LieCore.jointChar (coord x) (coord d)) iJ))
  attach_J : CFSG.Assembly.IsComponentOf ((J.subgroupOf G₀).map η)
    (Δ.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit τ (coord x), rootDiagUnit τ (coord d)} : Set (ModGL τ (ExcOmega f))))
  attach_nbr : ∀ e ∈ D, ∀ K : Subgroup X, K ≤ G₀ →
    CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) →
    CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map η)
      (Δ.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ (coord e)})
  orbit : componentOrbitLength ρ (componentRoots (LieCore.jointChar (coord x) (coord d)) iJ) = 1 ∨
    (componentOrbitLength ρ (componentRoots (LieCore.jointChar (coord x) (coord d)) iJ) = 2 ∧
      (∃ h : TwistTag.E6.tag = τ, diag = diagramAt τ (ExcOmega f) .E6 h) ∧
      p ∣ Nat.card (GaloisField 2 f) - 1 ∧ Δ.n = 1)
  α : Fin τ.rank → ℤ
  α_mem : α ∈ componentRoots (LieCore.jointChar (coord x) (coord d)) iJ
  wD : ModGL τ (ExcOmega f)
  wD_mem : wD ∈ torusGroup τ (ExcOmega f) ⊔
    rootSpan τ (ExcOmega f) (kernelRoots (LieCore.jointChar (coord x) (coord d)))
  pair_one :
    componentOrbitLength ρ (componentRoots (LieCore.jointChar (coord x) (coord d)) iJ) = 1 →
      Nat.card ((R.subgroupOf G₀).map η) = Nat.card (GaloisField 2 f) ∧
      (R.subgroupOf G₀).map η = excCurve α wD ⊓ Δ.model ∧
      Nat.card ((Rm.subgroupOf G₀).map η) = Nat.card (GaloisField 2 f) ∧
      (Rm.subgroupOf G₀).map η = excCurve (-α) wD ⊓ Δ.model ∧
      (excCurve α wD).map Δ.step = excCurve α wD ∧
      (excCurve (-α) wD).map Δ.step = excCurve (-α) wD
  pair_two :
    componentOrbitLength ρ (componentRoots (LieCore.jointChar (coord x) (coord d)) iJ) = 2 →
      ((excCurve α wD).map Δ.step).map Δ.step = excCurve α wD ∧
      (R.subgroupOf G₀).map η ≤ excCurve α wD ⊔ (excCurve α wD).map Δ.step ∧
      Nat.card ((R.subgroupOf G₀).map η) = Nat.card (GaloisField 2 f) ^ 2

namespace ExcPacket

variable
  {X : Type} [Group X] {τ : CFSG.Blueprint.Chevalley.Tag} {f p : ℕ}
  {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X}
  (P : ExcPacket τ f p G₀ B₁ D J x R Rm)

@[expose] def chiD : Multiplicative (Fin τ.rank → ℤ) →* (ExcOmega f)ˣ × (ExcOmega f)ˣ :=
  LieCore.jointChar (P.coord x) (P.coord P.d)

@[expose] def chiAt (e : X) : Multiplicative (Fin τ.rank → ℤ) →* (ExcOmega f)ˣ :=
  CFSG.LieType.AlgebraicGroups.rootCharHom (P.coord e)

@[expose] def rootsJ : Set (Fin τ.rank → ℤ) := componentRoots P.chiD P.iJ

@[expose] def b : ℕ := componentOrbitLength P.ρ P.rootsJ

end ExcPacket

@[expose] def ExcNbrRange {X : Type} [Group X]
    (K R : Subgroup X) : Prop :=
  (∃ (m g : ℕ) (β : Fin (ggU .PSL (m + 1) g).D.rank → ℤ),
    ((4 ≤ m ∧ 1 ≤ g) ∨ (m = 3 ∧ 2 ≤ g)) ∧ β ∈ (ggU .PSL (m + 1) g).D.roots ∧
      GGRootVia (ggU .PSL (m + 1) g) K R β) ∨
  (∃ (n g : ℕ) (β : Fin (ggU .PSU n g).D.rank → ℤ), 4 ≤ n ∧ 1 ≤ g ∧
    β ∈ (ggU .PSU n g).D.roots ∧ GGLongRoot (ggU .PSU n g).D β ∧
      GGRootVia (ggU .PSU n g) K R β) ∨
  (∃ (g : ℕ) (β : Fin (ggU .PSU 6 g).D.rank → ℤ), 2 ≤ g ∧ β ∈ (ggU .PSU 6 g).D.roots ∧
    2 • β ∉ (ggU .PSU 6 g).D.roots ∧ GGRootVia (ggU .PSU 6 g) K R β) ∨
  (∃ (n g : ℕ) (β : Fin (ggU .POmegaPlus n g).D.rank → ℤ), 4 ≤ n ∧ 1 ≤ g ∧
    β ∈ (ggU .POmegaPlus n g).D.roots ∧ GGRootVia (ggU .POmegaPlus n g) K R β) ∨
  (∃ (n g : ℕ) (β : Fin (ggU .POmegaMinus n g).D.rank → ℤ), 4 ≤ n ∧ 1 ≤ g ∧
    β ∈ (ggU .POmegaMinus n g).D.roots ∧ GGLongRoot (ggU .POmegaMinus n g).D β ∧
    GGRootVia (ggU .POmegaMinus n g) K R β) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F) (g : ℕ)
      (β : Fin (triD4Universal F σ).D.rank → ℤ), TriField F σ g ∧
    GGLongRoot (triD4Universal F σ).D β ∧ GGRootVia (triD4Universal F σ) K R β) ∨
  (∃ (t : StatedLieTag) (g : ℕ) (β : Fin (ggU t 0 g).D.rank → ℤ),
    (t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ 1 ≤ g ∧ β ∈ (ggU t 0 g).D.roots ∧
    GGRootVia (ggU t 0 g) K R β) ∨
  (∃ (g : ℕ) (β : Fin (ggU .twistedE6 0 g).D.rank → ℤ), 1 ≤ g ∧
    β ∈ (ggU .twistedE6 0 g).D.roots ∧ GGLongRoot (ggU .twistedE6 0 g).D β ∧
    GGRootVia (ggU .twistedE6 0 g) K R β)

@[expose] def ExcU1a :
    Prop :=
  ∀ (t : StatedLieTag), (t = .E6 ∨ t = .E7 ∨ t = .E8) →
    ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
      (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp t n f ψ p G₀ B₁ D J L x →
      ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 t n f p ψ R Rm ∧
        ∃ P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm, P.b = 1

@[expose] def ExcU1b :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1) →
    ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .twistedE6 n f p ψ R Rm ∧
      Nonempty (ExcPacket .E6 f p G₀ B₁ D J x R Rm)

@[expose] def ExcUR :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    p = 3 → 3 ∣ 2 ^ f + 1 → ¬ 9 ∣ 2 ^ f + 1 →
    ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .twistedE6 n f p ψ R Rm ∧
      ∃ P : ExcPacket .E6 f p G₀ B₁ D J x R Rm, P.b = 1

@[expose] def ExcUK :
    Prop :=
  ∀ (t : StatedLieTag), (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
      (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp t n f ψ p G₀ B₁ D J L x →
    ∀ (R Rm : Subgroup X) (P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm),
    ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K →
      Odd (Nat.card (Subgroup.center ↥K)) →
      ∃ iK : KernelComponent (P.chiAt e), P.rootsJ ⊆ componentRoots (P.chiAt e) iK ∧
        (K.subgroupOf G₀).map P.η ≤ rootSpan (GGFinModel.langTag t) (ExcOmega f)
          (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) ∧
        (componentRoots (P.chiAt e) iK = P.rootsJ → K = J)

@[expose] def ExcU3 :
    Prop :=
  ∀ (t : StatedLieTag), (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
      (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp t n f ψ p G₀ B₁ D J L x →
    ∀ (R Rm : Subgroup X) (P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm),
      2 ≤ compRank P.rootsJ

@[expose] def ExcU5 :
    Prop :=
  ∀ (t : StatedLieTag), (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
      (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp t n f ψ p G₀ B₁ D J L x →
    ∀ (R Rm : Subgroup X) (P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm),
    R ≤ J → Rm ≤ J → GGRootPosG0 t n f p ψ R Rm → P.b = 1 →
    ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
      Odd (Nat.card (Subgroup.center ↥K)) → K ≠ G₀ →
      ∀ iK : KernelComponent (P.chiAt e), P.rootsJ ⊆ componentRoots (P.chiAt e) iK →
        componentRoots (P.chiAt e) iK ≠ P.rootsJ →
        (K.subgroupOf G₀).map P.η ≤ rootSpan (GGFinModel.langTag t) (ExcOmega f)
          (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) →
        componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1 →
        2 ≤ compRank P.rootsJ →
        ¬ GGSixLSevenA3Case K →
        ExcNbrRange K R

@[expose] def ExcU7 :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ∀ (R Rm : Subgroup X) (P : ExcPacket .E6 f p G₀ B₁ D J x R Rm),
    R ≤ J → Rm ≤ J → GGRootPosG0 .twistedE6 n f p ψ R Rm → P.b = 2 →
    ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
      Odd (Nat.card (Subgroup.center ↥K)) → K ≠ G₀ →
      ∀ iK : KernelComponent (P.chiAt e), P.rootsJ ⊆ componentRoots (P.chiAt e) iK →
        componentRoots (P.chiAt e) iK ≠ P.rootsJ →
        (K.subgroupOf G₀).map P.η ≤
          rootSpan .E6 (ExcOmega f) (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) →
        componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1 →
        2 ≤ compRank P.rootsJ →
        ∃ β : Fin (ggU .PSU 6 f).D.rank → ℤ, 2 ≤ f ∧ β ∈ (ggU .PSU 6 f).D.roots ∧
          2 • β ∉ (ggU .PSU 6 f).D.roots ∧ GGRootVia (ggU .PSU 6 f) K R β

end CFSG.StandardType.LieKnownR2.ExcPos

end
