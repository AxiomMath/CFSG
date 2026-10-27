module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def TwE6U7C1 : Prop :=
  ∀ {M N : Type} [CommGroup M] [CommGroup N]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} {χ' : Multiplicative (Fin Tag.E6.rank → ℤ) →* N}
    {i₁ i₂ : KernelComponent χ}, i₁ ≠ i₂ → compRank (componentRoots χ i₁) = 2 →
    compRank (componentRoots χ i₂) = 2 → ∀ {i' : KernelComponent χ'},
      componentRoots χ i₁ ⊆ componentRoots χ' i' → componentRoots χ i₂ ⊆ componentRoots χ' i' →
      componentRoots χ' i' ≠ {α | IsRoot Tag.E6 α} →
      compRank (componentRoots χ' i') = 5 ∧ (componentRoots χ' i').ncard = 30

@[expose] def TwE6U7C2 : Prop :=
  ∀ {M : Type} [CommGroup M] {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M}
    (i : KernelComponent χ) {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)},
    (∀ γ, IsRoot Tag.E6 γ → ρ γ = permLattice (TwistTag.perm .E6) γ) →
    ∀ {Ψ₁ Ψ₂ : Set (Fin Tag.E6.rank → ℤ)}, Ψ₁ ⊆ componentRoots χ i → Ψ₂ ⊆ componentRoots χ i →
      Ψ₁.Nonempty → Disjoint Ψ₁ Ψ₂ → (fun u => ρ u) '' Ψ₁ = Ψ₂ →
      (fun u => ρ u) '' componentRoots χ i = componentRoots χ i →
      ¬ twistInner (componentRoots χ i) (fun u => ρ u)

@[expose] def ExcSuClass {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀) (a : Fin Tag.E6.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (f p : ℕ) : Prop :=
  rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ p.Prime ∧ p ≠ 2 ∧ rootDiagUnit Tag.E6 a ^ p = 1 ∧
    S.D.q = 2 ^ f ∧ twistKind S.ρ (rootCharHom a) i = .suN ∧
    compRank (componentRoots (rootCharHom a) i) = 5 ∧
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def ExcSwapped {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀) (a : Fin Tag.E6.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (f : ℕ) (A : Subgroup (ModGL Tag.E6 GGL)) : Prop :=
  Nat.card ↥A = (2 ^ f) ^ 2 ∧ A ≤ S.Γ ∧
    ∃ (α : Fin Tag.E6.rank → ℤ) (w : ModGL Tag.E6 GGL),
      α ∈ componentRoots (rootCharHom a) i ∧
      w ∈ torusGroup Tag.E6 GGL ⊔ rootSpan Tag.E6 GGL (kernelRoots (rootCharHom a)) ∧
      excCurve α w ≤ rootSpan Tag.E6 GGL (componentRoots (rootCharHom a) i) ∧
      ((excCurve α w).map S.D.step).map S.D.step = excCurve α w ∧
      (∀ v ∈ excCurve α w, ∀ v' ∈ (excCurve α w).map S.D.step, v * v' = v' * v) ∧
      A ≤ excCurve α w ⊔ (excCurve α w).map S.D.step

@[expose] def ExcU7Cover : Prop :=
  ∀ (p₀ : ℕ) (S : LangSetup Tag.E6 GGL p₀) (a : Fin Tag.E6.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (f p : ℕ), ExcSuClass S a i f p →
    ∃ φ : (ggU .PSU 6 f).K →* ModGL Tag.E6 GGL,
      φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      φ.ker ≤ Subgroup.center (ggU .PSU 6 f).K ∧ Finite (ggU .PSU 6 f).K ∧
      Group.IsPerfect (ggU .PSU 6 f).K ∧
      CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .PSU 6 f).K ∧
      ∃ (β : Fin (ggU .PSU 6 f).D.rank → ℤ) (u : (ggU .PSU 6 f).K),
        β ∈ (ggU .PSU 6 f).D.roots ∧ 2 • β ∉ (ggU .PSU 6 f).D.roots ∧
        ExcSwapped S a i f (ggRootSub (ggU .PSU 6 f).D φ β u)

@[expose] def ExcU7Transport : Prop :=
  ∀ (p₀ : ℕ) (S : LangSetup Tag.E6 GGL p₀) (a : Fin Tag.E6.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (f p : ℕ), ExcSuClass S a i f p →
    ∀ A A' : Subgroup (ModGL Tag.E6 GGL), ExcSwapped S a i f A → ExcSwapped S a i f A' →
      ∃ h ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        A.map (MulAut.conj h).toMonoidHom = A'

end CFSG.StandardType.LieKnownR2.ExcPos
