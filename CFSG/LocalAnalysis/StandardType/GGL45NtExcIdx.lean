module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Exc

open scoped CFSG.ConvolutionPoints



@[expose] def corootVec
                                      {τ : Tag} (β : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  fun i => corootPair β (Pi.single i 1)

@[expose] def CorootPSaturated
                                      {τ : Tag} (p : ℕ) (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  ∀ y : Fin τ.rank → ℤ, p • y ∈ AddSubgroup.closure (corootVec '' Ψ) →
    y ∈ AddSubgroup.closure (corootVec '' Ψ)

@[expose] noncomputable def famM
                                   {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) : Subgroup (adjointGroup τ L) :=
  (familyGroup a).subgroupOf (adjointGroup τ L)

@[expose] noncomputable def famS
                                   {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) : Subgroup (adjointGroup τ L) :=
  ⁅famM a, famM a⁆

@[expose] def IdxConclusion
    {τ : Tag} {L : Type} [Field L]
    {ι : Type} (p : ℕ) (a : ι → Fin τ.rank → Lˣ)
    (F₀ : adjointGroup τ L →* adjointGroup τ L) : Prop :=
  ¬ p ∣ ((Subgroup.closure {x | x ∈ famS a ⊓ F₀.eqLocus (MonoidHom.id _) ∧
      ∃ k : ℕ, x ^ 2 ^ k = 1}).subgroupOf (famS a ⊓ F₀.eqLocus (MonoidHom.id _))).index

@[expose] def cochar
                                      {τ : Tag} {L : Type} [Field L] (lam : Fin τ.rank → ℤ) (c : Lˣ) : Fin τ.rank → Lˣ := fun i => c ^ lam i

@[expose] noncomputable def famZ
                                      {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) : Subgroup (ModGL τ L) :=
  Subgroup.closure {g | ∃ (lam : Fin τ.rank → ℤ) (c : Lˣ),
    (∀ α ∈ familyKernel a, ∑ i, α i * lam i = 0) ∧ g = rootDiagUnit τ (cochar lam c)}

@[expose] def ExcIdxFrobInput :
                                   Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {ι : Type} (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (a : ι → Fin τ.rank → Lˣ) (e : ℕ), 1 ≤ e → ∀ (Q' : ModGL τ L),
      (∀ t, ∃ t', Q' * rootDiagUnit τ t * Q'⁻¹ = rootDiagUnit τ t') →
      (Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
        n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n) →
      ∀ (F₀ : adjointGroup τ L →* adjointGroup τ L),
        (∀ g, (F₀ g : ModGL τ L) = frobTwistGL τ L 2 e Q' g) →
        (∀ g ∈ famM a, F₀ g ∈ famM a) → Finite ↥(F₀.eqLocus (MonoidHom.id _)) →
        CorootPSaturated p (familyKernel a) → IdxConclusion p a F₀

@[expose] def ExcBorelInput :
                                   Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] {ι : Type} (a : ι → Fin τ.rank → Lˣ),
    (∀ g ∈ famZ a, g ∈ adjointGroup τ L ∧ ∀ m ∈ famM a, g * m = m * g) ∧
    (∀ m ∈ famM a, ∃ z ∈ famZ a, ∃ s ∈ famS a, (m : ModGL τ L) = z * s) ∧
    Finite {g : adjointGroup τ L // (g : ModGL τ L) ∈ famZ a ∧ g ∈ famS a} ∧
    IsConnectedAlgebraicSubgroup L ((famZ a).map (modGLPoint τ L).toMonoidHom) ∧
    IsConnectedAlgebraicSubgroup L
      (((famS a).map (adjointGroup τ L).subtype).map (modGLPoint τ L).toMonoidHom)

end CFSG.HardMathSupport.C14Idx
