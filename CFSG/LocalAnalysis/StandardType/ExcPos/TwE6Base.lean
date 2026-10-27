module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

structure ExcBase
    (τ : CFSG.Blueprint.Chevalley.Tag) {X : Type} [Group X] (f p : ℕ)
    (G₀ B₁ D J : Subgroup X) (x : X) : Type where
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

namespace ExcBase

variable
  {X : Type} [Group X] {τ : CFSG.Blueprint.Chevalley.Tag} {f p : ℕ}
  {G₀ B₁ D J : Subgroup X} {x : X}
  (B : ExcBase τ f p G₀ B₁ D J x)

@[expose] def rootsJ : Set (Fin τ.rank → ℤ) :=
  componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) B.iJ

@[expose] def b : ℕ := componentOrbitLength B.ρ B.rootsJ


@[expose] def chiD : Multiplicative (Fin τ.rank → ℤ) →* (ExcOmega f)ˣ × (ExcOmega f)ˣ :=
  LieCore.jointChar (B.coord x) (B.coord B.d)

include B in
theorem x_mem : x ∈ D := by
  rw [← B.closure_eq]
  exact Subgroup.subset_closure (by simp)

theorem mapsTo_rho_chiD : Set.MapsTo B.ρ (kernelRoots B.chiD) (kernelRoots B.chiD) := by
  intro γ hγ
  obtain ⟨hroot, hchar⟩ := hγ
  have hpair : rootChar (B.coord x) γ = 1 ∧ rootChar (B.coord B.d) γ = 1 := by
    simpa [chiD, LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom] using hchar
  refine ⟨(B.frob.isRoot_iff γ).2 hroot, ?_⟩
  have hx : rootChar (B.coord x) (B.ρ γ) = 1 := by
    rw [B.frob.rootChar_eq (B.coord x) (B.coord_torus x B.x_mem) γ hroot, hpair.1, one_pow]
  have hd : rootChar (B.coord B.d) (B.ρ γ) = 1 := by
    rw [B.frob.rootChar_eq (B.coord B.d) (B.coord_torus B.d B.d_mem) γ hroot, hpair.2, one_pow]
  simpa [chiD, LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom] using And.intro hx hd

theorem b_eq_one_or_two : B.b = 1 ∨ B.b = 2 := by
  rcases B.orbit with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

end ExcBase

structure ExcPairData
    {τ : CFSG.Blueprint.Chevalley.Tag} {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase τ f p G₀ B₁ D J x) (R Rm : Subgroup X) :
    Type where
  α : Fin τ.rank → ℤ
  α_mem : α ∈ componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) B.iJ
  wD : ModGL τ (ExcOmega f)
  wD_mem : wD ∈ torusGroup τ (ExcOmega f) ⊔
    rootSpan τ (ExcOmega f) (kernelRoots (LieCore.jointChar (B.coord x) (B.coord B.d)))
  pair_one :
    componentOrbitLength B.ρ (componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) B.iJ) = 1 →
      Nat.card ((R.subgroupOf G₀).map B.η) = Nat.card (GaloisField 2 f) ∧
      (R.subgroupOf G₀).map B.η = excCurve α wD ⊓ B.Δ.model ∧
      Nat.card ((Rm.subgroupOf G₀).map B.η) = Nat.card (GaloisField 2 f) ∧
      (Rm.subgroupOf G₀).map B.η = excCurve (-α) wD ⊓ B.Δ.model ∧
      (excCurve α wD).map B.Δ.step = excCurve α wD ∧
      (excCurve (-α) wD).map B.Δ.step = excCurve (-α) wD
  pair_two :
    componentOrbitLength B.ρ (componentRoots (LieCore.jointChar (B.coord x) (B.coord B.d)) B.iJ) = 2 →
      ((excCurve α wD).map B.Δ.step).map B.Δ.step = excCurve α wD ∧
      (R.subgroupOf G₀).map B.η ≤ excCurve α wD ⊔ (excCurve α wD).map B.Δ.step ∧
      Nat.card ((R.subgroupOf G₀).map B.η) = Nat.card (GaloisField 2 f) ^ 2

@[expose] def ExcPacket.ofBasePair
    {τ : CFSG.Blueprint.Chevalley.Tag} {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X} (B : ExcBase τ f p G₀ B₁ D J x)
    (P : ExcPairData B R Rm) : ExcPacket τ f p G₀ B₁ D J x R Rm where
  one_le_f := B.one_le_f
  Fr := B.Fr
  hFr := B.hFr
  diag := B.diag
  hdiag := B.hdiag
  Δ := B.Δ
  hΦ := B.hΦ
  hq := B.hq
  ρ := B.ρ
  frob := B.frob
  finite := B.finite
  η := B.η
  ker_η := B.ker_η
  range_η := B.range_η
  Θ := B.Θ
  Θ_mem := B.Θ_mem
  Θ_eq_one := B.Θ_eq_one
  η_conj := B.η_conj
  coord := B.coord
  Θ_eq_coord := B.Θ_eq_coord
  coord_pow := B.coord_pow
  coord_torus := B.coord_torus
  d := B.d
  d_mem := B.d_mem
  closure_eq := B.closure_eq
  iJ := B.iJ
  map_J_le := B.map_J_le
  attach_J := B.attach_J
  attach_nbr := B.attach_nbr
  orbit := B.orbit
  α := P.α
  α_mem := P.α_mem
  wD := P.wD
  wD_mem := P.wD_mem
  pair_one := P.pair_one
  pair_two := P.pair_two


@[expose] def ExcPacket.toBase
    {τ : CFSG.Blueprint.Chevalley.Tag} {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X}
    (P : ExcPacket τ f p G₀ B₁ D J x R Rm) : ExcBase τ f p G₀ B₁ D J x where
  one_le_f := P.one_le_f
  Fr := P.Fr
  hFr := P.hFr
  diag := P.diag
  hdiag := P.hdiag
  Δ := P.Δ
  hΦ := P.hΦ
  hq := P.hq
  ρ := P.ρ
  frob := P.frob
  finite := P.finite
  η := P.η
  ker_η := P.ker_η
  range_η := P.range_η
  Θ := P.Θ
  Θ_mem := P.Θ_mem
  Θ_eq_one := P.Θ_eq_one
  η_conj := P.η_conj
  coord := P.coord
  Θ_eq_coord := P.Θ_eq_coord
  coord_pow := P.coord_pow
  coord_torus := P.coord_torus
  d := P.d
  d_mem := P.d_mem
  closure_eq := P.closure_eq
  iJ := P.iJ
  map_J_le := P.map_J_le
  attach_J := P.attach_J
  attach_nbr := P.attach_nbr
  orbit := P.orbit

theorem ExcPacket.ofBasePair_b
    {τ : CFSG.Blueprint.Chevalley.Tag} {X : Type} [Group X] {f p : ℕ}
    {G₀ B₁ D J : Subgroup X} {x : X} {R Rm : Subgroup X} (B : ExcBase τ f p G₀ B₁ D J x)
    (P : ExcPairData B R Rm) : (ExcPacket.ofBasePair B P).b = B.b := rfl

end CFSG.StandardType.LieKnownR2.ExcPos
