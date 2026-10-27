module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGLatDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
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

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem orbit_perm_eq_one_of_cartan_F4 (π : Equiv.Perm (Fin Tag.F4.rank))
    (h : ∀ i j, Tag.F4.cartan (π i) (π j) = Tag.F4.cartan i j) : π = 1 := by
  have key : ∀ π : Equiv.Perm (Fin Tag.F4.rank),
      (∀ i j, tagCartanEntry .F4 (π i) (π j) = tagCartanEntry .F4 i j) → π = 1 := by
    decide +kernel
  exact key π h

private theorem orbit_sigmaE6_mul_self : excDiagramSigmaE6 * excDiagramSigmaE6 = 1 := by
  decide +kernel

theorem perm_mul_self_eq_one_of_cartan {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) : π * π = 1 := by
  rcases hτ with rfl | rfl | rfl | rfl
  · rw [orbit_perm_eq_one_of_cartan_F4 π hπ, mul_one]
  · rcases perm_eq_one_or_eq_sigma_of_cartan_E6 π hπ with rfl | rfl
    · exact mul_one 1
    · exact orbit_sigmaE6_mul_self
  · rw [perm_eq_one_of_cartan_E7 π hπ, mul_one]
  · rw [perm_eq_one_of_cartan_E8 π hπ, mul_one]

private theorem orbit_latPerm_latPerm {N : ℕ} {π : Equiv.Perm (Fin N)} (h : π * π = 1)
    (v : Fin N → ℤ) : latPerm π (latPerm π v) = v := by
  have hinv : π.symm = π := inv_eq_iff_mul_eq_one.2 h
  funext k
  have hk : π (π k) = k := by
    have := congrArg (fun g : Equiv.Perm (Fin N) => g k) h
    simpa using this
  simp only [latPerm, hinv, hk]

theorem rho_rho_eq_of_latPerm
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (π : Equiv.Perm (Fin τ.rank)) (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : S.ρ (S.ρ γ) = γ := by
  have hππ := perm_mul_self_eq_one_of_cartan hτ π hπ
  have hls : ∀ (c : ℤ) (v : Fin τ.rank → ℤ), latPerm π (c • v) = c • latPerm π v :=
    fun c v => rfl
  rw [hρ _ ((S.frob.isRoot_iff γ).2 hγ), hρ γ hγ, hls, orbit_latPerm_latPerm hππ, smul_smul]
  rcases hε with rfl | rfl <;> simp

private theorem orbit_iterate_eq_or {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρρ : ∀ γ, IsRoot τ γ → ρ (ρ γ) = γ) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (k : ℕ) :
    (ρ : (Fin τ.rank → ℤ) → _)^[k] δ = δ ∨ (ρ : (Fin τ.rank → ℤ) → _)^[k] δ = ρ δ := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h]; exact hρρ δ hδ)

theorem langOrbit_cases_of_rho_rho
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hρρ : ∀ γ, IsRoot τ γ → S.ρ (S.ρ γ) = γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) :
    (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
        rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i) ∨
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
        ∃ j : KernelComponent (rootCharHom a), j ≠ i ∧
          (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
            componentRoots (rootCharHom a) j ∧
          rationalRoots S.ρ (rootCharHom a) i =
            componentRoots (rootCharHom a) i ∪ componentRoots (rootCharHom a) j ∧
          ∀ α ∈ componentRoots (rootCharHom a) i, ∀ β ∈ componentRoots (rootCharHom a) j,
            iform α β = 0) := by
  have hroot : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot τ γ := fun γ hγ => hγ.1.1
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[2] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    ext δ
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have h : (S.ρ : (Fin τ.rank → ℤ) → _)^[2] γ = γ := hρρ γ (hroot γ hγ)
      rw [h]
      exact hγ
    · intro hδ
      exact ⟨δ, hδ, hρρ δ (hroot δ hδ)⟩
  have hle : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 2 :=
    Nat.sInf_le ⟨two_pos, h2⟩
  have hcases : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∨
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 := by omega
  rcases hcases with h1 | h2'
  · left
    refine ⟨h1, ?_⟩
    rw [h1, Function.iterate_one] at hs
    have hmaps : Set.MapsTo (S.ρ : (Fin τ.rank → ℤ) → _) (componentRoots (rootCharHom a) i)
        (componentRoots (rootCharHom a) i) := fun x hx => hs.subset (Set.mem_image_of_mem _ hx)
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      exact hmaps.iterate k hδ
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  · right
    refine ⟨h2', ?_⟩
    obtain ⟨j, hj⟩ := outer_exists_image_component S hT i
    have hne : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i := by
      have h := hmin 1 one_pos (by omega)
      rwa [Function.iterate_one] at h
    have hji : j ≠ i := by
      rintro rfl
      exact hne hj
    refine ⟨j, hji, hj, ?_, ?_⟩
    · rw [← hj]
      ext γ
      constructor
      · rintro ⟨k, δ, hδ, rfl⟩
        rcases orbit_iterate_eq_or hρρ (hroot δ hδ) k with h | h
        · left
          rw [h]
          exact hδ
        · right
          rw [h]
          exact ⟨δ, hδ, rfl⟩
      · rintro (hγ | ⟨δ, hδ, rfl⟩)
        · exact ⟨0, γ, hγ, rfl⟩
        · exact ⟨1, δ, hδ, rfl⟩
    · rintro α ⟨hα, hαi⟩ β ⟨hβ, hβj⟩
      exact iform_eq_zero_of_mk_ne (α := ⟨α, hα⟩) (β := ⟨β, hβ⟩)
        (by rw [hαi, hβj]; exact hji.symm)

end CFSG.StandardType.LangRat
