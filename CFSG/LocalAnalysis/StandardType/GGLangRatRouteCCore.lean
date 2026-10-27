module

public import CFSG.LocalAnalysis.StandardType.GGLangRatFixedChassis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcHighFixE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighStable
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterCartan
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

theorem langRatRouteC_localNorm_of_modelPerfect
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom b) i))
    (hperf : Group.IsPerfect ↥(rootSpan τ L (componentRoots (rootCharHom b) i) ⊓ S.D.model))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom b) i) (u : Lˣ) (r : ℕ)
    (hwr : (w ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) • γ = γ)
    (hur : u ^ (S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) = u) :
    rootDiagUnit τ (∏ j ∈ Finset.range
        (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r),
      Hchar ((w ^ j) • γ) (u ^ S.D.q ^ j)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom b) i := by
  classical
  set Ψ := componentRoots (rootCharHom b) i with hΨdef
  have hs1 : componentOrbitLength S.ρ Ψ = 1 := S.componentOrbitLength_eq_one_of_five_leT hb i h5
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    intro t
    rcases hτ with rfl | rfl <;> cases t <;> decide
  have hSL : SimplyLacedTag τ := by
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hΨroot : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ := S.image_componentRoots_eq_of_five_leT hb i h5
  have hwΨ : ∀ δ ∈ Ψ, w • δ ∈ Ψ := fun δ hδ => by
    rw [← S.rho_eq_smul_of_frob hFr hΦ hn (hΨroot.isRoot δ hδ), ← hst]
    exact ⟨δ, hδ, rfl⟩
  have hwpowΨ : ∀ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ Ψ → (w ^ k) • δ ∈ Ψ := by
    intro k
    induction k with
    | zero => intro δ hδ; simpa using hδ
    | succ k ih => intro δ hδ; rw [pow_succ', mul_smul]; exact hwΨ _ (ih δ hδ)
  rw [hs1, one_mul] at hwr hur
  set x : ModGL τ L := rootDiagUnit τ (∏ t ∈ Finset.range r,
    Hchar ((w ^ (1 * t)) • γ) (u ^ S.D.q ^ (1 * t))) with hxdef
  have hprod : ∀ (n : ℕ) (c : ℕ → Lˣ),
      rootDiagUnit τ (∏ t ∈ Finset.range n, Hchar ((w ^ (1 * t)) • γ) (c t)) ∈
        rootSpan τ L Ψ := by
    intro n c
    induction n with
    | zero => simp [rootDiagUnit_one]
    | succ n ih =>
      rw [Finset.prod_range_succ, rootDiagUnit_mul]
      refine mul_mem ih ?_
      have hδ : (w ^ (1 * n)) • γ ∈ Ψ := hwpowΨ _ γ hγ
      exact rootSpan_mono (fun α hα => by
        rcases hα with rfl | rfl
        · exact hδ
        · exact hΨroot.neg_mem _ hδ) (Hel_root_mem_rootSpan hSL (hΨroot.isRoot _ hδ) _)
  have hxspan : x ∈ rootSpan τ L Ψ := hprod r _
  have hxfix : iterHom S.D.step 1 x = x := by
    rw [hxdef, langRatFC_iterHom_step_prod_stride S hFr hΦ hn γ u 1 r 1]
    congr 1
    have hper : ∀ j, (fun k => Hchar ((w ^ k) • γ) (u ^ S.D.q ^ k)) (j + r) =
        (fun k => Hchar ((w ^ k) • γ) (u ^ S.D.q ^ k)) j := by
      intro j
      simp only
      rw [pow_add, mul_smul, hwr, pow_add, mul_comm (S.D.q ^ j), pow_mul, hur]
    have := langRatFC_prod_range_shift_period (fun k => Hchar ((w ^ k) • γ) (u ^ S.D.q ^ k)) r
      hper 1
    simp only [one_mul] at this ⊢
    rw [← this]
    exact Finset.prod_congr rfl fun k _ => by rw [add_comm]
  have hH : CFSG.LocalAnalysis.GLTheoremA.T171Sh.fixedPointSubgroup (iterHom S.D.step 1)
      (rootSpan τ L Ψ) = rootSpan τ L Ψ ⊓ S.D.model :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.fixedPointSubgroup_step_one S Ψ
  have hcore : x ∈ langRatFC_core S Ψ 1 := by
    refine le_iSup₂ (f := fun (H : Subgroup (ModGL τ L)) (_ : H ≤ rootSpan τ L Ψ ∧
      (∀ g ∈ H, iterHom S.D.step 1 g = g) ∧ Group.IsPerfect ↥H) => H)
      (CFSG.LocalAnalysis.GLTheoremA.T171Sh.fixedPointSubgroup (iterHom S.D.step 1)
        (rootSpan τ L Ψ))
      ⟨fun g hg => hg.1, fun g hg => hg.2, by rw [hH]; exact hperf⟩ ⟨hxspan, hxfix⟩
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] '' Ψ = Ψ := by rw [Function.iterate_one]; exact hst
  have h := langRatFC_norm_factor_mem S hFr hΦ hn hb i (s := 1) hs
    (fun k hk hk1 => absurd hk1 (by omega)) u r hcore
  simpa [hs1] using h

theorem langRatRouteC_modelPerfect_of_fixedData
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom b) i))
    (D : CFSG.LocalAnalysis.GLTheoremA.T171Sh.TwoDExcFixedData S b i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i))) :
    Group.IsPerfect ↥(rootSpan τ L (componentRoots (rootCharHom b) i) ⊓ S.D.model) := by
  have hs1 := S.componentOrbitLength_eq_one_of_five_leT hb i h5
  have hC : D.C = rootSpan τ L (componentRoots (rootCharHom b) i) ⊓ S.D.model := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.T171Sh.fixedPointSubgroup_step_one S]
    ext x
    constructor
    · intro hx
      exact ⟨D.le hx, by rw [← hs1]; exact D.fix x hx⟩
    · rintro ⟨hx, hfix⟩
      exact D.full x hx (by rw [hs1]; exact hfix)
  rw [← hC]
  exact D.perf

end CFSG.StandardType.LangRat

end
