module

public import CFSG.LocalAnalysis.StandardType.GGLangRatFixedChassis
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate1952
public import Certificates.Certificate13659
import CFSG.LocalAnalysis.StandardType.GGLangRatBFrame
import CFSG.LocalAnalysis.StandardType.GGLangRatBAutSplit
import CFSG.LocalAnalysis.StandardType.GGLangRatBAutUnitary
import CFSG.LocalAnalysis.StandardType.GGLangRatBFrameDiag
import CFSG.LocalAnalysis.StandardType.GGLangRatBFixedPerfect
import CFSG.LocalAnalysis.StandardType.GGLangRatBDiagFixed
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitAct
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6TFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTriKac
import CFSG.RankThree.PartTwo.Sec13.K135MultPrime
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFrame
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPin
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Classical2
open scoped MatrixGroups

private theorem langRatB_mem_core
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {Ψ : Set (Fin τ.rank → ℤ)} {s ν : ℕ} (ψ : SL(ν, L) →* ModGL τ L)
    (hψΨ : ψ.range ≤ rootSpan τ L Ψ) (Φ' : SL(ν, L) ≃* SL(ν, L))
    (hFsψ : ∀ X, iterHom S.D.step s (ψ X) = ψ (Φ' X))
    (hperf : Group.IsPerfect ↥(fixSubgroup Φ')) {D : SL(ν, L)} (hD : Φ' D = D) :
    ψ D ∈ langRatFC_core S Ψ s := by
  have hmem : ψ D ∈ (fixSubgroup Φ').map ψ := ⟨D, (mem_fixSubgroup Φ').2 hD, rfl⟩
  refine (le_iSup₂ (f := fun (H : Subgroup (ModGL τ L)) (_ : H ≤ rootSpan τ L Ψ ∧
    (∀ g ∈ H, iterHom S.D.step s g = g) ∧ Group.IsPerfect ↥H) => H) ((fixSubgroup Φ').map ψ)
    ⟨?_, ?_, ?_⟩) hmem
  · rintro _ ⟨X, -, rfl⟩
    exact hψΨ ⟨X, rfl⟩
  · rintro _ ⟨X, hX, rfl⟩
    rw [hFsψ, (mem_fixSubgroup Φ').1 hX]
  · rw [Subgroup.isPerfect_iff] at hperf ⊢
    rw [← Subgroup.map_commutator, hperf]

private theorem langRatB_diag_split_eq {L : Type} [Field L] {ν : ℕ} (σQ : L ≃+* L) (N : ℕ)
    (hσ : ∀ c, σQ c = c ^ N) (π : Equiv.Perm (Fin ν)) {x y : Fin ν} (u : Lˣ) :
    (fun j => σQ ((fun k : Fin ν =>
        if k = x then (u : L) else if k = y then (((u⁻¹ : Lˣ)) : L) else 1) (π.symm j))) =
      fun j => if j = π x then ((u ^ N : Lˣ) : L)
        else if j = π y then (((u ^ N)⁻¹ : Lˣ) : L) else 1 := by
  funext j
  simp only [Equiv.symm_apply_eq]
  split_ifs <;> simp [hσ]

private theorem langRatB_diag_unitary_eq {L : Type} [Field L] {ν : ℕ} (σQ : L ≃+* L) (N : ℕ)
    (hσ : ∀ c, σQ c = c ^ N) (π : Equiv.Perm (Fin ν)) {x y : Fin ν} (hxy : x ≠ y) (u : Lˣ) :
    (fun j => (σQ ((fun k : Fin ν =>
        if k = x then (u : L) else if k = y then (((u⁻¹ : Lˣ)) : L) else 1) (π.symm j)))⁻¹) =
      fun j => if j = π y then ((u ^ N : Lˣ) : L)
        else if j = π x then (((u ^ N)⁻¹ : Lˣ) : L) else 1 := by
  funext j
  simp only [Equiv.symm_apply_eq]
  by_cases h1 : j = π x
  · subst h1
    have h2 : ¬ π x = π y := fun h2 => hxy (π.injective h2)
    simp [h2, hσ]
  · by_cases h2 : j = π y
    · subst h2
      simp [h1, hσ]
    · simp [h1, h2, hσ]

private theorem langRatB_orbit_diag
    {τ : Tag} (hτ : SimplyLacedTag τ) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {w : WeylGroup τ}
    (hρ : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → S.ρ δ = w • δ) {s ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1)
    (sh : Fin ν × Fin ν → Fin ν × Fin ν)
    (hsh : ∀ p : Fin ν × Fin ν, p.1 ≠ p.2 → (sh p).1 ≠ (sh p).2)
    (hshape : ∀ x y, x ≠ y →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) = σ (sh (x, y)).1 (sh (x, y)).2)
    (Φ' : SL(ν, L) ≃* SL(ν, L))
    (hdiag : ∀ x y : Fin ν, x ≠ y → ∀ (u : Lˣ) (X : SL(ν, L)),
      (X : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun j =>
        if j = x then (u : L) else if j = y then (((u⁻¹ : Lˣ)) : L) else 1) →
      ((Φ' X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun j =>
        if j = (sh (x, y)).1 then ((u ^ S.D.q ^ s : Lˣ) : L)
          else if j = (sh (x, y)).2 then (((u ^ S.D.q ^ s)⁻¹ : Lˣ) : L) else 1))
    {x y : Fin ν} (hxy : x ≠ y) (u : Lˣ) (r : ℕ) (hwr : (w ^ (s * r)) • σ x y = σ x y)
    (hur : u ^ (S.D.q ^ (s * r)) = u) :
    ∃ D : SL(ν, L), Φ' D = D ∧ ψ D = rootDiagUnit τ (∏ t ∈ Finset.range r,
      Hchar ((w ^ (s * t)) • σ x y) (u ^ (S.D.q ^ (s * t)))) := by
  have hiter : ∀ (j : ℕ) (δ : Fin τ.rank → ℤ), IsRoot τ δ →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ = (w ^ j) • δ := by
    intro j
    induction j with
    | zero => intro δ _; simp
    | succ j ih =>
      intro δ hδ
      rw [Function.iterate_succ_apply', hρ _ (S.iterate_isRoot j hδ), ih δ hδ, pow_succ',
        mul_smul]
  let ab : ℕ → Fin ν × Fin ν := fun t => sh^[t] (x, y)
  have hab0 : ab 0 = (x, y) := rfl
  have hab_succ : ∀ t, ab (t + 1) = sh (ab t) := fun t =>
    Function.iterate_succ_apply' sh t (x, y)
  have hne : ∀ t, (ab t).1 ≠ (ab t).2 := by
    intro t
    induction t with
    | zero => exact hxy
    | succ t ih =>
      rw [hab_succ]
      exact hsh _ ih
  have hσab : ∀ t, σ (ab t).1 (ab t).2 = (w ^ (s * t)) • σ x y := by
    intro t
    induction t with
    | zero => simp [hab0]
    | succ t ih =>
      have h1 := hshape (ab t).1 (ab t).2 (hne t)
      rw [Prod.mk.eta] at h1
      rw [hab_succ, ← h1, hiter s _ (hψ.isRoot _ _ (hne t)), ih, ← mul_smul, ← pow_add,
        show s + s * t = s * (t + 1) by ring]
  have hper : ab r = ab 0 := by
    have h1 : σ (ab r).1 (ab r).2 = σ (ab 0).1 (ab 0).2 := by
      rw [hσab r, hwr, hab0]
    have h2 := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T.sigma_injective hψ one_ne_zero
      hnorm (hne r) (hne 0) h1
    exact Prod.ext h2.1 h2.2
  let v : ℕ → Lˣ := fun t => u ^ (S.D.q ^ (s * t))
  have hv_succ : ∀ t, v (t + 1) = v t ^ S.D.q ^ s := by
    intro t
    show u ^ (S.D.q ^ (s * (t + 1))) = (u ^ (S.D.q ^ (s * t))) ^ S.D.q ^ s
    rw [← pow_mul, ← pow_add, show s * t + s = s * (t + 1) by ring]
  have hvr : v r = v 0 := by
    show u ^ (S.D.q ^ (s * r)) = u ^ (S.D.q ^ (s * 0))
    rw [mul_zero, pow_zero, pow_one]
    exact hur
  obtain ⟨D, hD, hDψ⟩ := langRatB_diag_fixed Φ' (fun t => (ab t).1) (fun t => (ab t).2) hne v
    (r := r) (congrArg Prod.fst hper) (congrArg Prod.snd hper) hvr
    (fun t X hX => by
      have h := hdiag (ab t).1 (ab t).2 (hne t) (v t) X hX
      rw [Prod.mk.eta, ← hab_succ, ← hv_succ] at h
      exact h)
    ψ (rootDiagUnitHom τ L) (fun t => Hchar ((w ^ (s * t)) • σ x y) (v t))
    (fun t X hX => by
      have h := langRatB_frame_diag hτ hψ (hne t) (v t) X hX
      rw [h, hσab t]
      rfl)
  exact ⟨D, hD, hDψ⟩

private theorem langRatB_unitary_ne_three_two
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (i : KernelComponent (rootCharHom b)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom b) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)]
        (σ x y) = σ (π y) (π x))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i)) :
    (ν, S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) ≠ (3, 2) := by
  intro h32
  have hcard := (rationalComponent_of_unitary_frame_T S hb i hν hψ hΨ π hπ).2 h32
  have hfin : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) :=
    Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hcard; norm_num at hcard)
  refine CFSG.RankThree.PartTwo.Sec13.F135Last.not_quasisimple_of_card_dvd (a := 3) (b := 3)
    (X := ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i)) ?_ hqs (MulEquiv.refl _)
  exact (Subgroup.index_dvd_card _).trans (by simpa using hcard)

theorem langRatB_localCoreA
    (k : TwistKind) (hk : k = .inner ∨ k = .suN) :
    ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
      (τ = .E7 ∨ τ = .E8) → S.IsAlgebraic → ∀ w : WeylGroup τ,
      S.D.n = canonicalRep (coxeterSystem τ) L w →
      ∀ b : Fin τ.rank → Lˣ, rootDiagUnit τ b ∈ S.D.torus → ∀ i : KernelComponent (rootCharHom b),
        twistKind S.ρ (rootCharHom b) i = k →
        2 ≤ compRank (componentRoots (rootCharHom b) i) →
        (componentRoots (rootCharHom b) i).ncard =
          compRank (componentRoots (rootCharHom b) i) *
            (compRank (componentRoots (rootCharHom b) i) + 1) →
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) →
        ∀ γ ∈ componentRoots (rootCharHom b) i, ∀ (u : Lˣ) (r : ℕ), 0 < r →
          (w ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) • γ = γ →
          u ^ (S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) = u →
          rootDiagUnit τ (∏ t ∈ Finset.range r,
            Hchar ((w ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * t)) • γ)
              (u ^ (S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * t)))) ∈
            langRatFC_core S (componentRoots (rootCharHom b) i)
              (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) := by
  intro τ L _ _ hc2 p₀ S hτ hAlgS w hn b hb i hki h2 hnc hqs γ hγ u r hr hwr hur
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    intro t
    rcases hτ with rfl | rfl <;> cases t <;> decide
  have hSL : SimplyLacedTag τ := by
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hρ : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → S.ρ δ = w • δ := fun δ hδ =>
    S.rho_eq_smul hτ' hn hδ
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hb i
  obtain ⟨m, -, hmL, hTm⟩ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.excTri_exists_order S hb
  obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨ⟩ := langRatB_frame_exists hτ hmL hTm i h2 hnc
  obtain ⟨r₂, e, hr₂, hchar, he, hq⟩ := exists_char_pow S
  have hr₂' : r₂ = 2 := CharP.eq L hchar hc2
  subst hr₂'
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) 2 (e * componentOrbitLength S.ρ
    (componentRoots (rootCharHom b) i))
  have hσc : ∀ c, σQ c = c ^ (2 ^ (e * componentOrbitLength S.ρ
      (componentRoots (rootCharHom b) i))) := fun c => by
    have h1 : σQ c = iterateFrobenius L 2 (e * componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) i)) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) =
      2 ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) := by
    rw [hq, ← pow_mul]
  have hf : 1 ≤ e * componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) :=
    Nat.mul_pos he hs0
  have hAlg2 : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ 2 ^ n = c := by
    intro c
    obtain ⟨n, hn0, hcn⟩ := hAlgS c
    exact ⟨e * n, Nat.mul_pos he hn0, by rw [pow_mul, ← hq]; exact hcn⟩
  have hψΨ : ψ.range ≤ rootSpan τ L (componentRoots (rootCharHom b) i) :=
    le_of_eq (by rw [hψ.range, hΨ])
  have hγΨ := hγ
  rw [hΨ] at hγΨ
  obtain ⟨x, y, hxy, rfl⟩ := hγΨ
  rcases hk with rfl | rfl
  · obtain ⟨π, hπ⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.splitShape_of_twistKind_inner
      S hb i hki hν hψ one_ne_zero hnorm hΨ
    have hFs' : ∀ x y, x ≠ y → ∃ μ : Lˣ, ∀ c : L,
        iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i))
          (pinnedX τ L (σ x y) c) =
          pinnedX τ L (σ (π x) (π y)) ((μ : L) * σQ c) := by
      intro x y hxy
      obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S
        (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) (hψ.isRoot x y hxy)
      refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
      rw [iterHom_eq_iterate, hμ, hπ x y hxy, hσc, ← hQ]
      rfl
    obtain ⟨Φ', hFsψ, ⟨β, hβ⟩, hdg⟩ := langRatB_aut_split hν hψ _ σQ π hFs'
    have hperf := langRatB_fixed_perfect_split hAlg2 hf hν π β Φ'
      (fun x y hxy t => by rw [hβ x y hxy t, hσc t])
    obtain ⟨D, hD, hDψ⟩ := langRatB_orbit_diag hSL S hρ hψ hnorm (fun p => (π p.1, π p.2))
      (fun p hp => π.injective.ne hp) (fun x y hxy => hπ x y hxy) Φ'
      (fun x y hxy u X hX => by
        rw [hdg X _ hX, hQ]
        congr 1
        exact langRatB_diag_split_eq σQ _ hσc π u)
      hxy u r hwr hur
    rw [← hDψ]
    exact langRatB_mem_core S ψ hψΨ Φ' hFsψ hperf hD
  · obtain ⟨π, hπ⟩ := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_perm S hb i hki hν hψ
      one_ne_zero hnorm hΨ
    have hFs' : ∀ x y, x ≠ y → ∃ μ : Lˣ, ∀ c : L,
        iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i))
          (pinnedX τ L (σ x y) c) =
          pinnedX τ L (σ (π y) (π x)) ((μ : L) * σQ c) := by
      intro x y hxy
      obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S
        (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) (hψ.isRoot x y hxy)
      refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
      rw [iterHom_eq_iterate, hμ, hπ x y hxy, hσc, ← hQ]
      rfl
    obtain ⟨Φ', hFsψ, ⟨β, hβ⟩, hdg⟩ := langRatB_aut_unitary hν hψ _ σQ π hFs'
    have hne : (ν, 2 ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom b) i))) ≠
        (3, 2) := by
      rw [← hQ]
      exact langRatB_unitary_ne_three_two S hb i hν hψ hΨ π hπ hqs
    have hperf := langRatB_fixed_perfect_unitary hAlg2 hf hν hne π β Φ'
      (fun x y hxy t => by rw [hβ x y hxy t, hσc t])
    obtain ⟨D, hD, hDψ⟩ := langRatB_orbit_diag hSL S hρ hψ hnorm (fun p => (π p.2, π p.1))
      (fun p hp => (π.injective.ne hp).symm) (fun x y hxy => hπ x y hxy) Φ'
      (fun x y hxy u X hX => by
        rw [hdg X _ hX, hQ]
        congr 1
        exact langRatB_diag_unitary_eq σQ _ hσc π hxy u)
      hxy u r hwr hur
    rw [← hDψ]
    exact langRatB_mem_core S ψ hψΨ Φ' hFsψ hperf hD

end CFSG.StandardType.LangRat
