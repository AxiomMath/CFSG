module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeShape
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeCentre
public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KNegCong
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentSU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.H13.J4Order
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.HardMathSupport.Dickson.Sec6
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre
open scoped MatrixGroups

theorem q_pow_mod_three_of_not_twistInner
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (ha : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hi6 : (componentRoots (rootCharHom a) i).ncard = 6)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) % 3 = 2 := by
  classical
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  obtain ⟨ψ, σ, hψ, hnorm, hΨ⟩ := (TwE6UniqAbs.kac_facts h3 ha).frame i hi6
  have hnorm' : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1 := fun x y hxy => by
    rw [mul_one]
    exact hnorm x y hxy
  have hmaps : ∀ x y, x ≠ y →
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1' : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] (σ x y) ∈
        (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] ''
          componentRoots (rootCharHom a) i :=
      ⟨_, h1', rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin Tag.E6.rank → ℤ),
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[n] (-γ) =
        -(S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases (by norm_num) one_ne_zero hnorm'
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s])
      hmaps (hneg s) (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    exfalso
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm one_ne_zero hnorm' π
    refine hout ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨x, y, hxy, rfl⟩ := hγ
      rw [hπ x y hxy, hwσ]
  ·
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm one_ne_zero hnorm' π
    obtain ⟨γ₁, γ₂, hP, hΨeq, hglueAll⟩ := Up34Exc.RD.glue_of_check2 Up34Exc.RD.noG2_E6 73
      Up34Exc.RD.okE6 (by norm_num) Up34Exc.RD.rdCheck2_E6 a ha i hi6
    obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_ne_one h3
    have ha1 : ∃ j, a j ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply h1
      have : a = 1 := funext hcon
      rw [this, rootDiagUnit_one]
    obtain ⟨j0, hj0⟩ := ha1
    obtain ⟨ε, hε, hglue⟩ := hglueAll ω hω3 hω1
    have hw' : w ∈ Subgroup.closure {r : WeylGroup Tag.E6 |
        ∃ γ ∈ componentRoots (rootCharHom a) i, r = rootReflection γ} := by
      rw [hΨ]
      exact hw
    have hnegw : ∀ γ ∈ componentRoots (rootCharHom a) i,
        (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] γ = -(w • γ) := by
      intro γ hγ
      rw [hΨ] at hγ
      obtain ⟨x, y, hxy, rfl⟩ := hγ
      rw [hπ x y hxy, hψ.neg (π x) (π y), hwσ x y]
    exact q_pow_mod_three_of_neg_a2 (s := s) (w := w) S hT i hw' hnegw hP hΨeq hω3 hω1 hε hglue
      ⟨j0, hj0⟩

end CFSG.StandardType.TwE6TwA2K

end
