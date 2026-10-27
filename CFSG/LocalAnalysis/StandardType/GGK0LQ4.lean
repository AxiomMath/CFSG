module

public import CFSG.LocalAnalysis.StandardType.GGK0LQDict
public import CFSG.LocalAnalysis.StandardType.GGK0LQS3
public import CFSG.LocalAnalysis.StandardType.GGK0LQAlgSetup
public import CFSG.LocalAnalysis.StandardType.GGLangModelIndex
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0LQ
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private noncomputable def lk0xlq4_fullFactor_equiv_rationalSpan
    (A : K0LangMark Omega lab p R I phi) (c : KernelComponent (rootCharHom A.a)) :
    fullFactor A.setup A.iota A.a c ≃* rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) c := by
  have hle : rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) c ≤ A.iota.range := by
    rw [A.iota_range]
    exact inf_le_right
  refine (Subgroup.equivMapOfInjective (fullFactor A.setup A.iota A.a c) A.iota A.iota_inj).trans ?_
  refine MulEquiv.subgroupCongr ?_
  rw [fullFactor, Subgroup.map_comap_eq]
  exact inf_eq_right.mpr hle

theorem k0_fullFactor_a12
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (hAlg : ∀ c : Omega, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    (hj : A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩) (hqs : A.row.D.orbits[j].qs = false) :
    Nonempty ((fullFactor A.setup A.iota A.a (P.repr j)) ≃* Equiv.Perm (Fin 3)) := by
  have hp : p.Prime := hpair.1
  have hTp : rootDiagUnit A.tau A.a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall A.a_pow
  have hτ : A.tau ≠ Tag.G2 := by
    have h : ∀ T : GGKacType, absTag T ≠ Tag.G2 := fun T => by cases T <;> simp [absTag]
    rw [← A.tau_eq]
    exact h A.row.T
  have hp5 : A.tau = Tag.G2 → 5 ≤ p := fun h => absurd h hτ
  obtain ⟨hk, hq, hrank⟩ := lq_K4 A P j hj hqs
  have hτ4 : A.tau = .F4 ∨ A.tau = .E6 ∨ A.tau = .E7 ∨ A.tau = .E8 := by
    have h : ∀ T : GGKacType, absTag T = .F4 ∨ absTag T = .E6 ∨ absTag T = .E7 ∨ absTag T = .E8 :=
      fun T => by cases T <;> simp [absTag]
    rw [← A.tau_eq]
    exact h A.row.T
  have hInv : ∀ m ∈ A.setup.D.model, m ^ 2 = 1 → m ∈ A.setup.Γ := fun m hm hm2 =>
    CFSG.StandardType.LangRat.langModel_mem_Γ_of_sq_eq_one (S := A.setup) hτ4 A.q_eq
      (lq_setup_isAlgebraic hAlg A) hm hm2
  obtain ⟨e⟩ := lq_span_s3 A.setup hp A.a_torus hTp A.a_ne (P.repr j) hk hp5 hq hrank hInv
  exact ⟨(lk0xlq4_fullFactor_equiv_rationalSpan A (P.repr j)).trans e⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
