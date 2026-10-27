module

public import CFSG.LocalAnalysis.StandardType.GGK0LQDictKinds
public import CFSG.LocalAnalysis.StandardType.GGK0LQInner
public import CFSG.LocalAnalysis.StandardType.GGK0LQSuN
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.Sporadic.ThSchreier.GlobalData

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

theorem k0_rationalComponent_quasisimple
    (hlab : LargeEvenInLambda2 lab)
    (hpair : GGKacExcPair lab p) (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].qs = true) :
    CFSG.IsQuasisimple (rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) := by
  have hp : p.Prime := hpair.1
  have hpL : (p : Omega) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff Omega 2 p).1 h
    exact hpair.2.1 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hTp : rootDiagUnit A.tau A.a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall A.a_pow
  have hτ : A.tau ≠ Tag.G2 := by
    have h : ∀ T : GGKacType, absTag T ≠ Tag.G2 := fun T => by cases T <;> simp [absTag]
    rw [← A.tau_eq]
    exact h A.row.T
  have hp5 : A.tau = Tag.G2 → 5 ≤ p := fun h => absurd h hτ
  obtain ⟨hK1a, hK1b⟩ := lq_K1 hlab A P j hj
  cases hk : twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) with
  | inner =>
    by_cases hQ : 4 ≤ A.setup.D.q ^
        componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j))
    · exact rationalComponent_quasisimple_inner_of_four_leT A.setup
        CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds A.a_torus (P.repr j) hk hQ
    · exact lq_inner_quasisimple_of_not_rank_one A.setup hp A.a_torus hTp A.a_ne (P.repr j) hk
        hp5 (not_le.1 hQ) (hK1a hk (not_le.1 hQ))
  | suN => exact lq_suN_quasisimple A.setup hp hpL A.a_torus hTp (P.repr j) hk (hK1b hk)
  | twoD => exact langSetup_tame_twoD_of_prime A.setup hp hpL A.a_torus hTp A.a_ne (P.repr j) hk
  | exc => exact langSetup_tame_exc_of_prime A.setup hp hpL A.a_torus hTp A.a_ne (P.repr j) hk

end CFSG.StandardType.GGK0MarkedKacIface1587

end
