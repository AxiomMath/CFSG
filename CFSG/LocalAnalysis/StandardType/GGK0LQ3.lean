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

private theorem lk0xlq3_isSolvable_of_commutator {G : Type*} [Group G] (H : Subgroup G)
    (h : Group.IsSolvable ↥⁅H, H⁆) : Group.IsSolvable ↥H := by
  have hle : (commutator ↥H).map H.subtype ≤ ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator]
    simp [Subgroup.map_top, Subgroup.range_subtype]
  let f : ↥(commutator ↥H) →* ↥⁅H, H⁆ :=
    ((H.subtype.comp (commutator ↥H).subtype).codRestrict ⁅H, H⁆
      (fun x => hle ⟨x.1, x.2, rfl⟩))
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥⁅H, H⁆ => (z : G)) hxy
  have key : Group.IsSolvable ↥(commutator ↥H) := Group.isSolvable_of_isSolvable_injective hf
  exact Group.isSolvable_commutator_iff.1 key

theorem k0_rationalSpan_solvable
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    (hj : A.row.D.orbits[j].qs = false) :
    Group.IsSolvable (rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) := by
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
  apply lk0xlq3_isSolvable_of_commutator
  show Group.IsSolvable ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))
  rcases lq_K2 A P j hj with ⟨hk, hq, hrank⟩ | ⟨hk, hrk, hq⟩
  · exact lq_inner_solvable_of_rank_one A.setup hp A.a_torus hTp A.a_ne (P.repr j) hk hp5
      (by rw [hq]; norm_num) hrank
  · exact lq_suN_solvable A.setup hp hpL A.a_torus hTp (P.repr j) hk ⟨hrk, hq⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
