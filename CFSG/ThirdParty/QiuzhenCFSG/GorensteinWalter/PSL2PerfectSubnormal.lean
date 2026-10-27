module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

namespace CFSG
end CFSG
open CFSG

/-!
# Perfect subnormal subgroups of odd `PSL₂`

For odd prime-power fields, a nontrivial perfect subnormal subgroup of
`PSL₂(K)` forces the non-exceptional range `|K| > 3` and is the whole group.
The field of order three is excluded through `PSL₂(3) ≃ A₄`, which is
solvable.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A nontrivial perfect subnormal subgroup of odd `PSL₂(K)` is the whole
group, and the exceptional field of order three cannot occur. -/
public theorem psl2_perfect_subnormal_eq_top
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (J : Subgroup (PSL2 K))
    (hJne : J ≠ ⊥) (hJperf : Group.IsPerfect J)
    (hJsn : J.IsSubnormal) :
    3 < Nat.card K ∧ J = ⊤ := by
  have hcard_ge : 3 ≤ Nat.card K := by
    rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hpodd.not_two_dvd_nat (by simp)
    have hpge : 3 ≤ p := by
      have hp2 := hp.two_le
      omega
    rw [hcard]
    exact hpge.trans (by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn)
  have hcard_ne_three : Nat.card K ≠ 3 := by
    intro hcard3
    let : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = 3 := by
      simpa [Nat.card_eq_fintype_card] using hcard3
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let eP : PSL2 K ≃* alternatingGroup (Fin 4) :=
      (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
    have hPsolv : Group.IsSolvable (PSL2 K) := by
      let : Group.IsSolvable (alternatingGroup (Fin 4)) :=
        ⟨⟨2, by
          change ⁅commutator (alternatingGroup (Fin 4)),
            commutator (alternatingGroup (Fin 4))⁆ = ⊥
          rw [← alternatingGroup.kleinFour_eq_commutator (by simp)]
          exact Subgroup.commutator_self_eq_bot_iff.mpr
            (alternatingGroup.kleinFour_isKleinFour (by simp)).isMulCommutative⟩⟩
      exact Group.isSolvable_of_surjective (f := eP.symm.toMonoidHom) eP.symm.surjective
    let : Group.IsSolvable (PSL2 K) := hPsolv
    have hJsolv : Group.IsSolvable J := inferInstance
    let : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).2 hJne
    let : Group.IsPerfect J := hJperf
    exact Group.IsPerfect.not_isSolvable J hJsolv
  have hcard_gt : 3 < Nat.card K := by omega
  have hPSLsimple : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hPSLsimple hJsn with
      hJbot | hJtop
  · exact False.elim (hJne hJbot)
  · exact ⟨hcard_gt, hJtop⟩

end CFSG.GorensteinWalter
