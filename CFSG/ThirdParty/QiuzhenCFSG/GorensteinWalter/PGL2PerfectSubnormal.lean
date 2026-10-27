module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

namespace CFSG
end CFSG
open CFSG

/-!
# Perfect subnormal subgroups of odd `PGL₂`

The linear constructor in Bender's `D`-group classification repeatedly needs
the same socle identification: a nontrivial perfect subnormal subgroup of an
odd projective general linear group is its derived `PSL₂` subgroup.  The field
of order three is excluded because `PGL₂(3) ≃ S₄` has solvable derived subgroup
`A₄`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every nontrivial perfect subnormal subgroup of odd `PGL₂(K)` is the
derived `PSL₂(K)` subgroup.  In particular the exceptional field of order
three cannot occur. -/
public theorem pgl2_perfect_subnormal_eq_commutator
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (J : Subgroup (PGL2 K))
    (hJne : J ≠ ⊥) (hJperf : Group.IsPerfect J)
    (hJsn : J.IsSubnormal) :
    3 < Nat.card K ∧ J = commutator (PGL2 K) := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
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
  let : Group.IsPerfect J := hJperf
  have hJcomm : J ≤ commutator (PGL2 K) := by
    rw [← Subgroup.commutator_eq_self (H := J)]
    exact Subgroup.commutator_mono le_top le_top
  have hcard_ne_three : Nat.card K ≠ 3 := by
    intro hcard3
    let : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = 3 := by
      simpa [Nat.card_eq_fintype_card] using hcard3
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let eP : PGL2 K ≃* Equiv.Perm (Fin 4) :=
      (pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm
    let eD : commutator (PGL2 K) ≃* alternatingGroup (Fin 4) :=
      (commutator_mulEquiv_alternatingGroup_of_mulEquiv_perm_four eP).some
    have hDsolv : Group.IsSolvable (commutator (PGL2 K)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 4)) :=
        ⟨⟨2, by
          change ⁅commutator (alternatingGroup (Fin 4)),
            commutator (alternatingGroup (Fin 4))⁆ = ⊥
          rw [← alternatingGroup.kleinFour_eq_commutator (by simp)]
          exact Subgroup.commutator_self_eq_bot_iff.mpr
            (alternatingGroup.kleinFour_isKleinFour (by simp)).isMulCommutative⟩⟩
      exact Group.isSolvable_of_surjective (f := eD.symm.toMonoidHom) eD.symm.surjective
    let D : Subgroup (PGL2 K) := commutator (PGL2 K)
    let JD : Subgroup D := J.subgroupOf D
    let : Group.IsSolvable D := hDsolv
    have : Group.IsSolvable JD := inferInstance
    have hJsolv : Group.IsSolvable J :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hJcomm).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hJcomm).surjective
    let : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).2 hJne
    exact Group.IsPerfect.not_isSolvable J hJsolv
  have hcard_gt : 3 < Nat.card K := by omega
  let D : Subgroup (PGL2 K) := commutator (PGL2 K)
  let JD : Subgroup D := J.subgroupOf D
  have hJDsn : JD.IsSubnormal := hJsn.subgroupOf
  let eD : D ≃* PSL2 K :=
    (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      K hK hcard_gt (MulEquiv.refl (PGL2 K))).some
  have hPSLsimple : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hDsimple : IsSimpleGroup D :=
    (MulEquiv.isSimpleGroup_congr eD).mpr hPSLsimple
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hDsimple hJDsn with
      hJDbot | hJDtop
  · exfalso
    apply hJne
    have hmap : JD.map D.subtype = J :=
      Subgroup.map_subgroupOf_eq_of_le hJcomm
    rw [hJDbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  · refine ⟨hcard_gt, ?_⟩
    apply le_antisymm hJcomm
    intro x hx
    let xD : D := ⟨x, hx⟩
    have hxJD : xD ∈ JD := by
      rw [hJDtop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hxJD

end CFSG.GorensteinWalter
