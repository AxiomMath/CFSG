module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2PerfectSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectSubnormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

namespace CFSG
end CFSG
open CFSG

/-!
# Perfect normal subgroups in odd-index linear models

This is the linear-constructor core needed by the specialized Bender 1.7(v)
absorption in Gorenstein--Walter Lemma 2.5.  A nontrivial perfect normal
subgroup lies in the normal odd-index linear subgroup and becomes its simple
`PSL₂` socle in either the `PSL₂` or `PGL₂` model.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A nontrivial perfect normal subgroup of a finite group is simple when it
lies under a normal odd-index subgroup modeled by odd `PSL₂` or `PGL₂`. -/
public theorem perfect_normal_subgroup_isSimple_of_linear_model
    {Q : Type u} [Group Q] [Finite Q]
    (S L : Subgroup Q)
    (hSnormal : S.Normal) (hSne : S ≠ ⊥)
    (hSperf : Group.IsPerfect S)
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hmodel : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) :
    IsSimpleGroup S := by
  let : L.Normal := hLnormal
  let pi : Q →* Q ⧸ L := QuotientGroup.mk' L
  let I : Subgroup (Q ⧸ L) := S.map pi
  have hIperf : Group.IsPerfect I := by
    dsimp [I]
    let : Group.IsPerfect S := hSperf
    exact Group.IsPerfect.map pi
  have hQodd : Odd (Nat.card (Q ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hLindex
  have hQsolv : Group.IsSolvable (Q ⧸ L) :=
    odd_order_theorem (Q ⧸ L) hQodd
  have hIbot : I = ⊥ := by
    by_contra hIne
    let : Group.IsSolvable (Q ⧸ L) := hQsolv
    have hIsolv : Group.IsSolvable I := inferInstance
    let : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
    let : Group.IsPerfect I := hIperf
    exact Group.IsPerfect.not_isSolvable I hIsolv
  have hSleL : S ≤ L := by
    have hker : S ≤ pi.ker := (Subgroup.map_eq_bot_iff S).mp hIbot
    simpa [pi, QuotientGroup.ker_mk'] using hker
  let SL : Subgroup L := S.subgroupOf L
  let eSL : SL ≃* S := Subgroup.subgroupOfEquivOfLe hSleL
  have hSLne : SL ≠ ⊥ := by
    intro hbot
    apply hSne
    have hmap : SL.map L.subtype = S :=
      Subgroup.map_subgroupOf_eq_of_le hSleL
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hSLperf : Group.IsPerfect SL := by
    let : Group.IsPerfect S := hSperf
    exact Group.IsPerfect.ofSurjective
      (f := eSL.symm.toMonoidHom) eSL.symm.surjective
  have hSLnormal : SL.Normal := by
    dsimp [SL]
    exact Subgroup.Normal.subgroupOf hSnormal L
  have hSLsn : SL.IsSubnormal := hSLnormal.isSubnormal
  rcases hmodel with hPSL | hPGL
  · rcases hPSL with ⟨e⟩
    let J : Subgroup (PSL2 K) := SL.map e.toMonoidHom
    have hJne : J ≠ ⊥ := by
      dsimp [J]
      exact (Subgroup.map_eq_bot_iff_of_injective SL e.injective).not.mpr hSLne
    have hJperf : Group.IsPerfect J := by
      dsimp [J]
      let : Group.IsPerfect SL := hSLperf
      exact Group.IsPerfect.map e.toMonoidHom
    have hJsn : J.IsSubnormal := by
      dsimp [J]
      exact hSLsn.map e.surjective
    obtain ⟨hcard, hJtop⟩ :=
      psl2_perfect_subnormal_eq_top K hK J hJne hJperf hJsn
    let eMap : SL ≃* J :=
      Subgroup.equivMapOfInjective SL e.toMonoidHom e.injective
    let eJtop : J ≃* (⊤ : Subgroup (PSL2 K)) :=
      MulEquiv.subgroupCongr hJtop
    let eSmodel : S ≃* PSL2 K :=
      (((eSL.symm.trans eMap).trans eJtop).trans Subgroup.topEquiv)
    have hPSLsimple : IsSimpleGroup (PSL2 K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact (MulEquiv.isSimpleGroup_congr eSmodel).mpr hPSLsimple
  · rcases hPGL with ⟨e⟩
    let : Finite (PGL2 K) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk
        Matrix.ProjGenLinGroup.mk_surjective
    let J : Subgroup (PGL2 K) := SL.map e.toMonoidHom
    have hJne : J ≠ ⊥ := by
      dsimp [J]
      exact (Subgroup.map_eq_bot_iff_of_injective SL e.injective).not.mpr hSLne
    have hJperf : Group.IsPerfect J := by
      dsimp [J]
      let : Group.IsPerfect SL := hSLperf
      exact Group.IsPerfect.map e.toMonoidHom
    have hJsn : J.IsSubnormal := by
      dsimp [J]
      exact hSLsn.map e.surjective
    obtain ⟨hcard, hJcomm⟩ :=
      pgl2_perfect_subnormal_eq_commutator K hK J hJne hJperf hJsn
    let eMap : SL ≃* J :=
      Subgroup.equivMapOfInjective SL e.toMonoidHom e.injective
    let eJcomm : J ≃* commutator (PGL2 K) :=
      MulEquiv.subgroupCongr hJcomm
    let eComm : commutator (PGL2 K) ≃* PSL2 K :=
      (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
        K hK hcard (MulEquiv.refl (PGL2 K))).some
    let eSmodel : S ≃* PSL2 K :=
      (((eSL.symm.trans eMap).trans eJcomm).trans eComm)
    have hPSLsimple : IsSimpleGroup (PSL2 K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact (MulEquiv.isSimpleGroup_congr eSmodel).mpr hPSLsimple

end CFSG.GorensteinWalter
