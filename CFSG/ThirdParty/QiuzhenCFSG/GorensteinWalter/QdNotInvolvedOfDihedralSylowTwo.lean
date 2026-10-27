module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QdSLNotInvolvedOfDihedralSylowTwo
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.InvolvedQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3

namespace CFSG
end CFSG
open CFSG

/-!
# Qd(p) is not involved in a group with dihedral Sylow 2-subgroups

For odd `p`, the canonical `SL₂(p)` complement of `Qd(p)` is already
excluded from every subquotient of a finite group with dihedral Sylow
2-subgroups.  Pulling that complement through an assumed involvement witness
for `Qd(p)` gives the contradiction.
-/

namespace CFSG.GorensteinWalter

open Glauberman

universe u

/-- If a finite group has dihedral Sylow 2-subgroups, then `Qd(p)` is not
involved for any odd prime `p`. -/
public theorem qd_not_involved_of_hasDihedralSylowTwo
    {G : Type u} [Group G] [Finite G]
    (hG : HasDihedralSylowTwo G)
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) :
    ¬ Involved (Qd p) G := by
  intro hQd
  apply qdSL_not_involved_of_hasDihedralSylowTwo hG hpodd
  rcases hQd with ⟨K, N, hN, ⟨e⟩⟩
  let : N.Normal := hN
  let L : Subgroup (Qd p) :=
    (SemidirectProduct.inr : qdSL p →* Qd p).range
  let eSL : qdSL p ≃* L :=
    MulEquiv.ofBijective
      (SemidirectProduct.inr : qdSL p →* Qd p).rangeRestrict
      ⟨(fun _ _ hxy ↦
          SemidirectProduct.inr_injective (congrArg Subtype.val hxy)),
        (SemidirectProduct.inr : qdSL p →* Qd p).rangeRestrict_surjective⟩
  let L' : Subgroup (K ⧸ N) := L.map e.symm.toMonoidHom
  let eL : L ≃* L' :=
    Subgroup.equivMapOfInjective L e.symm.toMonoidHom e.symm.injective
  have hL' : Involved L' (K ⧸ N) := involved_of_subgroup L'
  have hSLquot : Involved (qdSL p) (K ⧸ N) :=
    (Involved_iff_of_mulEquiv (eSL.trans eL)).mpr hL'
  have hSLK : Involved (qdSL p) K :=
    involved_of_involved_quotient N hSLquot
  exact involved_of_involved_subgroup hSLK

end CFSG.GorensteinWalter
