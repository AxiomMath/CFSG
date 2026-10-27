module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceSolv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem vBig_of_isL2Quot {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (h : IsL2Quot n (oTwoQuot ↥L)) : VBig L :=
  vBig_of_not_isSolvable fun hs => by
    obtain ⟨e⟩ := h
    have : Group.IsSolvable (oTwoQuot ↥L) := isSolvable_oTwoQuot_of_vertex hs
    exact not_isSolvable_psl_two_pow hn
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

end CFSG.Quasithin

