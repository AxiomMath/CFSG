module

public import CFSG.RankThree.PartOne.KF.F4Torus
public import CFSG.RankThree.Chevalley.SteinbergCFLargeReeSplitSylow

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeCover
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint

variable {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exists_conj_into_Tp4
    (h : F4Param p a K) (X : Subgroup ↥(F4.reeGamma K a))
    (hX : ∀ x ∈ X, x ^ p = 1) : ∃ g : ↥(F4.reeGamma K a), ∀ x ∈ X, g * x * g⁻¹ ∈ Tp4 h :=
  exists_conj_into_Tp4_of h
    (fun R hR hRp => (CFSG.RankThree.Chevalley.large_Ree_split_torus_contains_Sylow_prime_subgroups
      a K h.card h.prime (by have := h.five_le; omega) h.dvd).2.2 R hR hRp)
    (fun x hx => CFSG.LieType.Ree.LargeReeInvolution.rankOne_exists_torusPair_eq h.card hx) X hX

end CFSG.RankThree.PartOne.KFU
