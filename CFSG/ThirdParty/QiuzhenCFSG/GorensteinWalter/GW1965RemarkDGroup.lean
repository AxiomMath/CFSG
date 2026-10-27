module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientDihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalPComplementQuotientPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuotientTwoGroupNotNormalizerContainsCPrime

namespace CFSG
end CFSG
open CFSG

/-!
# The D-group characterization in the remark after Proposition 9

This module proves the first assertion in the remark after Proposition 9 of
Gorenstein--Walter Part II.  It is kept below the `GW1965` wrapper so that the
wrapper can import the completed theorem without an import cycle.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The remark after Proposition 9 (p. 219): a proper subgroup is a `D`-group
in the quotient sense exactly when some Klein four subgroup has
`N_H(Z) ⊃ C'_H(Z)`. -/
public theorem gw_prop9_remark_dGroup_iff_existsFourSubgroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hH : H ≠ ⊤) :
    IsDGroupQuotient H ↔
      ∃ Z : Subgroup (↥H), IsKleinFour Z ∧
        NormalizerContainsCPrime (G := ↥H) Z := by
  constructor
  · intro hDQ
    have hDG : IsDGroup H := properSubgroups_areDGroups hmin H hH
    have hdihedral : HasDihedralSylowTwo H :=
      hasDihedralSylowTwo_of_isDGroup_of_isDGroupQuotient hDG hDQ
    rcases gw_lemma_2_1 hdihedral with hfirst | hsecond | hthird
    · let S : Sylow 2 H := Classical.choice Sylow.nonempty
      obtain ⟨m, hm, ⟨e⟩⟩ := hdihedral S
      obtain ⟨Z, hZS, hZ⟩ :=
        exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
          (S : Subgroup H) hm e
      exact ⟨Z, hZ, hfirst.2.2 S Z hZS hZ⟩
    · rcases hsecond.2.2 with
        ⟨_S, _hScard, Z₀, Z₁, _hZ₀S, _hZ₁S, hZ₀, hZ₁,
          _hnotconj, _hcover, hsplit⟩
      rcases hsplit with ⟨hpos₀, _hneg₁⟩ | ⟨hpos₁, _hneg₀⟩
      · exact ⟨Z₀, hZ₀, hpos₀⟩
      · exact ⟨Z₁, hZ₁, hpos₁⟩
    · exact False.elim
        (not_isPGroup_quotient_pPrimeCore_of_isDGroupQuotient hDQ
          (isPGroup_quotient_pPrimeCore_of_normalPComplement hthird.2))
  · rintro ⟨Z, hZ, hstrict⟩
    have hDG : IsDGroup H := properSubgroups_areDGroups hmin H hH
    rcases hDG with ⟨_hSylow, hQ⟩ | ⟨_hSylow, eA7⟩ |
        ⟨_hSylow, K, hKprimePower, L, hLnormal, hLindex, hLmodel⟩
    · exact False.elim
        (quotientTwoGroup_not_normalizerContainsCPrime hQ Z hZ hstrict)
    · exact Or.inl eA7
    · refine Or.inr ⟨L, hLnormal, hLindex, ?_⟩
      rcases hLmodel with hPSL | hPGL
      · exact Or.inl ⟨K, inferInstance, inferInstance, hKprimePower, hPSL⟩
      · exact Or.inr ⟨K, inferInstance, inferInstance, hKprimePower, hPGL⟩

end CFSG.GorensteinWalter
