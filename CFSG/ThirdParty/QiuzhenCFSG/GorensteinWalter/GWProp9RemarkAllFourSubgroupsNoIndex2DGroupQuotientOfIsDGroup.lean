module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuotientTwoGroupNotNormalizerContainsCPrime

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 9 remark under the classification conclusion

This module contains the classification-independent reduction of the second
assertion in the remark after Proposition 9.  Once `IsDGroup G` is supplied,
the all-Klein-four normalizer hypothesis excludes both the index-two branch
of Lemma 2.1 and the two-group quotient constructor of `IsDGroup`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem quotient_isTwoGroup_of_normalPComplement
    {G : Type u} [Group G] [Finite G]
    (hNPC : Glauberman.NormalPComplement 2 G) :
    IsPGroup 2 (G ⧸ pPrimeCore 2 G) := by
  let Q := G ⧸ pPrimeCore 2 G
  let q : G →* Q := QuotientGroup.mk' (pPrimeCore 2 G)
  have htop : Op_p'p 2 G = ⊤ := Glauberman.normalPComplement_eq_top hNPC
  have hmap := congrArg (Subgroup.map q) htop
  have hpcore : pCore 2 Q = ⊤ := by
    simpa [Op_p'p, q, Q,
      Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective (pPrimeCore 2 G)) (pCore 2 Q),
      Subgroup.map_top_of_surjective q
        (QuotientGroup.mk'_surjective (pPrimeCore 2 G))] using hmap
  have htopP : IsPGroup 2 (⊤ : Subgroup Q) := by
    rw [← hpcore]
    exact pCore_isPGroup
  exact htopP.of_equiv Subgroup.topEquiv

/-- The second assertion of the remark after Proposition 9, conditional only
on the classification conclusion `IsDGroup G`. -/
public theorem
    gw_prop9_remark_allFourSubgroups_noIndex2_dGroupQuotient_of_isDGroup
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G)
    (hC' : ∀ Z : Subgroup G, IsKleinFour Z → NormalizerContainsCPrime Z)
    (hD : IsDGroup G) :
    (¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2) ∧ IsDGroupQuotient G := by
  have hnotQ : ¬ IsPGroup 2 (G ⧸ pPrimeCore 2 G) := by
    intro hQ
    let S : Sylow 2 G := Classical.choice Sylow.nonempty
    obtain ⟨m, hm, ⟨e⟩⟩ := hdihedral S
    obtain ⟨Z, _hZS, hZ⟩ :=
      exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
        (S : Subgroup G) hm e
    exact
      quotientTwoGroup_not_normalizerContainsCPrime hQ Z hZ (hC' Z hZ)
  have hno2 : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
    rcases gw_lemma_2_1 hdihedral with hfirst | hrest
    · exact hfirst.1
    rcases hrest with hsecond | hthird
    · exfalso
      rcases hsecond.2.2 with
        ⟨S, _hScard, Z₀, Z₁, _hZ₀S, _hZ₁S, hZ₀, hZ₁,
          _hnotconj, _hcover, hsplit⟩
      rcases hsplit with ⟨_hpos₀, hneg₁⟩ | ⟨_hpos₁, hneg₀⟩
      · exact hneg₁ (hC' Z₁ hZ₁)
      · exact hneg₀ (hC' Z₀ hZ₀)
    · exact False.elim
        (hnotQ (quotient_isTwoGroup_of_normalPComplement hthird.2))
  refine ⟨hno2, ?_⟩
  rcases hD with ⟨_hSylow, hQ⟩ | ⟨_hSylow, eA7⟩ |
      ⟨_hSylow, K, hKprimePower, L, hLnormal, hLindex, hLmodel⟩
  · exact False.elim (hnotQ hQ)
  · exact Or.inl eA7
  ·
    refine Or.inr ⟨L, hLnormal, hLindex, ?_⟩
    rcases hLmodel with hPSL | hPGL
    · exact Or.inl ⟨K, inferInstance, inferInstance, hKprimePower, hPSL⟩
    · exact Or.inr ⟨K, inferInstance, inferInstance, hKprimePower, hPGL⟩

end CFSG.GorensteinWalter
