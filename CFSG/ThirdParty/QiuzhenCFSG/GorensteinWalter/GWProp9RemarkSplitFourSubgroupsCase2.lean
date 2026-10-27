module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuotientTwoGroupNotNormalizerContainsCPrime
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Split-four-subgroup reduction in the remark after Proposition 9

The split clause of the remark after Proposition 9 (p. 219) assumes two
Klein-four subgroups `Z₀, Z₁` of a dihedral-Sylow group `G` with
`N_G(Z₀) ⊃ C'(Z₀)` and `N_G(Z₁) = C'(Z₁)`.  Lemma 2.1 then leaves exactly
the index-two, no-index-four, two-class branch; the normal-index-four branch
is excluded by the `C'`-strictness of `Z₀` because that branch has a normal
`2`-complement and hence a `2`-group quotient by `O₂'(G)`.

The remaining classification step (a dihedral subgroup of `PΓL₂(K)`
containing `PSL₂(K)` and possessing a self-centralizing Klein four contains
the full `PGL₂(K)` layer) is not present below `GW1965`; it is recorded in
`/tmp/gw1965split-report.md`.  This module contains the acyclic reduction
that is provable with the lower `GWLemma21`/`CPrime`/`DGroupQuotient`
infrastructure.
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

private theorem not_normalizerContainsCPrime_of_eq
    {G : Type u} [Group G] (Z : Subgroup G)
    (h : cPrime Z = (Subgroup.normalizer (Z : Set G) : Set G)) :
    ¬ NormalizerContainsCPrime Z := by
  rintro ⟨_hle, hnotle⟩
  exact hnotle (by rw [h])

private theorem split_forces_case2
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G)
    (Z₀ Z₁ : Subgroup G)
    (hZ₀ : IsKleinFour Z₀) (hZ₁ : IsKleinFour Z₁)
    (hN₀ : NormalizerContainsCPrime Z₀)
    (hN₁ : cPrime Z₁ = (Subgroup.normalizer (Z₁ : Set G) : Set G)) :
    (∃ N : Subgroup G, N.Normal ∧ N.index = 2) ∧
      (¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 4) := by
  have hnotstrict₁ : ¬ NormalizerContainsCPrime Z₁ :=
    not_normalizerContainsCPrime_of_eq Z₁ hN₁
  have hthird : ¬ ((∃ N : Subgroup G, N.Normal ∧ N.index = 4) ∧
      Glauberman.NormalPComplement 2 G) := by
    rintro ⟨_hN4, hNPC⟩
    exact quotientTwoGroup_not_normalizerContainsCPrime
      (quotient_isTwoGroup_of_normalPComplement hNPC) Z₀ hZ₀ hN₀
  have hfirst : ¬ ((¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2) ∧
      (∀ x y : G, IsInvolution x → IsInvolution y → ∃ g : G, g * x * g⁻¹ = y) ∧
      (∀ S : Sylow 2 G, ∀ Z : Subgroup G, Z ≤ (S : Subgroup G) →
        IsKleinFour Z → NormalizerContainsCPrime Z)) := by
    rintro ⟨_hno2, _hallConj, hC'⟩
    have hZp : IsPGroup 2 Z₁ := by
      apply IsPGroup.of_card (n := 2)
      rw [hZ₁.card_four]
      norm_num
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hZp
    exact hnotstrict₁ (hC' S Z₁ hS hZ₁)
  rcases gw_lemma_2_1 hdihedral with hfirst' | hsecond | hthird'
  · exact False.elim (hfirst hfirst')
  · exact ⟨hsecond.1, hsecond.2.1⟩
  · exact False.elim (hthird hthird')

/-- The classification-independent reduction forced by the split
four-subgroup hypotheses of the Proposition 9 remark: `G` has a normal
subgroup of index two and no normal subgroup of index four. -/
public theorem gw_prop9_remark_splitFourSubgroups_case2
    {G : Type u} [Group G] [Finite G]
    (hdihedral : HasDihedralSylowTwo G)
    (Z₀ Z₁ : Subgroup G)
    (hZ₀ : IsKleinFour Z₀) (hZ₁ : IsKleinFour Z₁)
    (hN₀ : NormalizerContainsCPrime Z₀)
    (hN₁ : cPrime Z₁ = (Subgroup.normalizer (Z₁ : Set G) : Set G)) :
    (∃ N : Subgroup G, N.Normal ∧ N.index = 2) ∧
      (¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 4) :=
  split_forces_case2 hdihedral Z₀ Z₁ hZ₀ hZ₁ hN₀ hN₁

end CFSG.GorensteinWalter
