module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.SpecificGroups.KleinFour

namespace CFSG
end CFSG
open CFSG

/-!
# The `|K| = 3` exceptional case of the split-four local endpoint

For `K = 𝔽₃` the coefficient automorphism group is trivial, so
`PΓL₂(K)` is the full `PGL₂(K) ≅ S₄` layer.  A subgroup containing the
canonical `PSL₂(K) ≅ A₄` layer therefore has order `12` or `24`.

The order-`12` alternative is exactly the `PSL₂(K)` layer.  There,
Gorenstein--Walter Lemma 2.1 applies (the layer has no normal subgroup of
index two or four) and supplies, for the given Klein-four subgroup, the
strict inequality `C'(Z) ⊊ N(Z)`, contradicting the hypothesis.
The order-`24` alternative is the full `PGL₂(K)` layer, which gives the
conclusion directly.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem ringEquiv_card_three_subsingleton
    {K : Type u} [Field K] [Finite K]
    (hcard : Nat.card K = 3) :
    Subsingleton (K ≃+* K) := by
  letI : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  let e : ZMod 3 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  have h_id (σ : K ≃+* K) : σ = RingEquiv.refl K := by
    apply RingEquiv.ext
    intro x
    have hσe : (e.trans σ).trans e.symm = RingEquiv.refl (ZMod 3) := by
      apply RingEquiv.ext
      intro z
      have hh := RingHom.ext_zmod ((e.trans σ).trans e.symm).toRingHom
        (RingEquiv.refl (ZMod 3)).toRingHom
      have hf :
          (((e.trans σ).trans e.symm) : ZMod 3 → ZMod 3) =
            ((RingEquiv.refl (ZMod 3)) : ZMod 3 → ZMod 3) := by
        exact congrArg
          (fun f : ZMod 3 →+* ZMod 3 => (f : ZMod 3 → ZMod 3)) hh
      exact congrFun hf z
    calc
      σ x = e (e.symm (σ x)) := by simp
      _ = e ((e.trans σ).trans e.symm (e.symm x)) := by
        simp [RingEquiv.trans_apply]
      _ = e (e.symm x) := by rw [hσe]; simp
      _ = x := by simp
  exact ⟨fun σ τ => by rw [h_id σ, h_id τ]⟩

private theorem alternatingGroupFour_no_normal_index_two_or_four
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* alternatingGroup (Fin 4)) :
    (¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2) ∧
      (¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 4) := by
  have hGcard : Nat.card G = 12 := by
    calc
      Nat.card G = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr e.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hmap : (commutator G).map e.toMonoidHom =
      commutator (alternatingGroup (Fin 4)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  let eComm : commutator G ≃* commutator (alternatingGroup (Fin 4)) :=
    (Subgroup.equivMapOfInjective (commutator G) e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hmap)
  have hcommCard : Nat.card (commutator G) = 4 := by
    calc
      Nat.card (commutator G) =
          Nat.card (commutator (alternatingGroup (Fin 4))) :=
        Nat.card_congr eComm.toEquiv
      _ = Nat.card (alternatingGroup.kleinFour (Fin 4)) := by
        rw [alternatingGroup.kleinFour_eq_commutator (by simp)]
      _ = 4 := alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  constructor
  · rintro ⟨N, hNnormal, hNindex⟩
    have hcomm_le := commutator_le_of_normal_index_two N hNnormal hNindex
    have h4dvd : 4 ∣ Nat.card N := by
      rw [← hcommCard]
      exact Subgroup.card_dvd_of_le hcomm_le
    have hNcard : Nat.card N = 6 := by
      have hm := N.index_mul_card
      rw [hNindex, hGcard] at hm
      omega
    omega
  · rintro ⟨N, hNnormal, hNindex⟩
    have hcomm_le := commutator_le_of_normal_index_four N hNnormal hNindex
    have h4dvd : 4 ∣ Nat.card N := by
      rw [← hcommCard]
      exact Subgroup.card_dvd_of_le hcomm_le
    have hNcard : Nat.card N = 3 := by
      have hm := N.index_mul_card
      rw [hNindex, hGcard] at hm
      omega
    omega

/-- The `|K| = 3` case of the large-field local endpoint: a subgroup of
`PΓL₂(K)` containing `PSL₂(K)` and a Klein four with `C'(Z) = N(Z)` must
contain the full `PGL₂(K)` layer. -/
public theorem pGammaL2_contains_pgl_of_selfCentralizing_four_cardThree
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : Nat.card K = 3)
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hAd : HasDihedralSylowTwo A)
    (Z : Subgroup A) (hZ : IsKleinFour Z)
    (hN : cPrime Z = (Subgroup.normalizer (Z : Set A) : Set A)) :
    pGammaL2PGLRange K ≤ A := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  haveI : Subsingleton (K ≃+* K) := ringEquiv_card_three_subsingleton hcard
  letI : Finite (K ≃+* K) := inferInstance
  letI : Fintype (K ≃+* K) := Fintype.ofFinite _
  letI : Finite (PGammaL2 K) :=
    Finite.of_injective (fun x : PGammaL2 K => (x.left, x.right)) (by
      intro x y hxy
      exact SemidirectProduct.ext
        (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  letI : Finite (↥A) := inferInstance
  have hAutCard : Nat.card (K ≃+* K) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_eq_one_iff).2
      ⟨RingEquiv.refl K, fun σ => Subsingleton.elim σ (RingEquiv.refl K)⟩
  have hQcard : Nat.card (PGammaL2 K ⧸ pGammaL2PGLRange K) = 1 := by
    have h := Nat.card_congr (pGammaL2QuotientPGL2 K).toEquiv
    simpa [pGammaL2PGLRange] using h.trans hAutCard
  have hRindex : (pGammaL2PGLRange K).index = 1 := by
    rw [Subgroup.index_eq_card]
    exact hQcard
  have hRtop : pGammaL2PGLRange K = ⊤ := Subgroup.index_eq_one.mp hRindex
  have hRcard24 : Nat.card (↥(pGammaL2PGLRange K)) = 24 := by
    have h := Nat.card_congr (pGammaL2PGLRangeEquiv K).toEquiv
    rw [pgl2_card_formula K, hcard] at h
    norm_num at h
    exact h.symm
  have hGcard : Nat.card (PGammaL2 K) = 24 := by
    calc
      Nat.card (PGammaL2 K) = Nat.card (↥(pGammaL2PGLRange K)) := by
        rw [hRtop, Subgroup.card_top]
      _ = 24 := hRcard24
  have hP0card : Nat.card (↥(pGammaL2PSLRange K)) = 12 := by
    have h := Nat.card_congr (pGammaL2PSLRangeEquiv K).toEquiv
    rw [psl2_card_formula K hK, hcard] at h
    norm_num at h
    exact h.symm
  have h12dvd : 12 ∣ Nat.card (↥A) := by
    have hc := Subgroup.card_dvd_of_le
      (H := pGammaL2PSLRange K) (K := A) hPSL
    rwa [hP0card] at hc
  have hAdvd24 : Nat.card (↥A) ∣ 24 := by
    have hc := Subgroup.card_dvd_of_le
      (H := A) (K := ⊤) (le_top : A ≤ ⊤)
    rwa [Subgroup.card_top, hGcard] at hc
  rcases h12dvd with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    exact Nat.card_pos.ne' hk
  have hk_le : k ≤ 2 := by
    have hle : Nat.card (↥A) ≤ 24 :=
      Nat.le_of_dvd (by norm_num : 0 < 24) hAdvd24
    rw [hk] at hle
    omega
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl
  · have hAeqP0 : A = pGammaL2PSLRange K := by
      exact (Subgroup.eq_of_le_of_card_ge hPSL (by
        simp [hk, hP0card])).symm
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three (by
        simpa [Nat.card_eq_fintype_card] using hcard)
    let eA4 : ↥A ≃* alternatingGroup (Fin 4) :=
      (MulEquiv.subgroupCongr hAeqP0).trans
        ((pGammaL2PSLRangeEquiv K).symm.trans
          (((psl2RingEquiv eK).symm).trans psl2_three_equiv_alternatingGroup))
    rcases alternatingGroupFour_no_normal_index_two_or_four eA4 with
      ⟨hno2, hno4⟩
    rcases gw_lemma_2_1 hAd with hfirst | hsecond | hthird
    · have hZp : IsPGroup 2 Z := by
        apply IsPGroup.of_card (n := 2)
        rw [hZ.card_four]
        norm_num
      obtain ⟨S, hZleS⟩ := IsPGroup.exists_le_sylow hZp
      have hstrict := hfirst.2.2 S Z hZleS hZ
      change cPrime Z ⊂
        (Subgroup.normalizer (Z : Set A) : Set A) at hstrict
      rw [hN] at hstrict
      exact (lt_irrefl _ hstrict).elim
    · exact False.elim (hno2 hsecond.1)
    · exact False.elim (hno4 hthird.1)
  · have hAtop : A = ⊤ := by
      apply Subgroup.eq_top_of_card_eq A
      simp [hk, hGcard]
    rw [hAtop]
    exact le_top

end CFSG.GorensteinWalter
