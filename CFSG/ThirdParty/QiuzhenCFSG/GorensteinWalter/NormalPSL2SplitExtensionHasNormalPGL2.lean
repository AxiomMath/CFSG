module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2ContainsPGLSelfCentralizingFourAll
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeNormalExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGroupExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime

namespace CFSG
end CFSG
open CFSG

/-!
# The split-four normal-extension lift

Given a self-centralizing normal `N ≃ PSL₂(K)` in a finite group `G` with
dihedral Sylow `2`-subgroups and trivial odd core, conjugation embeds `G`
faithfully into `PΓL₂(K)`.  For `|K| > 3` this is the existing
`normalPSL2ToPGammaL2` embedding; the transported `C'(Z) = N(Z)` Klein four
`Z₁` then forces the image subgroup to contain the full `PGL₂(K)` layer via
the all-fields local dispatcher, and pulling that layer back gives the normal
`PGL₂(K)` subgroup of `G`.

For `|K| = 3`, the same extension is handled through the faithful
`Aut(A₄) ≅ S₄` argument: the normal `PSL₂(3)` core has index either one or
two.  Index one is excluded by Lemma 2.1 and `C'(Z₁) = N(Z₁)`; index two
gives `G ≅ PGL₂(3)`, so the top subgroup is the required normal `PGL₂(K)`
layer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem centralizer_map_bijective
    {G H : Type u} [Group G] [Group H]
    (Z : Subgroup G) (e : G ≃* H) :
    Subgroup.centralizer ((Z.map e.toMonoidHom : Subgroup H) : Set H) =
      (Subgroup.centralizer (Z : Set G)).map e.toMonoidHom := by
  apply le_antisymm
  · intro x hx
    let g : G := e.symm x
    refine ⟨g, ?_, ?_⟩
    · change g ∈ Subgroup.centralizer (Z : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact e.injective (by
        calc
          e (z * g) = e z * x := by simp [g]
          _ = x * e z := by
            have hx' := (Subgroup.mem_centralizer_iff.mp hx) (e z)
              (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
            exact hx'
          _ = e (g * z) := by simp [g])
    · simp [g]
  · exact Subgroup.map_centralizer_le_centralizer_image (Z : Set G) e.toMonoidHom

private theorem cPrime_map_bijective
    {G H : Type u} [Group G] [Group H]
    (Z : Subgroup G) (e : G ≃* H)
    (h : cPrime Z = (Subgroup.normalizer (Z : Set G) : Set G)) :
    cPrime (Z.map e.toMonoidHom) =
      (Subgroup.normalizer ((Z.map e.toMonoidHom : Subgroup H) : Set H)) := by
  have hNorm : (Subgroup.normalizer (Z : Set G)).map e.toMonoidHom =
      Subgroup.normalizer ((Z.map e.toMonoidHom : Subgroup H) : Set H) := by
    exact Subgroup.map_equiv_normalizer_eq Z e
  have hCent : Subgroup.centralizer ((Z.map e.toMonoidHom : Subgroup H) : Set H) =
      (Subgroup.centralizer (Z : Set G)).map e.toMonoidHom :=
    centralizer_map_bijective Z e
  have hC : cPrime (Z.map e.toMonoidHom) =
      {x : H | ∃ g : G, g ∈ cPrime Z ∧ e g = x} := by
    ext x
    constructor
    · intro hx
      have hxn : x ∈ Subgroup.normalizer
          ((Z.map e.toMonoidHom : Subgroup H) : Set H) := hx.1
      have hxc : x ^ 2 ∈ Subgroup.centralizer
          ((Z.map e.toMonoidHom : Subgroup H) : Set H) := hx.2
      rw [← hNorm] at hxn
      rw [hCent] at hxc
      rcases hxn with ⟨g, hgN, hgx⟩
      rcases hxc with ⟨c, hcC, hcx⟩
      have hg2 : g ^ 2 = c := by
        apply e.injective
        calc
          e (g ^ 2) = x ^ 2 := by rw [← hgx]; simp
          _ = e c := hcx.symm
      refine ⟨g, ⟨hgN, ?_⟩, hgx⟩
      simpa [hg2] using hcC
    · rintro ⟨g, hg, rfl⟩
      exact ⟨by rw [← hNorm]; exact Subgroup.mem_map.mpr ⟨g, hg.1, rfl⟩,
             by rw [hCent]; exact Subgroup.mem_map.mpr ⟨g ^ 2, hg.2, by simp⟩⟩
  have hC' : {x : H | ∃ g : G, g ∈ cPrime Z ∧ e g = x} =
      {x : H | ∃ g : G,
        g ∈ (Subgroup.normalizer (Z : Set G) : Set G) ∧ e g = x} := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, by rwa [h] at hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, by rwa [← h] at hg, rfl⟩
  calc
    cPrime (Z.map e.toMonoidHom) =
        {x : H | ∃ g : G, g ∈ cPrime Z ∧ e g = x} := hC
    _ = {x : H | ∃ g : G,
        g ∈ (Subgroup.normalizer (Z : Set G) : Set G) ∧ e g = x} := hC'
    _ = ((Subgroup.normalizer (Z : Set G)).map e.toMonoidHom : Set H) := by
      ext x
      simp
    _ = (Subgroup.normalizer
        ((Z.map e.toMonoidHom : Subgroup H) : Set H) : Set H) := by
      exact congrArg (fun S : Subgroup H => (S : Set H)) hNorm

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

private theorem normal_PSL2_split_extension_has_normal_PGL2_cardThree
    {G : Type u} [Group G] [Finite G]
    (hSylow : HasDihedralSylowTwo G)
    (N : Subgroup G) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : Nat.card K = 3)
    (e : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (Z₁ : Subgroup G) (hZ₁ : IsKleinFour Z₁)
    (hN₁ : cPrime Z₁ = (Subgroup.normalizer (Z₁ : Set G) : Set G)) :
    ∃ L : Subgroup G, L.Normal ∧ IsIsoToPGL2OddExists (G := G) L := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  let eK : ZMod 3 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eN3 : N ≃* PSL2 (ZMod 3) := e.trans (psl2RingEquiv eK).symm
  let eHA4 : PSL2 (ZMod 3) ≃* alternatingGroup (Fin 4) :=
    psl2_three_equiv_alternatingGroup
  rcases quotient_centralizer_mulAut_embedding N with ⟨φ, hφ⟩
  let q : G ≃* G ⧸ Subgroup.centralizer (N : Set G) :=
    ((QuotientGroup.quotientMulEquivOfEq (G := G) hC).trans
      (QuotientGroup.quotientBot (G := G))).symm
  let ψ : G →* MulAut N := φ.comp q.toMonoidHom
  have hψ : Function.Injective ψ := hφ.comp q.injective
  let ρ : G →* MulAut (PSL2 (ZMod 3)) :=
    (MulAut.congr eN3).toMonoidHom.comp ψ
  have hρ : Function.Injective ρ := (MulAut.congr eN3).injective.comp hψ
  have hHcard : Nat.card N = 12 := by
    exact (Nat.card_congr eN3.toEquiv).trans nat_card_psl2_zmod3
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  let c : Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 4))
  have hc : Function.Bijective c :=
    GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  let eAut : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
    MulEquiv.ofBijective c hc
  have hAutAcard : Nat.card (MulAut (alternatingGroup (Fin 4))) = 24 :=
    (Nat.card_congr eAut.toEquiv).symm.trans hPermCard
  have hAutPSLcard : Nat.card (MulAut (PSL2 (ZMod 3))) = 24 := by
    calc
      Nat.card (MulAut (PSL2 (ZMod 3))) =
          Nat.card (MulAut (alternatingGroup (Fin 4))) :=
        Nat.card_congr (MulAut.congr eHA4).toEquiv
      _ = 24 := hAutAcard
  have hGle : Nat.card G ≤ 24 :=
    (Nat.card_le_card_of_injective ρ hρ).trans_eq hAutPSLcard
  have hHdvd : Nat.card N ∣ Nat.card G := N.card_subgroup_dvd_card
  obtain ⟨k, hk⟩ := hHdvd
  rw [hHcard] at hk
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    exact Nat.card_pos.ne' hk
  have hkle : k ≤ 2 := by
    have hle : Nat.card G ≤ 24 := hGle
    rw [hk] at hle
    omega
  have hkcases : k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl
  · have hNtop : N = ⊤ := by
      apply Subgroup.eq_top_of_card_eq N
      rw [hHcard, hk]
    let eGN : G ≃* N :=
      ((MulEquiv.subgroupCongr hNtop).trans (Subgroup.topEquiv (G := G))).symm
    let eG3 : G ≃* PSL2 (ZMod 3) := eGN.trans eN3
    rcases alternatingGroupFour_no_normal_index_two_or_four
        (eG3.trans eHA4) with ⟨hno2, hno4⟩
    rcases gw_lemma_2_1 hSylow with hfirst | hsecond | hthird
    · have hZp : IsPGroup 2 Z₁ := by
        apply IsPGroup.of_card (n := 2)
        rw [hZ₁.card_four]
        norm_num
      obtain ⟨S, hZleS⟩ := IsPGroup.exists_le_sylow hZp
      have hstrict : NormalizerContainsCPrime Z₁ :=
        hfirst.2.2 S Z₁ hZleS hZ₁
      rw [NormalizerContainsCPrime, hN₁] at hstrict
      exact (lt_irrefl _ hstrict).elim
    · exact False.elim (hno2 hsecond.1)
    · exact False.elim (hno4 hthird.1)
  · have hGcard : Nat.card G = 24 := by
      simpa using hk
    have hρbij : Function.Bijective ρ :=
      (Nat.bijective_iff_injective_and_card ρ).mpr
        ⟨hρ, hGcard.trans hAutPSLcard.symm⟩
    let eGAutH : G ≃* MulAut (PSL2 (ZMod 3)) := MulEquiv.ofBijective ρ hρbij
    let eGS4 : G ≃* Equiv.Perm (Fin 4) :=
      (eGAutH.trans (MulAut.congr eHA4)).trans eAut.symm
    let eGPGL3 : G ≃* PGL2 (ZMod 3) := eGS4.trans pgl2_three_equiv_perm.symm
    let eGPGLK : G ≃* PGL2 K := eGPGL3.trans (pgl2RingEquiv eK)
    refine ⟨⊤, inferInstance, ?_⟩
    refine ⟨K, inferInstance, inferInstance, ?_⟩
    refine ⟨hK, ⟨(Subgroup.topEquiv (G := G)).trans eGPGLK⟩⟩

/-- The split-four normal-extension lift: a self-centralizing normal
`PSL₂(K)` core in a dihedral-Sylow group with trivial odd core and a split
Klein-four pair forces a normal `PGL₂(K)` subgroup of `G`. -/
public theorem normal_PSL2_split_extension_has_normal_PGL2
    {G : Type u} [Group G] [Finite G]
    (hSylow : HasDihedralSylowTwo G)
    (hO : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : N ≃* PSL2 K)
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (Z₀ Z₁ : Subgroup G)
    (hZ₀ : IsKleinFour Z₀) (hZ₁ : IsKleinFour Z₁)
    (hN₀ : NormalizerContainsCPrime Z₀)
    (hN₁ : cPrime Z₁ = (Subgroup.normalizer (Z₁ : Set G) : Set G)) :
    ∃ L : Subgroup G, L.Normal ∧ IsIsoToPGL2OddExists (G := G) L := by
  classical
  rcases hK with ⟨p, f, hp, hpodd, hf, hKcard⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hK' : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hpodd, hf, hKcard⟩
  by_cases hcard3 : Nat.card K = 3
  · exact normal_PSL2_split_extension_has_normal_PGL2_cardThree
      hSylow N K hK' hcard3 e hC Z₁ hZ₁ hN₁
  · have hcardgt : 3 < Nat.card K := by
      have hpge3 : 3 ≤ p := by
        have hp_ne2 : p ≠ 2 := by
          intro hp2
          subst p
          exact hpodd.not_two_dvd_nat (by simp)
        have hp_two : 2 ≤ p := hp.two_le
        omega
      have hq : Nat.card K = p ^ f := hKcard
      by_cases hf1 : f = 1
      · subst f
        have hq1 : Nat.card K = p := by simpa using hq
        by_cases hp3eq : p = 3
        · exfalso
          exact hcard3 (by rw [hq1, hp3eq])
        · omega
      · have hfge2 : 2 ≤ f := by omega
        rw [hq]
        have h9le : 9 ≤ p ^ 2 := by
          have h := Nat.pow_le_pow_left hpge3 2
          norm_num at h
          exact h
        have hp2le : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos hfge2
        omega
    let fmap : G →* PGammaL2 K :=
      normalPSL2ToPGammaL2 N K hK' hcardgt e
        (pGammaL2ToMulAutPSL2_surjective K hKcard hK' hcardgt)
    have hfmap : Function.Injective fmap := by
      dsimp [fmap]
      exact normalPSL2ToPGammaL2_injective N K hK' hcardgt e hC _
    let A : Subgroup (PGammaL2 K) := fmap.range
    let eG : G ≃* A := MulEquiv.ofBijective fmap.rangeRestrict
      ⟨fun a b hab => hfmap (congrArg Subtype.val hab),
        fmap.rangeRestrict_surjective⟩
    letI : Finite A := Finite.of_surjective eG eG.surjective
    have hA : HasDihedralSylowTwo A :=
      hasDihedralSylowTwo_of_mulEquiv eG.symm hSylow
    have hPSL : pGammaL2PSLRange K ≤ A := by
      dsimp [A, fmap]
      exact normalPSL2ToPGammaL2_range_contains_psl N K hK' hcardgt e _
    let Z : Subgroup A := Z₁.map eG.toMonoidHom
    have hZ : IsKleinFour Z := isKleinFour_map_mulEquiv_cross Z₁ hZ₁ eG
    have hZN : cPrime Z =
        (Subgroup.normalizer (Z : Set A) : Set A) :=
      cPrime_map_bijective Z₁ eG hN₁
    have hPGL : pGammaL2PGLRange K ≤ A :=
      pGammaL2_contains_pgl_of_selfCentralizing_four_all
        hK' A hPSL hA Z hZ hZN
    let L : Subgroup G := (pGammaL2PGLRange K).comap fmap
    haveI : L.Normal := inferInstance
    have hLmap : L.map fmap = pGammaL2PGLRange K := by
      apply le_antisymm
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨g, hg, rfl⟩
        exact hg
      · intro x hx
        have hxA : x ∈ A := hPGL hx
        rcases (MonoidHom.mem_range.mp hxA) with ⟨g, hgx⟩
        refine ⟨g, ?_, ?_⟩
        · change fmap g ∈ pGammaL2PGLRange K
          rwa [hgx]
        · exact hgx
    let eL : L ≃* PGL2 K :=
      (L.equivMapOfInjective fmap hfmap).trans
        ((MulEquiv.subgroupCongr hLmap).trans (pGammaL2PGLRangeEquiv K).symm)
    refine ⟨L, inferInstance, ?_⟩
    refine ⟨K, inferInstance, inferInstance, ?_⟩
    refine ⟨hK', ⟨eL⟩⟩

end CFSG.GorensteinWalter
