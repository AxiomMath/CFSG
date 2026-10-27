module

public import CFSG.OddTranspositions.PartThree.EightOne.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Central
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Width

public section

namespace CFSG.OddTranspositions.PartThree.EightOne

open CFSG.Timmesfeld.Bridge.Asc72

theorem odd_card_oddCore {X : Type} [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : CFSG.oddCore X = CFSG.pPrimeCore 2 X :=
    (CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm
  rw [h]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem not_mem_of_isBenderGroup {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    {R : Subgroup G} [R.Normal] (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ R)) {d : G}
    (hd : d ∈ D) : d ∉ R := by
  rintro hdR
  rcases hS.subset_or_disjoint R with hsub | hdisj
  · have htop : R = ⊤ := hS.eq_top_of_subset R hsub
    haveI hsimple : IsSimpleGroup (G ⧸ R) :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB
    haveI : Subsingleton (G ⧸ R) := QuotientGroup.subsingleton_iff.mpr htop
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (G ⧸ R)).exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  · exact hdisj d hd hdR

theorem setup_quotient_of_le_solvableRadical {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D) (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ CFSG.solvableRadical G))
    {Q : Subgroup G} [Q.Normal] (hQ : Q ≤ CFSG.solvableRadical G) :
    Setup (G ⧸ Q) (QuotientGroup.mk' Q '' D) := by
  refine hS.map (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q) ?_
  intro d hd h1
  rw [QuotientGroup.mk'_apply] at h1
  exact not_mem_of_isBenderGroup hS hB hd (hQ ((QuotientGroup.eq_one_iff d).mp h1))

theorem map_solvableRadical_eq {G : Type} [Group G] [Finite G] {Q : Subgroup G} [Q.Normal]
    (hQ : Q ≤ CFSG.solvableRadical G) :
    (CFSG.solvableRadical G).map (QuotientGroup.mk' Q) = CFSG.solvableRadical (G ⧸ Q) := by
  haveI hRs : Group.IsSolvable ↥(CFSG.solvableRadical G) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hQs : Group.IsSolvable ↥Q :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hQ)
      (Subgroup.inclusion_injective hQ)
  have hk : Group.IsSolvable (QuotientGroup.mk' Q).ker := by
    rw [QuotientGroup.ker_mk']
    exact hQs
  exact CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical
    (QuotientGroup.mk'_surjective Q) hk

theorem nonempty_mulEquiv_quotient_solvableRadical {G : Type} [Group G] [Finite G]
    {Q : Subgroup G} [Q.Normal] (hQ : Q ≤ CFSG.solvableRadical G) :
    Nonempty ((G ⧸ Q) ⧸ CFSG.solvableRadical (G ⧸ Q) ≃* G ⧸ CFSG.solvableRadical G) := by
  haveI hRs : Group.IsSolvable ↥(CFSG.solvableRadical G) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hQs : Group.IsSolvable ↥Q :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hQ)
      (Subgroup.inclusion_injective hQ)
  have hk : Group.IsSolvable (QuotientGroup.mk' Q).ker := by
    rw [QuotientGroup.ker_mk']
    exact hQs
  exact ⟨(CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.solQuotEquiv
    (ρ := QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q) hk).symm⟩

theorem oddCore_le_of_isBenderGroup {G : Type} [Group G] [Finite G] {R : Subgroup G} [R.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ R)) : CFSG.oddCore G ≤ R := by
  haveI hsimple : IsSimpleGroup (G ⧸ R) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB
  set K : Subgroup (G ⧸ R) := (CFSG.oddCore G).map (QuotientGroup.mk' R) with hK
  haveI hKn : K.Normal :=
    (CFSG.oddCore_normal (G := G)).map (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)
  have hKodd : Odd (Nat.card K) := by
    refine (odd_card_oddCore (X := G)).of_dvd_nat ?_
    rw [hK]
    exact Subgroup.card_map_dvd (CFSG.oddCore G) (QuotientGroup.mk' R)
  have hNotOdd : ¬ Odd (Nat.card (G ⧸ R)) := by
    obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := G ⧸ R)
    have h4 : 4 ≤ Nat.card (Subgroup.center (P : Subgroup (G ⧸ R))) :=
      CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.four_le_card_center hB P
    have hP4 : 4 ≤ Nat.card (P : Subgroup (G ⧸ R)) :=
      h4.trans (Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_subgroup_dvd_card (Subgroup.center (P : Subgroup (G ⧸ R)))))
    have hPne : Nat.card (P : Subgroup (G ⧸ R)) ≠ 1 := by omega
    have h2P : 2 ∣ Nat.card (P : Subgroup (G ⧸ R)) := by
      rcases (Sylow.isPGroup' P).card_eq_or_dvd with h | h
      · exact absurd h hPne
      · exact h
    intro hodd
    exact hodd.not_two_dvd_nat
      (h2P.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup (G ⧸ R))))
  rcases hsimple.eq_bot_or_eq_top_of_normal K with hbot | htop
  · have hbot' : (CFSG.oddCore G).map (QuotientGroup.mk' R) = ⊥ := hK ▸ hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot'
    exact hbot'
  · rw [htop, Subgroup.card_top] at hKodd
    exact (hNotOdd hKodd).elim

theorem isPGroup_two_of_le_center {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hEc : E ≤ Subgroup.center X) (hO : CFSG.oddCore X = ⊥) : IsPGroup 2 E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro e
  have hdvd : orderOf (e : X) ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E e.2
  have hne : orderOf (e : X) ≠ 0 := by
    have hpos : 0 < Nat.card E := Nat.card_pos
    rintro h0
    rw [h0, Nat.zero_dvd] at hdvd
    exact hpos.ne' hdvd
  obtain ⟨k, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd hne
  set f : X := (e : X) ^ 2 ^ k with hf
  have hford : orderOf f = m := by
    rw [hf, orderOf_pow_of_dvd (n := 2 ^ k) (pow_pos (by norm_num) k).ne']
    · rw [hcard, Nat.mul_div_cancel_left m (pow_pos (by norm_num) k)]
    · rw [hcard]
      exact dvd_mul_right _ _
  have hfcenter : f ∈ Subgroup.center X := by
    rw [hf]
    exact (Subgroup.center X).pow_mem (hEc e.2) _
  have hnormal : (Subgroup.zpowers f).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hfcenter)
  have hodd : Odd (Nat.card (Subgroup.zpowers f)) := by
    rw [Nat.card_zpowers, hford]
    exact hm
  have hle : Subgroup.zpowers f ≤ CFSG.oddCore X := le_sSup ⟨hnormal, hodd⟩
  have hf1 : f = 1 := by
    have hmem : f ∈ CFSG.oddCore X := hle (Subgroup.mem_zpowers f)
    rw [hO] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hm1 : m = 1 := by
    rw [← hford, hf1, orderOf_one]
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_coe, hcard, hm1, mul_one]

theorem nonempty_mulEquiv_quotient_twoOddCore (G : Type) [Group G] [Finite G] :
    Nonempty (G ⧸ twoOddCore G ≃*
      (G ⧸ CFSG.pCore 2 G) ⧸ CFSG.oddCore (G ⧸ CFSG.pCore 2 G)) := by
  have hNO : CFSG.pCore 2 G ≤
      (CFSG.oddCore (G ⧸ CFSG.pCore 2 G)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 G)) := by
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hmap : ((CFSG.oddCore (G ⧸ CFSG.pCore 2 G)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 G))).map (QuotientGroup.mk' (CFSG.pCore 2 G)) =
      CFSG.oddCore (G ⧸ CFSG.pCore 2 G) :=
    Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 G)) _
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hmap).symm.trans
    (QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 G)
      ((CFSG.oddCore (G ⧸ CFSG.pCore 2 G)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 G))) hNO)).symm⟩

end CFSG.OddTranspositions.PartThree.EightOne
