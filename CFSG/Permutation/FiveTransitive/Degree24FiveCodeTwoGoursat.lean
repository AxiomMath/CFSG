module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree24FiveAut
public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_sylow_five_card_twenty_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 25) :
    alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let R : Subgroup P :=
    (S : Subgroup H).map H.subtype
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let SN : Subgroup N :=
    R.subgroupOf N
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let κ : N →* MulAut R :=
    R.normalizerMonoidHom
  have hfixedSet :
      sylowFixedPoints X P s S =
        MulAction.fixedPoints S X :=
    sylowFixedPoints_eq_sylow_subgroup_fixedPoints
      X P s S
  have hFcard : Nat.card F = 9 := by
    change Nat.card (sylowFixedPoints X P s S) = 9
    rw [hfixedSet]
    exact
      sylow_five_card_twenty_five_fixedPoints_eq_nine
        X P hcard h5 hnotAlt s hs S hScard
  have hFtype : Fintype.card F = 9 := by
    rw [← Nat.card_eq_fintype_card]
    exact hFcard
  let inclusion : S →* Equiv.Perm X :=
    P.subtype.comp
      (H.subtype.comp
        (S : Subgroup H).subtype)
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let RP : Subgroup (Equiv.Perm X) :=
    inclusion.range
  let eSRP : S ≃* RP :=
    MonoidHom.ofInjective hinclusion
  have hRPcard : Nat.card RP = 25 := by
    calc
      Nat.card RP = Nat.card S :=
        Nat.card_congr eSRP.symm.toEquiv
      _ = 25 := hScard
  obtain ⟨rp, hrpSupport⟩ :
      ∃ rp : RP,
        (rp.1 : Equiv.Perm X).support.card = 15 := by
    rcases
        subgroup_card_twenty_five_support_distribution
          X hcard RP hRPcard with
      hfive | ⟨_, _, hfifteen⟩ |
        ⟨hfixedFour, _⟩
    · obtain ⟨r⟩ :=
        (Nat.card_pos_iff.mp hfive).1
      have hr :
          (r.1.1 : Equiv.Perm X).support.card = 5 :=
        r.prop
      obtain ⟨u, hu⟩ := r.1.prop
      have hmem :
          (r.1 : Equiv.Perm X) ∈ P := by
        rw [← hu]
        exact
          (((S : Subgroup H).subtype u : H) : P).prop
      have hne : (r.1 : Equiv.Perm X) ≠ 1 := by
        intro hrone
        rw [hrone, Equiv.Perm.support_one] at hr
        norm_num at hr
      exact False.elim
        (hnotAlt
          (alternatingGroup_le_of_nontrivial_support_le_seven
            X P hcard h5 hmem hne (by omega)))
    · obtain ⟨r⟩ :=
        (Nat.card_pos_iff.mp (by omega : 0 <
          permutationSubgroupSupportCount RP 15)).1
      exact ⟨r.1, r.prop⟩
    · have hsFixed :
          s ⊆ MulAction.fixedPoints RP X := by
        intro x hx
        rw [MulAction.mem_fixedPoints]
        intro r
        obtain ⟨u, hu⟩ := r.prop
        change (r.1 : Equiv.Perm X) x = x
        rw [← hu]
        have hfix :=
          (mem_fixingSubgroup_iff P).mp
            (((S : Subgroup H).subtype u : H).prop)
            x hx
        change
          (((u : H) : P) : Equiv.Perm X) x = x
        simpa [Subgroup.smul_def,
          Equiv.Perm.smul_def] using hfix
      have hfixedNcard :
          (MulAction.fixedPoints RP X).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact hfixedFour
      have hle :=
        Set.ncard_le_ncard hsFixed
      rw [hs, hfixedNcard] at hle
      omega
  obtain ⟨u, hu⟩ := rp.prop
  let rR : R :=
    ⟨((u : H) : P),
      Subgroup.mem_map_of_mem H.subtype u.prop⟩
  let rPerm : Equiv.Perm X :=
    ((u : H) : P)
  have hrPermEq :
      rPerm = (rp : Equiv.Perm X) := by
    change inclusion u = (rp : Equiv.Perm X)
    exact hu
  have hrSupport :
      rPerm.support.card = 15 := by
    rw [hrPermEq]
    exact hrpSupport
  let eSR : S ≃* R :=
    (S : Subgroup H).equivMapOfInjective
      H.subtype H.subtype_injective
  have hAutRP :
      Nat.card (MulAut RP) = 480 :=
    mulAut_card_eq_four_hundred_eighty_of_subgroup_card_twenty_five
      X hcard RP hRPcard
  have hAutS :
      Nat.card (MulAut S) = 480 := by
    calc
      Nat.card (MulAut S) =
          Nat.card (MulAut RP) :=
        Nat.card_congr (MulAut.congr eSRP).toEquiv
      _ = 480 := hAutRP
  have hAutR :
      Nat.card (MulAut R) = 480 := by
    calc
      Nat.card (MulAut R) =
          Nat.card (MulAut S) :=
        Nat.card_congr (MulAut.congr eSR.symm).toEquiv
      _ = 480 := hAutS
  let J : Subgroup (Equiv.Perm F) :=
    ρ.range
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ :=
      sylowNormalizer_five_transitive_on_fixedPoints
        X P h5 s hs S a b ha hb
    let qJ : J := ⟨ρ q, ⟨q, rfl⟩⟩
    refine ⟨qJ, ?_⟩
    intro i
    exact hq i
  have hAltNested :
      alternatingGroup F ≤
        (MulAction.toPermHom J F).range :=
    Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_nine
      J F hFtype hJ5
  have hNestedLe :
      (MulAction.toPermHom J F).range ≤ J := by
    intro q hq
    obtain ⟨j, hj⟩ := hq
    rw [← hj]
    exact j.prop
  have hAlt :
      alternatingGroup F ≤ ρ.range :=
    hAltNested.trans hNestedLe
  letI : IsSimpleGroup (alternatingGroup F) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card, hFtype]
      norm_num)
  have hAltCard :
      Nat.card (alternatingGroup F) = 181440 := by
    letI : Nontrivial F :=
      Fintype.one_lt_card_iff_nontrivial.mp (by
        rw [hFtype]
        norm_num)
    rw [Nat.card_eq_fintype_card,
      card_alternatingGroup, hFtype]
    norm_num
  have hκrangeLe :
      Nat.card κ.range ≤ 480 := by
    rw [← hAutR]
    exact
      Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_subgroup_dvd_card κ.range)
  have hcentralLift
      (q : Equiv.Perm F)
      (hq : q ∈ alternatingGroup F) :
      ∃ n : N, ρ n = q ∧ κ n = 1 := by
    apply
      FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one
        N (Equiv.Perm F) (MulAut R)
          ρ κ (alternatingGroup F) hAlt
    · rw [hAltCard]
      omega
    · exact hq
  let C : Subgroup N :=
    κ.ker
  let ρC : C →* Equiv.Perm F :=
    ρ.comp C.subtype
  have hAltC :
      alternatingGroup F ≤ ρC.range := by
    intro q hq
    obtain ⟨n, hnFixed, hnCentral⟩ :=
      hcentralLift q hq
    let c : C := ⟨n, hnCentral⟩
    exact ⟨c, hnFixed⟩
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp
      (N.subtype.comp C.subtype)
  have hbaseMapMem :
      ∀ c : C, baseMap c ∈
        Subgroup.centralizer
          ({rPerm} : Set (Equiv.Perm X)) := by
    intro c
    have hcCentral :
        (c.1 : N) ∈
          (Subgroup.centralizer (R : Set P)).subgroupOf N := by
      rw [← R.normalizerMonoidHom_ker]
      exact c.prop
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcCommute :
        Commute ((c.1 : N) : P) (rR : P) :=
      (hcCentral (rR : P) rR.prop).symm
    exact
      congrArg Subtype.val hcCommute
  let centMap :
      C →*
        Subgroup.centralizer
          ({rPerm} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({rPerm} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm rPerm.support :=
    (Degree19.centralizerToSupport rPerm).comp centMap
  let rSupport : Equiv.Perm rPerm.support :=
    rPerm.subtypePerm
      (fun _ => rPerm.apply_mem_support)
  have hsupportMapMem :
      ∀ c : C, supportMap c ∈
        Subgroup.centralizer
          ({rSupport} :
            Set (Equiv.Perm rPerm.support)) := by
    intro c
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change baseMap c (rPerm x.1) =
      rPerm (baseMap c x.1)
    have hcomm : Commute (baseMap c) rPerm :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap c).prop
    exact
      congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
  let supportCentMap :
      C →*
        Subgroup.centralizer
          ({rSupport} :
            Set (Equiv.Perm rPerm.support)) :=
    supportMap.codRestrict
      (Subgroup.centralizer
        ({rSupport} :
          Set (Equiv.Perm rPerm.support)))
      hsupportMapMem
  have hrpow : (rp : RP) ^ 5 = 1 :=
    subgroup_card_twenty_five_pow_five_eq_one
      X hcard RP hRPcard rp
  have hrPermPow : rPerm ^ 5 = 1 := by
    have hrpowPerm :
        ((rp : Equiv.Perm X) ^ 5) = 1 :=
      congrArg Subtype.val hrpow
    rwa [hrPermEq]
  have hrCycleTypeRaw :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one
      hrPermPow
  have hrSum := rPerm.sum_cycleType
  rw [hrCycleTypeRaw, Multiset.sum_replicate,
    nsmul_eq_mul, Nat.cast_id, hrSupport] at hrSum
  have hrCycleCard :
      rPerm.cycleType.card = 3 := by
    omega
  have hrCycleType :
      rPerm.cycleType = {5, 5, 5} := by
    rw [hrCycleTypeRaw, hrCycleCard]
    norm_num
  have hrSupportExtend :
      Equiv.Perm.ofSubtype rSupport = rPerm := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => rPerm.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hrSupportCycleType :
      rSupport.cycleType = rPerm.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hrSupportExtend]
  have hrSupportTypeCard :
      Fintype.card rPerm.support = 15 := by
    calc
      Fintype.card rPerm.support =
          rPerm.support.card :=
        Fintype.card_coe _
      _ = 15 := hrSupport
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({rSupport} :
              Set (Equiv.Perm rPerm.support))) = 750 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hrSupportCycleType, hrCycleType,
      hrSupportTypeCard]
    norm_num
  have hsupportRangeLe :
      Nat.card supportCentMap.range ≤ 750 := by
    rw [← hsupportCentralizerCard]
    exact
      Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_subgroup_dvd_card
          supportCentMap.range)
  have hFsubset :
      (F : Set X) ⊆
        (rPerm.support : Set X)ᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxSupport
    apply Equiv.Perm.mem_support.mp hxSupport
    let rN : N :=
      ⟨rR, R.le_normalizer rR.prop⟩
    let rSN : SN :=
      ⟨rN, rR.prop⟩
    have hfix :=
      MulAction.mem_fixedPoints.mp hx rSN
    change rPerm x = x at hfix
    exact hfix
  have hFncard : (F : Set X).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hFcard
  have hsupportNcard :
      (rPerm.support : Set X).ncard = 15 := by
    rw [Set.ncard_coe_finset, hrSupport]
  have hcomplNcard :
      ((rPerm.support : Set X)ᶜ).ncard = 9 := by
    have htotal :=
      Set.ncard_add_ncard_compl
        (rPerm.support : Set X)
    rw [hsupportNcard,
      Nat.card_eq_fintype_card, hcard] at htotal
    omega
  have hFset :
      (F : Set X) =
        (rPerm.support : Set X)ᶜ := by
    apply Set.eq_of_subset_of_ncard_le hFsubset
    rw [hcomplNcard, hFncard]
  let eF : F ≃ Fin 9 :=
    Fintype.equivFinOfCardEq hFtype
  let q : Equiv.Perm F :=
    eF.symm.permCongr
      (Fin.cycleRange 2 :
        Equiv.Perm (Fin 9))
  have hqSupport : q.support.card = 3 := by
    change
      (eF.symm.permCongr
        (Fin.cycleRange 2 :
          Equiv.Perm (Fin 9))).support.card = 3
    rw [Degree20.card_support_permCongr,
      Fin.isThreeCycle_cycleRange_two.card_support]
  have hqThree : q.IsThreeCycle :=
    card_support_eq_three_iff.mp hqSupport
  have hqAlt : q ∈ alternatingGroup F :=
    hqThree.mem_alternatingGroup
  obtain ⟨c, hcFixed, hcSupport⟩ :=
    FiveTransitive.SimpleGoursat.exists_lift_with_aux_eq_one
      C (Equiv.Perm F)
        (Subgroup.centralizer
          ({rSupport} :
            Set (Equiv.Perm rPerm.support)))
      ρC supportCentMap
        (alternatingGroup F) hAltC (by
          rw [hAltCard]
          omega)
        q hqAlt
  let cN : N := c
  let cP : P := cN
  let cPerm : Equiv.Perm X := cP
  have hcFixSupport :
      ∀ x ∈ rPerm.support,
        cPerm x = x := by
    intro x hx
    have happ :=
      congrFun
        (congrArg DFunLike.coe
          (congrArg Subtype.val hcSupport))
        (⟨x, hx⟩ : rPerm.support)
    exact congrArg Subtype.val happ
  have hcSupportSubset :
      (cPerm.support : Set X) ⊆ F := by
    intro x hx
    rw [hFset]
    rw [Set.mem_compl_iff]
    intro hxR
    exact
      Equiv.Perm.mem_support.mp hx
        (hcFixSupport x hxR)
  have hcInvariantF :
      ∀ x, cPerm x ∈ F ↔ x ∈ F := by
    intro x
    rw [hFset]
    constructor
    · intro hcx hxSupport
      apply hcx
      rw [hcFixSupport x hxSupport]
      exact hxSupport
    · intro hx hcxSupport
      have hfixedImage :=
        hcFixSupport (cPerm x) hcxSupport
      have heq : cPerm x = x :=
        cPerm.injective hfixedImage
      rw [heq] at hcxSupport
      exact hx hcxSupport
  let cF : Equiv.Perm F :=
    cPerm.subtypePerm hcInvariantF
  have hcFq : cF = q := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have happ :=
      congrFun
        (congrArg DFunLike.coe hcFixed) x
    exact congrArg Subtype.val happ
  let valEmbedding : F ↪ X :=
    Function.Embedding.subtype _
  have hsupportMap :
      Finset.map valEmbedding cF.support =
        cPerm.support := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      exact
        Equiv.Perm.mem_support.mp hy
          (Subtype.ext hfix)
    · intro hx
      have hxF : x ∈ F :=
        hcSupportSubset
          (by exact hx)
      let y : F := ⟨x, hxF⟩
      have hy : y ∈ cF.support := by
        apply Equiv.Perm.mem_support.mpr
        intro hfix
        exact
          Equiv.Perm.mem_support.mp hx
            (congrArg Subtype.val hfix)
      exact
        Finset.mem_map.mpr
          ⟨y, hy, rfl⟩
  have hcSupportCard :
      cPerm.support.card = 3 := by
    calc
      cPerm.support.card =
          (Finset.map valEmbedding cF.support).card := by
        rw [hsupportMap]
      _ = cF.support.card :=
        Finset.card_map valEmbedding
      _ = q.support.card := by
        rw [hcFq]
      _ = 3 := hqSupport
  have hcPermNe : cPerm ≠ 1 := by
    intro hcOne
    rw [hcOne, Equiv.Perm.support_one] at hcSupportCard
    norm_num at hcSupportCard
  have hcSupportLe :
      (((cP : P) : Equiv.Perm X).support.card) ≤ 7 := by
    change cPerm.support.card ≤ 7
    omega
  exact
    hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 cP.prop hcPermNe hcSupportLe)

theorem five_point_stabilizer_card_ne_remaining_five_squared_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hCases :
      Nat.card (fixingSubgroup P s) = 97200 ∨
      Nat.card (fixingSubgroup P s) = 194400 ∨
      Nat.card (fixingSubgroup P s) = 14400 ∨
      Nat.card (fixingSubgroup P s) = 2332800 ∨
      Nat.card (fixingSubgroup P s) = 4665600 ∨
      Nat.card (fixingSubgroup P s) = 691200 ∨
      Nat.card (fixingSubgroup P s) = 8294400) :
    False := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let S : Sylow 5 H := Sylow.nonempty.some
  have hScard : Nat.card S = 25 := by
    rcases hCases with hH | hH | hH | hH | hH | hH | hH
    · exact
        sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
          H 3888 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
          H 7776 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
          H 576 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
          H 93312 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
          H 186624 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
          H 27648 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
    · exact
        sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
          H 331776 (by norm_num) (by norm_num)
            (by simpa only [H] using hH) S
  exact
    hnotAlt
      (alternatingGroup_le_of_sylow_five_card_twenty_five
        X P hcard h5 s hs S hScard)

end FiveTransitive.Degree24

end CFSG
