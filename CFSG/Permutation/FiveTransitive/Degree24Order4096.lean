module

public import CFSG.Permutation.FiveTransitive.Degree19FiveNormalizer
public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFixedPoints

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem order_seven_support_eq_twenty_one_of_stabilizer_card_not_dvd_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hnotSeven :
      ¬7 ∣ Nat.card (fixingSubgroup P s))
    (u : P) (huorder : orderOf u = 7) :
    (u : Equiv.Perm X).support.card = 21 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 7 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 24 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 24 := hcard
  have hnotSupportLe : ¬g.support.card ≤ 14 := by
    intro hsupport
    have hfixedCard :
        5 ≤ Fintype.card (Function.fixedPoints g) := by
      rw [Equiv.Perm.card_fixedPoints,
        Equiv.Perm.sum_cycleType, hcard]
      omega
    let e : Fin 5 ↪ Function.fixedPoints g :=
      Classical.choice
        (Function.Embedding.nonempty_of_card_le
          hfixedCard)
    let eX : Fin 5 ↪ X :=
      e.trans (Function.Embedding.subtype _)
    let t : Set X := Set.range eX
    have ht : t.ncard = 5 := by
      rw [Set.ncard_range_of_injective eX.injective,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    let uT : fixingSubgroup P t :=
      ⟨u, by
        rw [mem_fixingSubgroup_iff]
        rintro _ ⟨i, rfl⟩
        exact (e i).2⟩
    have huTorder : orderOf uT = 7 := by
      calc
        orderOf uT = orderOf (uT : P) :=
          (Subgroup.orderOf_coe _).symm
        _ = orderOf u := rfl
        _ = 7 := huorder
    have hsevenT :
        7 ∣ Nat.card (fixingSubgroup P t) := by
      rw [← huTorder, Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    have hequal :
        Nat.card (fixingSubgroup P s) =
          Nat.card (fixingSubgroup P t) :=
      five_point_stabilizers_have_equal_card
        X P h5 s t hs ht
    apply hnotSeven
    rw [hequal]
    exact hsevenT
  have hsupportEq :
      (k + 1) * 7 = g.support.card :=
    hsum
  have hkThree : k + 1 = 3 := by
    omega
  rw [← hsupportEq, hkThree]

private theorem sylow_seven_centralizer_card_dvd_forty_two_of_support_twenty_one
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 20891566080)
    (s : Set X) (hs : s.ncard = 5)
    (hnotSeven :
      ¬7 ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow 7 P) (hScard : Nat.card S = 7) :
    Nat.card
        (Subgroup.centralizer (S : Set P)) ∣ 42 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = 7 :=
    huRaw.trans hScard
  let uP : P := u
  let g : Equiv.Perm X := uP
  have huPorder : orderOf uP = 7 := by
    calc
      orderOf uP = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 7 := huorder
  have hgsupport : g.support.card = 21 := by
    simpa only [g, uP] using
      order_seven_support_eq_twenty_one_of_stabilizer_card_not_dvd_seven
        X P hcard h5 s hs hnotSeven uP huPorder
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf uP :=
        Subgroup.orderOf_coe _
      _ = 7 := huPorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, hgsupport] at hsum
  have hkThree : k + 1 = 3 := by omega
  have hcycleType :
      g.cycleType = {7, 7, 7} := by
    rw [hk, hgorder, hkThree]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapInjective :
      Function.Injective baseMap := by
    intro a b hab
    exact C.subtype_injective
      (P.subtype_injective hab)
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((q.prop (u : P) u.prop).symm)
  let centMap :
      C →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm g.support :=
    (Degree19.centralizerToSupport g).comp centMap
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hsupportMapMem :
      ∀ q : C, supportMap q ∈
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change baseMap q (g x.1) =
      g (baseMap q x.1)
    have hcomm : Commute (baseMap q) g :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap q).prop
    exact
      congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
  let supportCentMap :
      C →*
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) :=
    supportMap.codRestrict
      (Subgroup.centralizer
        ({gSupport} :
          Set (Equiv.Perm g.support)))
      hsupportMapMem
  have hsupportCentMapInjective :
      Function.Injective supportCentMap := by
    intro a b hab
    by_contra habNe
    let w : C := a * b⁻¹
    have hwNe : w ≠ 1 := by
      intro hw
      exact habNe (mul_inv_eq_one.mp hw)
    have hwSupportCentOne :
        supportCentMap w = 1 := by
      dsimp only [w]
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel _
    have hwSupportOne :
        supportMap w = 1 :=
      congrArg Subtype.val hwSupportCentOne
    let wP : P := w
    let wPerm : Equiv.Perm X := wP
    have hwFixSupport :
        ∀ x ∈ g.support, wPerm x = x := by
      intro x hx
      have happly :=
        congrFun
          (congrArg DFunLike.coe hwSupportOne)
          (⟨x, hx⟩ : g.support)
      exact congrArg Subtype.val happly
    have hwSupportSubset :
        wPerm.support ⊆ g.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxg
      exact
        Equiv.Perm.mem_support.mp hx
          (hwFixSupport x hxg)
    have hwSupportCard :
        wPerm.support.card ≤ 3 := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ = 3 := by
          rw [Finset.card_compl, hcard, hgsupport]
    have hwPermNe : wPerm ≠ 1 := by
      intro hwOne
      apply hwNe
      apply hbaseMapInjective
      rw [map_one]
      exact hwOne
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 wP.prop hwPermNe (by
          change wPerm.support.card ≤ 7
          omega))
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportTypeCard :
      Fintype.card g.support = 21 := by
    rw [Fintype.card_coe, hgsupport]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = 2058 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hcycleType,
      hsupportTypeCard]
    norm_num
  have hCdvdSupport : Nat.card C ∣ 2058 := by
    rw [← hsupportCentralizerCard]
    exact Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective
  have hCdvdP :
      Nat.card C ∣ 20891566080 := by
    rw [← hPcard]
    exact Subgroup.card_subgroup_dvd_card C
  have hCdvdGcd :
      Nat.card C ∣
        Nat.gcd 2058 20891566080 :=
    Nat.dvd_gcd hCdvdSupport hCdvdP
  have hgcd :
      Nat.gcd 2058 20891566080 = 42 := by
    norm_num
  rw [hgcd] at hCdvdGcd
  simpa only [C] using hCdvdGcd

private theorem divisor_six_cases_for_order4096
    {n : ℕ} (hn : n ∣ 6) (hnPos : 0 < n) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
  have hnLe : n ≤ 6 :=
    Nat.le_of_dvd (by norm_num) hn
  interval_cases n
  all_goals norm_num at hn
  all_goals omega

theorem five_point_stabilizer_card_ne_four_thousand_ninety_six
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 4096 := by
  classical
  intro hHcard
  let H : Subgroup P := fixingSubgroup P s
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 20891566080 := by
    rw [hHindex,
      show Nat.card H = 4096 by
        simpa only [H] using hHcard] at hHindexCard
    omega
  have hnotSeven :
      ¬7 ∣ Nat.card (fixingSubgroup P s) := by
    rw [hHcard]
    norm_num
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Sylow 7 P := Sylow.nonempty.some
  have hScard : Nat.card S = 7 := by
    rw [S.card_eq_multiplicity, hPcard,
      show 20891566080 =
        7 * 2984509440 by norm_num,
      Nat.factorization_mul (by norm_num)
        (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 7 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd
        (by norm_num)]
    norm_num
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  have hSleC : (S : Subgroup P) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm'
        (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hCcardDvd : Nat.card C ∣ 42 := by
    simpa only [C] using
      sylow_seven_centralizer_card_dvd_forty_two_of_support_twenty_one
        X P hcard h5 hnotAlt hPcard
          s hs hnotSeven S hScard
  have hSsubCard :
      Nat.card ((S : Subgroup P).subgroupOf C) = 7 := by
    calc
      Nat.card ((S : Subgroup P).subgroupOf C) =
          Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv
      _ = 7 := hScard
  have hcCardRaw :=
    ((S : Subgroup P).subgroupOf C).index_mul_card
  have hcCard : c * 7 = Nat.card C := by
    dsimp only [c]
    change
      ((S : Subgroup P).subgroupOf C).index * 7 =
        Nat.card C
    calc
      ((S : Subgroup P).subgroupOf C).index * 7 =
          ((S : Subgroup P).subgroupOf C).index *
            Nat.card ((S : Subgroup P).subgroupOf C) :=
        congrArg
          (((S : Subgroup P).subgroupOf C).index * ·)
          hSsubCard.symm
      _ = Nat.card C := hcCardRaw
  have hcDvd : c ∣ 6 := by
    obtain ⟨t, ht⟩ := hCcardDvd
    refine ⟨t, ?_⟩
    have hcancel : 7 * 6 = 7 * (c * t) := by
      calc
        7 * 6 = 42 := by norm_num
        _ = Nat.card C * t := ht
        _ = (c * 7) * t := by rw [hcCard]
        _ = 7 * (c * t) := by ring
    omega
  have hAutCard : Nat.card (MulAut S) = 6 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 6 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer
          (S : Set P)).relIndex
          (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd : r ∣ 6 := by
    change C.relIndex N ∣ 6
    rwa [hrEq]
  letI : (S : Subgroup P).IsFiniteRelIndex C :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcPos : 0 < c :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrPos : 0 < r :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hNmod : N.index % 7 = 1 := by
    change
      (Subgroup.normalizer (S : Set P)).index % 7 = 1
    have hsylow :
        (Subgroup.normalizer (S : Set P)).index ≡
          1 [MOD 7] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 7 P
    change
      (Subgroup.normalizer (S : Set P)).index % 7 =
        1 % 7 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrel :
      C.relIndex N * N.index = C.index := by
    simpa only [C, N] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer
          (S : Set P))
  have hCindexCard := C.index_mul_card
  have hproduct :
      c * r * N.index * 7 = Nat.card P := by
    calc
      c * r * N.index * 7 =
          (r * N.index) * (c * 7) := by ring
      _ = C.index * Nat.card C := by
        rw [hrel, hcCard]
      _ = Nat.card P := hCindexCard
  have hcCases :
      c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 6 :=
    divisor_six_cases_for_order4096 hcDvd hcPos
  have hrCases :
      r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 6 :=
    divisor_six_cases_for_order4096 hrDvd hrPos
  have hcr : c * r = 3 := by
    rcases hcCases with hc | hc | hc | hc
    all_goals
      rcases hrCases with hr | hr | hr | hr
    all_goals rw [hc, hr, hPcard] at hproduct
    all_goals rw [hc, hr]
    all_goals norm_num at hproduct hNmod ⊢
    all_goals omega
  have hP3 :
      MulAction.IsMultiplyPretransitive P X 3 := by
    letI :
        MulAction.IsMultiplyPretransitive P X 5 :=
      hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hfixed
      (a : Degree15.NonidentitySylowElements 7 P) :
      Fintype.card
          (MulAction.fixedBy X
            (Degree15.nonidentitySylowElementVal 7 P a)) =
        3 := by
    rcases a with ⟨T, ⟨v, hvNe⟩⟩
    have hTcard : Nat.card T = 7 :=
      Degree15.sylow_card_eq_of_card_eq
        S hScard T
    have hvOrderT : orderOf v = 7 :=
      Degree15.orderOf_eq_prime_of_card_eq_prime
        hTcard hvNe
    let vP : P := v
    have hvOrderP : orderOf vP = 7 := by
      calc
        orderOf vP = orderOf v :=
          Subgroup.orderOf_coe _
        _ = 7 := hvOrderT
    have hvSupport :
        (vP : Equiv.Perm X).support.card = 21 :=
      order_seven_support_eq_twenty_one_of_stabilizer_card_not_dvd_seven
        X P hcard h5 s hs hnotSeven
          vP hvOrderP
    change
      Fintype.card
        (MulAction.fixedBy X vP) = 3
    rw [Degree15.card_fixedBy_subgroup_perm,
      hcard, hvSupport]
  have hbound :=
    Degree19.nonidentity_sylow_fixed_embedding_bound
      X P (p := 7) (m := 3) (f := 3)
        (by norm_num) S hScard
        (by rw [hcard]; norm_num)
        hfixed hP3
  have hNindexPos : 0 < N.index :=
    Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite
  have hNproduct :
      N.index * 21 = 20891566080 := by
    calc
      N.index * 21 =
          c * r * N.index * 7 := by
        rw [hcr]
        ring
      _ = Nat.card P := hproduct
      _ = 20891566080 := hPcard
  norm_num [Nat.descFactorial] at hbound
  have hbound' :
      N.index * 36 ≤ 20891566080 := by
    rw [← hPcard, Nat.card_eq_fintype_card]
    change
      N.index * 6 * 6 ≤
        Fintype.card P at hbound
    omega
  omega

end FiveTransitive.Degree24

end CFSG
