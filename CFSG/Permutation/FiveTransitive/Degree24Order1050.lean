module

public import CFSG.Permutation.FiveTransitive.Degree24Order567
public import CFSG.Permutation.FiveTransitive.OrderSevenSupportPower
public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private abbrev SylowSevenCountOneThousandFifty :=
  ↥(Nat.divisors 150)

private def sylowSevenCountOneThousandFiftyPredicate
    (n : SylowSevenCountOneThousandFifty) : Prop :=
  n.1 % 7 = 1 →
    n.1 = 1 ∨ n.1 = 15 ∨ n.1 = 50

private theorem sylowSevenCountOneThousandFifty_cases :
    ∀ n : SylowSevenCountOneThousandFifty,
      sylowSevenCountOneThousandFiftyPredicate n := by
  letI (n : SylowSevenCountOneThousandFifty) :
      Decidable
        (sylowSevenCountOneThousandFiftyPredicate n) := by
    dsimp only [sylowSevenCountOneThousandFiftyPredicate]
    infer_instance
  letI : Decidable
      (∀ n : SylowSevenCountOneThousandFifty,
        sylowSevenCountOneThousandFiftyPredicate n) :=
    Fintype.decidableForallFintype
  decide

theorem degree24_global_support_fourteen_card_of_local_sylow_count
    {a n : ℕ}
    (h : 5100480 * (n * 6) = a * 30240) :
    a = 1012 * n := by
  omega

theorem five_point_stabilizer_card_ne_one_thousand_fifty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 1050 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  intro hHcard
  have hP5 :
      MulAction.IsMultiplyPretransitive P X 5 := by
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
  have hPcard :
      Nat.card P = 5100480 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hPcardExact :
      Nat.card P = 5355504000 := by
    rw [hPcard, hHcard]
  let S : Sylow 7 H := Sylow.nonempty.some
  have hScard : Nat.card S = 7 :=
    sylow_card_eq_prime_of_card_eq_prime_mul
      H 7 150 (by norm_num) (by norm_num)
        (by simpa using hHcard) S
  have hSindex : S.index = 150 := by
    have hproduct := S.index_mul_card
    rw [hScard, hHcard] at hproduct
    omega
  let n := Nat.card (Sylow 7 H)
  have hnDvd : n ∣ 150 := by
    have hdiv := S.card_dvd_index
    change n ∣ S.index at hdiv
    simpa [hSindex] using hdiv
  have hnMod : n % 7 = 1 := by
    have hmod := card_sylow_modEq_one 7 H
    change n % 7 = 1 % 7 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  have hnMem : n ∈ Nat.divisors 150 :=
    Nat.mem_divisors.mpr ⟨hnDvd, by norm_num⟩
  have hnCases : n = 1 ∨ n = 15 ∨ n = 50 := by
    exact
      sylowSevenCountOneThousandFifty_cases
        ⟨n, hnMem⟩ hnMod
  have hAllCard :
      Nat.card {u : H // orderOf u = 7} =
        n * 6 := by
    have hcount :=
      card_order_prime_elements_of_sylow_card_prime
        H 7 S hScard
    change
      Nat.card {u : H // orderOf u = 7} =
        n * (7 - 1) at hcount
    norm_num at hcount
    simpa only [Nat.card_eq_fintype_card] using hcount
  have hSupport
      (u : fixingSubgroup P s)
      (hu : orderOf u = 7) :
      ((((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card = 14) :=
    order_seven_mem_five_stabilizer_support_eq_fourteen
      X P hcard h5 hnotAlt s hs u hu
  let localEquiv :
      {u : H // orderOf u = 7} ≃
        LocalOrderPrimeSupportElements X P s 7 14 := {
    toFun := fun u =>
      ⟨u.1, ⟨u.2, hSupport u.1 u.2⟩⟩
    invFun := fun u => ⟨u.1, u.2.1⟩
    left_inv := by
      intro u
      apply Subtype.ext
      rfl
    right_inv := by
      intro u
      apply Subtype.ext
      rfl }
  have hLocalCard :
      Nat.card
          (LocalOrderPrimeSupportElements
            X P s 7 14) =
        n * 6 := by
    rw [← Nat.card_congr localEquiv, hAllCard]
  letI : Fintype s := Fintype.ofFinite s
  have hsCard : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hs]
  let es : s ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hsCard
  let e₀ : Fin 5 ↪ X := {
    toFun := fun i => (es.symm i).1
    inj' := by
      intro i j hij
      apply es.symm.injective
      exact Subtype.ext hij }
  have he₀Range : Set.range e₀ = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        es.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hLocal :
      Nat.card
          (LocalOrderPrimeSupportElements
            X P s 7 14) =
        Nat.card
          (OrderPrimeSupportFixesEmbedding
            X P 7 14 e₀) :=
    Nat.card_congr
      (localOrderPrimeSupportEquiv
        X P s 7 14 e₀ he₀Range)
  have hfixed
      (u : OrderPrimeSupportElements X P 7 14) :
      Nat.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
        30240 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
          (Fintype.card
            (MulAction.fixedBy X u.1)).descFactorial
              (Fintype.card (Fin 5)) :=
        Degree15.card_fixedBy_embedding
          (G := P) (X := X) (I := Fin 5) u.1
      _ = 30240 := by
        rw [Degree15.card_fixedBy_subgroup_perm,
          hcard, u.2.2, Fintype.card_fin]
        norm_num [Nat.descFactorial]
  have hEcard : Nat.card (Fin 5 ↪ X) = 5100480 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_embedding_eq,
      Fintype.card_fin, hcard]
    norm_num [Nat.descFactorial]
  have hcount :=
    orderPrimeSupport_incidence_count
      X P hP5 7 14 30240 hfixed e₀
  rw [hEcard, ← hLocal, hLocalCard] at hcount
  have hGlobalCard :
      Nat.card
          (OrderPrimeSupportElements X P 7 14) =
        1012 * n :=
    degree24_global_support_fourteen_card_of_local_sylow_count
      hcount
  obtain ⟨u₀, hu₀order⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := H) 7 (by
        rw [hHcard]
        norm_num)
  have hGlobalNonempty :
      Nonempty
        (OrderPrimeSupportElements X P 7 14) := by
    refine ⟨⟨(u₀ : H), ?_, ?_⟩⟩
    · calc
        orderOf ((u₀ : H) : P) =
            orderOf u₀ :=
          Subgroup.orderOf_coe _
        _ = 7 := hu₀order
    · exact hSupport u₀ hu₀order
  have hThreeDvd :
      3 ∣ Nat.card
          (OrderPrimeSupportElements X P 7 14) :=
    three_dvd_card_orderSevenSupportElements
      X P 14 hGlobalNonempty
  have hnFifteen : n = 15 := by
    rcases hnCases with hnOne | hnFifteen | hnFifty
    · rw [hGlobalCard, hnOne] at hThreeDvd
      norm_num at hThreeDvd
    · exact hnFifteen
    · rw [hGlobalCard, hnFifty] at hThreeDvd
      norm_num at hThreeDvd
  let N : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  have hNindex : N.index = 15 := by
    calc
      N.index = Nat.card (Sylow 7 H) := by
        exact S.card_eq_index_normalizer.symm
      _ = n := rfl
      _ = 15 := hnFifteen
  have hNcard : Nat.card N = 70 := by
    have hproduct := N.index_mul_card
    rw [hNindex, hHcard] at hproduct
    omega
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  let C : Subgroup H :=
    Subgroup.centralizer (S : Set H)
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
      (Subgroup.centralizer (S : Set H)).relIndex
          (Subgroup.normalizer (S : Set H)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd : C.relIndex N ∣ 6 := by
    rwa [hrEq]
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrPos : 0 < C.relIndex N :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrel :
      C.relIndex N * N.index = C.index :=
    Subgroup.relIndex_mul_index
      (Subgroup.centralizer_le_normalizer (S : Set H))
  have hNcardEq :
      Nat.card N = C.relIndex N * Nat.card C := by
    have hproduct :
        N.index * (C.relIndex N * Nat.card C) =
          N.index * Nat.card N := by
      calc
        N.index * (C.relIndex N * Nat.card C) =
            C.index * Nat.card C := by
          rw [← hrel]
          ac_rfl
        _ = Nat.card H := C.index_mul_card
        _ = N.index * Nat.card N :=
          N.index_mul_card.symm
    exact
      (Nat.mul_left_cancel
        (Nat.pos_of_ne_zero
          Subgroup.index_ne_zero_of_finite)
        hproduct).symm
  have hFiveDvdC : 5 ∣ Nat.card C := by
    have hrLe : C.relIndex N ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hrDvd
    rw [hNcard] at hNcardEq
    have hrOneOrTwo :
        C.relIndex N = 1 ∨ C.relIndex N = 2 := by
      interval_cases C.relIndex N
      all_goals try norm_num at hrDvd
      all_goals omega
    rcases hrOneOrTwo with hrOne | hrTwo
    · have hCcard : Nat.card C = 70 := by
        rw [hrOne] at hNcardEq
        omega
      rw [hCcard]
      norm_num
    · have hCcard : Nat.card C = 35 := by
        rw [hrTwo] at hNcardEq
        omega
      rw [hCcard]
      norm_num
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨v, hvOrder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := C) 5 hFiveDvdC
  obtain ⟨u, huOrderRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huOrderS : orderOf u = 7 :=
    huOrderRaw.trans hScard
  let uH : H := u
  let uP : P := uH
  let g : Equiv.Perm X := uP
  have huOrderH : orderOf uH = 7 := by
    calc
      orderOf uH = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 7 := huOrderS
  have hgOrder : orderOf g = 7 := by
    calc
      orderOf g = orderOf uP :=
        Subgroup.orderOf_coe _
      _ = orderOf uH :=
        Subgroup.orderOf_coe _
      _ = 7 := huOrderH
  have hgSupport : g.support.card = 14 :=
    hSupport uH huOrderH
  let vH : H := v
  let vP : P := vH
  let vPerm : Equiv.Perm X := vP
  have hvPermOrder : orderOf vPerm = 5 := by
    calc
      orderOf vPerm = orderOf vP :=
        Subgroup.orderOf_coe _
      _ = orderOf vH :=
        Subgroup.orderOf_coe _
      _ = orderOf v :=
        Subgroup.orderOf_coe _
      _ = 5 := hvOrder
  have hvCommuteH : Commute vH uH := by
    exact (v.prop uH u.prop).symm
  have hvCommutePerm : Commute vPerm g := by
    exact
      congrArg Subtype.val
        (congrArg Subtype.val hvCommuteH)
  let vCent :
      Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)) :=
    ⟨vPerm, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hvCommutePerm⟩
  let vSupport : Equiv.Perm g.support :=
    Degree19.centralizerToSupport g vCent
  have hvCentOrder : orderOf vCent = 5 := by
    calc
      orderOf vCent = orderOf vPerm :=
        (Subgroup.orderOf_coe _).symm
      _ = 5 := hvPermOrder
  have hvSupportOrderDvdFive :
      orderOf vSupport ∣ 5 := by
    exact
      (orderOf_map_dvd
        (Degree19.centralizerToSupport g)
        vCent).trans (by rw [hvCentOrder])
  have hgPrime : (orderOf g).Prime := by
    rw [hgOrder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgPrime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder, hgSupport] at hsum
  have hkTwo : k + 1 = 2 := by omega
  have hgCycleType : g.cycleType = {7, 7} := by
    rw [hk, hgOrder, hkTwo]
    norm_num
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = 98 := by
    have hsupportSubtypeCard :
        Fintype.card g.support = 14 := by
      calc
        Fintype.card g.support = g.support.card :=
          Fintype.card_coe _
        _ = 14 := hgSupport
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hgCycleType,
      hsupportSubtypeCard]
    norm_num
  have hvSupportCommute :
      Commute vSupport gSupport := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change vPerm (g x.1) = g (vPerm x.1)
    exact congrFun
      (congrArg DFunLike.coe hvCommutePerm.eq) x.1
  let w :
      Subgroup.centralizer
        ({gSupport} :
          Set (Equiv.Perm g.support)) :=
    ⟨vSupport, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hvSupportCommute⟩
  have hvSupportOrderDvdNinetyEight :
      orderOf vSupport ∣ 98 := by
    have hwDvd : orderOf w ∣ Nat.card
        (Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support))) :=
      orderOf_dvd_natCard w
    have hwOrder :
        orderOf w = orderOf vSupport :=
      (Subgroup.orderOf_coe _).symm
    rw [hwOrder, hsupportCentralizerCard] at hwDvd
    exact hwDvd
  have hvSupportOne : vSupport = 1 := by
    have hGcd :=
      Nat.dvd_gcd hvSupportOrderDvdFive
        hvSupportOrderDvdNinetyEight
    norm_num at hGcd
    exact hGcd
  have hvFixSupport :
      ∀ x ∈ g.support, vPerm x = x := by
    intro x hx
    let y : g.support := ⟨x, hx⟩
    have happ :=
      congrArg
        (fun q : Equiv.Perm g.support => (q y).1)
        hvSupportOne
    exact happ
  have hvFixS :
      ∀ x ∈ s, vPerm x = x := by
    exact (mem_fixingSubgroup_iff P).mp vH.prop
  have hSupportDisjoint :
      Disjoint (g.support : Set X) s := by
    rw [Set.disjoint_left]
    intro x hxg hxs
    exact
      Equiv.Perm.mem_support.mp hxg
        ((mem_fixingSubgroup_iff P).mp uH.prop x hxs)
  let U : Set X := (g.support : Set X) ∪ s
  have hUncard : U.ncard = 19 := by
    change ((g.support : Set X) ∪ s).ncard = 19
    rw [Set.ncard_union_eq hSupportDisjoint,
      Set.ncard_coe_finset, hgSupport, hs]
  have hUcomplCard : Uᶜ.ncard = 5 := by
    have htotal := Set.ncard_add_ncard_compl U
    rw [Nat.card_eq_fintype_card, hcard,
      hUncard] at htotal
    omega
  have hvSupportSubset :
      (vPerm.support : Set X) ⊆ Uᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxU
    apply Equiv.Perm.mem_support.mp hx
    rcases hxU with hxg | hxs
    · exact hvFixSupport x hxg
    · exact hvFixS x hxs
  have hvSupportCard :
      vPerm.support.card ≤ 5 := by
    rw [← Set.ncard_coe_finset]
    exact
      (Set.ncard_le_ncard hvSupportSubset).trans_eq
        hUcomplCard
  have hvPermNe : vPerm ≠ 1 := by
    intro hvOne
    rw [hvOne, orderOf_one] at hvPermOrder
    norm_num at hvPermOrder
  exact hnotAlt
    (alternatingGroup_le_of_nontrivial_support_le_seven
      X P hcard h5 vP.prop hvPermNe (by
        change vPerm.support.card ≤ 7
        omega))

end FiveTransitive.Degree24

end CFSG
