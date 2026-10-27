module

public import CFSG.Permutation.FiveTransitive.Degree24PrimeSupportIncidence
public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem support_card_eq_of_nonidentity_mem_sylow_card_prime
    (G X : Type) [Group G] [Fintype G]
    [Fintype X] [DecidableEq X]
    (ρ : G →* Equiv.Perm X)
    {p : ℕ} [Fact p.Prime]
    (S₀ : Sylow p G) (hS₀card : Nat.card S₀ = p)
    (S T : Sylow p G)
    (u : S) (huNe : u ≠ 1)
    (v : T) (hvNe : v ≠ 1) :
    (ρ (u : G)).support.card =
      (ρ (v : G)).support.card := by
  classical
  have hScard : Nat.card S = p :=
    Degree15.sylow_card_eq_of_card_eq
      S₀ hS₀card S
  have hTcard : Nat.card T = p :=
    Degree15.sylow_card_eq_of_card_eq
      S₀ hS₀card T
  obtain ⟨q, hq⟩ := exists_smul_eq G S T
  let uqG : G := MulAut.conj q (u : G)
  have huqT : uqG ∈ (T : Subgroup G) := by
    rw [← hq]
    exact ⟨(u : G), u.prop, rfl⟩
  let uq : T := ⟨uqG, huqT⟩
  have huqNe : uq ≠ 1 := by
    intro huqOne
    apply huNe
    apply Subtype.ext
    have huqOneG : uqG = 1 :=
      congrArg Subtype.val huqOne
    change q * (u : G) * q⁻¹ = 1 at huqOneG
    have := congrArg (fun z : G => q⁻¹ * z * q) huqOneG
    simpa [mul_assoc] using this
  have hsupportWithin :
      (ρ (uq : G)).support =
        (ρ (v : G)).support := by
    apply le_antisymm
    · have huqGen :
          uq ∈ Subgroup.zpowers v :=
        mem_zpowers_of_prime_card
          hTcard hvNe
      obtain ⟨z, hz⟩ :=
        Subgroup.mem_zpowers_iff.mp huqGen
      have hzρ :
          ρ (uq : G) =
            (ρ (v : G)) ^ z := by
        rw [← map_zpow]
        exact congrArg
          (fun w : T => ρ (w : G))
          hz.symm
      rw [hzρ]
      exact Equiv.Perm.support_zpow_le _ _
    · have hvGen :
          v ∈ Subgroup.zpowers uq :=
        mem_zpowers_of_prime_card
          hTcard huqNe
      obtain ⟨z, hz⟩ :=
        Subgroup.mem_zpowers_iff.mp hvGen
      have hzρ :
          ρ (v : G) =
            (ρ (uq : G)) ^ z := by
        rw [← map_zpow]
        exact congrArg
          (fun w : T => ρ (w : G))
          hz.symm
      rw [hzρ]
      exact Equiv.Perm.support_zpow_le _ _
  calc
    (ρ (u : G)).support.card =
        (ρ uqG).support.card := by
      change
        (ρ (u : G)).support.card =
          (ρ (q * (u : G) * q⁻¹)).support.card
      rw [map_mul, map_mul, map_inv,
        Equiv.Perm.card_support_conj]
    _ = (ρ (v : G)).support.card := by
      rw [hsupportWithin]

private theorem support_card_eq_of_order_prime_of_sylow_card_prime
    (G X : Type) [Group G] [Fintype G]
    [Fintype X] [DecidableEq X]
    (ρ : G →* Equiv.Perm X)
    {p : ℕ} [Fact p.Prime]
    (S₀ : Sylow p G) (hS₀card : Nat.card S₀ = p)
    (u v : G) (huorder : orderOf u = p)
    (hvorder : orderOf v = p) :
    (ρ u).support.card = (ρ v).support.card := by
  classical
  have huNe : u ≠ 1 := by
    intro huOne
    rw [huOne, orderOf_one] at huorder
    exact (Fact.out : Nat.Prime p).ne_one huorder.symm
  have hvNe : v ≠ 1 := by
    intro hvOne
    rw [hvOne, orderOf_one] at hvorder
    exact (Fact.out : Nat.Prime p).ne_one hvorder.symm
  let Ru : Subgroup G := Subgroup.zpowers u
  have hRuCard : Nat.card Ru = p := by
    rw [Nat.card_zpowers, huorder]
  have hRuP : IsPGroup p Ru := by
    apply IsPGroup.of_card (n := 1)
    rw [hRuCard]
    simp
  obtain ⟨S, hRuS⟩ := hRuP.exists_le_sylow
  let uS : S :=
    ⟨u, hRuS (Subgroup.mem_zpowers u)⟩
  have huSNe : uS ≠ 1 := by
    intro huSOne
    apply huNe
    exact congrArg Subtype.val huSOne
  let Rv : Subgroup G := Subgroup.zpowers v
  have hRvCard : Nat.card Rv = p := by
    rw [Nat.card_zpowers, hvorder]
  have hRvP : IsPGroup p Rv := by
    apply IsPGroup.of_card (n := 1)
    rw [hRvCard]
    simp
  obtain ⟨T, hRvT⟩ := hRvP.exists_le_sylow
  let vT : T :=
    ⟨v, hRvT (Subgroup.mem_zpowers v)⟩
  have hvTNe : vT ≠ 1 := by
    intro hvTOne
    apply hvNe
    exact congrArg Subtype.val hvTOne
  exact
    support_card_eq_of_nonidentity_mem_sylow_card_prime
      G X ρ S₀ hS₀card S T uS huSNe vT hvTNe

private theorem order_three_mem_five_stabilizer_support_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (u : fixingSubgroup P s)
    (huorder : orderOf u = 3) :
    let g : Equiv.Perm X := (u : P)
    g.support.card = 9 ∨
      g.support.card = 12 ∨
      g.support.card = 15 ∨
      g.support.card = 18 := by
  classical
  dsimp
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 3 := by
    calc
      orderOf g = orderOf (u : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 3 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsFixed :
      s ⊆ MulAction.fixedBy X (u : P) := by
    intro x hx
    exact
      (mem_fixingSubgroup_iff P).mp u.prop x hx
  have hfixedAtLeast :
      5 ≤ Fintype.card
        (MulAction.fixedBy X (u : P)) := by
    calc
      5 = s.ncard := hs.symm
      _ ≤ (MulAction.fixedBy X (u : P)).ncard :=
        Set.ncard_le_ncard hsFixed
      _ = Fintype.card
          (MulAction.fixedBy X (u : P)) := by
        rw [← Nat.card_coe_set_eq,
          Nat.card_eq_fintype_card]
  have hsupportLe : g.support.card ≤ 19 := by
    rw [Degree15.card_fixedBy_subgroup_perm,
      hcard] at hfixedAtLeast
    change 5 ≤ 24 - g.support.card at hfixedAtLeast
    omega
  have hkLe : k + 1 ≤ 6 := by
    nlinarith
  have hkCases :
      k + 1 = 1 ∨ k + 1 = 2 ∨
        k + 1 = 3 ∨ k + 1 = 4 ∨
        k + 1 = 5 ∨ k + 1 = 6 := by
    omega
  rcases hkCases with hkOne | hkTwo | hkThree |
      hkFour | hkFive | hkSix
  · have hsmall : g.support.card ≤ 7 := by
      omega
    exact False.elim
      (hnotAlt
        (alternatingGroup_le_of_nontrivial_support_le_seven
          X P hcard h5 (u : P).prop
          (by
            intro hgOne
            have hgOne' : g = 1 := by
              simpa only [g] using hgOne
            rw [hgOne', orderOf_one] at hgorder
            norm_num at hgorder)
          hsmall))
  · have hsmall : g.support.card ≤ 7 := by
      omega
    exact False.elim
      (hnotAlt
        (alternatingGroup_le_of_nontrivial_support_le_seven
          X P hcard h5 (u : P).prop
          (by
            intro hgOne
            have hgOne' : g = 1 := by
              simpa only [g] using hgOne
            rw [hgOne', orderOf_one] at hgorder
            norm_num at hgorder)
          hsmall))
  · exact Or.inl (by
      rw [← hsum, hkThree]
      norm_num)
  · exact Or.inr (Or.inl (by
      rw [← hsum, hkFour]
      norm_num))
  · exact Or.inr (Or.inr (Or.inl (by
      rw [← hsum, hkFive]
      norm_num)))
  · exact Or.inr (Or.inr (Or.inr (by
      rw [← hsum, hkSix]
      norm_num)))

theorem degree24_order_three_support_incidence
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (hP5 : MulAction.IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5)
    (d : ℕ)
    (hSupport :
      ∀ u : fixingSubgroup P s, orderOf u = 3 →
        ((((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card = d)) :
    5100480 *
        Nat.card
          {u : fixingSubgroup P s // orderOf u = 3} =
      Nat.card
          (OrderPrimeSupportElements X P 3 d) *
        (24 - d).descFactorial 5 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let localEquiv :
      {u : H // orderOf u = 3} ≃
        LocalOrderPrimeSupportElements X P s 3 d := {
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
            X P s 3 d) =
        Nat.card {u : H // orderOf u = 3} := by
    exact (Nat.card_congr localEquiv).symm
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
            X P s 3 d) =
        Nat.card
          (OrderPrimeSupportFixesEmbedding
            X P 3 d e₀) :=
    Nat.card_congr
      (localOrderPrimeSupportEquiv
        X P s 3 d e₀ he₀Range)
  have hfixed
      (u : OrderPrimeSupportElements X P 3 d) :
      Nat.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
        (24 - d).descFactorial 5 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
          (Fintype.card
            (MulAction.fixedBy X u.1)).descFactorial
              (Fintype.card (Fin 5)) :=
        Degree15.card_fixedBy_embedding
          (G := P) (X := X) (I := Fin 5) u.1
      _ = (24 - d).descFactorial 5 := by
        rw [Degree15.card_fixedBy_subgroup_perm,
          hcard, u.2.2, Fintype.card_fin]
  have hEcard : Nat.card (Fin 5 ↪ X) = 5100480 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_embedding_eq,
      Fintype.card_fin, hcard]
    norm_num [Nat.descFactorial]
  have hcount :=
    orderPrimeSupport_incidence_count
      X P hP5 3 d ((24 - d).descFactorial 5)
        hfixed e₀
  rw [hEcard, ← hLocal, hLocalCard] at hcount
  exact hcount

theorem order_three_mem_five_stabilizer_support_eq_eighteen_of_card_eq_ninety_six
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard :
      Nat.card (fixingSubgroup P s) = 96)
    (v : fixingSubgroup P s)
    (hvorder : orderOf v = 3) :
    ((((v : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = 18) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  have hP5 :
      MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  let S : Sylow 3 H := Sylow.nonempty.some
  have hScard : Nat.card S = 3 :=
    sylow_card_eq_prime_of_card_eq_prime_mul
      H 3 32 (by norm_num) (by norm_num)
        (by simpa only [H] using hHcard) S
  have hSindex : S.index = 32 := by
    have hproduct := S.index_mul_card
    rw [hScard] at hproduct
    have hHcard' : Nat.card H = 96 := by
      simpa only [H] using hHcard
    rw [hHcard'] at hproduct
    omega
  let n := Nat.card (Sylow 3 H)
  have hnDvd : n ∣ 32 := by
    have hdiv := S.card_dvd_index
    change n ∣ S.index at hdiv
    simpa only [hSindex] using hdiv
  have hnMod : n % 3 = 1 := by
    have hmod := card_sylow_modEq_one 3 H
    change n % 3 = 1 % 3 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  have hnLe : n ≤ 32 :=
    Nat.le_of_dvd (by norm_num) hnDvd
  have hnCases : n = 1 ∨ n = 4 ∨ n = 16 := by
    have hfinite :
        ∀ q : Fin 33,
          q.1 ∣ 32 →
            q.1 % 3 = 1 →
              q.1 = 1 ∨ q.1 = 4 ∨ q.1 = 16 := by
      decide
    exact hfinite ⟨n, by omega⟩ hnDvd hnMod
  have hAllCard :
      Nat.card {u : H // orderOf u = 3} =
        n * 2 := by
    have hcount :=
      card_order_prime_elements_of_sylow_card_prime
        H 3 S hScard
    change
      Nat.card {u : H // orderOf u = 3} =
        n * (3 - 1) at hcount
    norm_num at hcount ⊢
    exact hcount
  letI : Nontrivial S :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hScard]
      norm_num)
  obtain ⟨u, huNe⟩ := exists_ne (1 : S)
  have huorderS : orderOf u = 3 :=
    Degree15.orderOf_eq_prime_of_card_eq_prime
      hScard huNe
  have huorderH : orderOf (u : H) = 3 := by
    calc
      orderOf (u : H) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 3 := huorderS
  let ρ : H →* Equiv.Perm X :=
    P.subtype.comp H.subtype
  let d : ℕ :=
    (ρ (u : H)).support.card
  have hSupport
      (w : H) (hworder : orderOf w = 3) :
      (ρ w).support.card = d := by
    have heq :=
      support_card_eq_of_order_prime_of_sylow_card_prime
        H X ρ S hScard (u : H) w huorderH hworder
    exact heq.symm
  have huCases :
      d = 9 ∨ d = 12 ∨ d = 15 ∨ d = 18 := by
    have hcases :=
      order_three_mem_five_stabilizer_support_cases
        X P hcard h5 hnotAlt s hs (u : H) huorderH
    change
      ((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 9 ∨
        ((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 12 ∨
        ((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 15 ∨
        ((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 18 at hcases
    change
      ((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 9 ∨
        ((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 12 ∨
        ((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 15 ∨
        ((((u : S) : H) : P) :
          Equiv.Perm X).support.card = 18
    exact hcases
  have hSupportFixing
      (w : fixingSubgroup P s)
      (hworder : orderOf w = 3) :
      ((((w : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = d) := by
    change (ρ (w : H)).support.card = d
    exact hSupport (w : H) hworder
  have hdEighteen : d = 18 := by
    rcases huCases with hdNine | hdTwelve |
        hdFifteen | hdEighteen
    · have hcount :=
        degree24_order_three_support_incidence
          X P hcard hP5 s hs 9 (by
            intro w hw
            rw [← hdNine]
            exact hSupportFixing w hw)
      rw [hAllCard] at hcount
      rcases hnCases with hnOne | hnFour | hnSixteen
      · rw [hnOne] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
      · rw [hnFour] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
      · rw [hnSixteen] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
    · have hcount :=
        degree24_order_three_support_incidence
          X P hcard hP5 s hs 12 (by
            intro w hw
            rw [← hdTwelve]
            exact hSupportFixing w hw)
      rw [hAllCard] at hcount
      rcases hnCases with hnOne | hnFour | hnSixteen
      · rw [hnOne] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
      · rw [hnFour] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
      · rw [hnSixteen] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
    · have hcount :=
        degree24_order_three_support_incidence
          X P hcard hP5 s hs 15 (by
            intro w hw
            rw [← hdFifteen]
            exact hSupportFixing w hw)
      rw [hAllCard] at hcount
      rcases hnCases with hnOne | hnFour | hnSixteen
      · rw [hnOne] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
      · rw [hnFour] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
      · rw [hnSixteen] at hcount
        norm_num [Nat.descFactorial] at hcount
        omega
    · exact hdEighteen
  have hvSupport : (ρ v).support.card = d :=
    hSupport v hvorder
  change (ρ (v : H)).support.card = 18
  rw [← hdEighteen]
  exact hvSupport

private theorem orderThreeSupportEighteen_support_centralizer_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (u : OrderPrimeSupportElements X P 3 18) :
    let g : Equiv.Perm X := u.1
    let gSupport : Equiv.Perm g.support :=
      g.subtypePerm (fun _ => g.apply_mem_support)
    Nat.card
        (Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support))) =
      524880 := by
  classical
  dsimp
  let g : Equiv.Perm X := u.1
  have hgorder : orderOf g = 3 := by
    calc
      orderOf g = orderOf u.1 :=
        Subgroup.orderOf_coe _
      _ = 3 := u.2.1
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, u.2.2] at hsum
  have hkSix : k + 1 = 6 := by omega
  have hcycleType :
      g.cycleType = {3, 3, 3, 3, 3, 3} := by
    rw [hk, hgorder, hkSix]
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
  have hsupportTypeCard :
      Fintype.card g.support = 18 := by
    rw [Fintype.card_coe, u.2.2]
  rw [Equiv.Perm.nat_card_centralizer,
    hgSupportCycleType, hcycleType,
    hsupportTypeCard]
  norm_num

private theorem orderThreeSupportEighteen_stabilizer_card_dvd_support_centralizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : OrderPrimeSupportElements X P 3 18) :
    let g : Equiv.Perm X := u.1
    let gSupport : Equiv.Perm g.support :=
      g.subtypePerm (fun _ => g.apply_mem_support)
    Nat.card
        (MulAction.stabilizer (ConjAct P) u) ∣
      Nat.card
        (Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support))) := by
  classical
  dsimp
  let g : Equiv.Perm X := u.1
  let K : Subgroup (ConjAct P) :=
    MulAction.stabilizer (ConjAct P) u
  let centMap :
      K →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    orderPrimeSupportStabilizerToCentralizer
      X P 3 18 u
  let supportMap : K →* Equiv.Perm g.support :=
    (Degree19.centralizerToSupport g).comp centMap
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hsupportMapMem :
      ∀ q : K, supportMap q ∈
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change
      (centMap q : Equiv.Perm X) (g x.1) =
        g ((centMap q : Equiv.Perm X) x.1)
    have hcomm :
        Commute (centMap q : Equiv.Perm X) g :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap q).prop
    exact
      congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
  let supportCentMap :
      K →*
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
    let w : K := a * b⁻¹
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
    let wP : P := ConjAct.ofConjAct w.1
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
        wPerm.support.card ≤ 6 := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ = 6 := by
          rw [Finset.card_compl, hcard, u.2.2]
    have hwPermNe : wPerm ≠ 1 := by
      intro hwOne
      apply hwNe
      apply Subtype.ext
      apply ConjAct.ofConjAct.injective
      apply Subtype.ext
      exact hwOne
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 wP.prop hwPermNe (by
          change wPerm.support.card ≤ 7
          omega))
  exact
    Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective

theorem orderThreeSupportEighteen_stabilizer_card_dvd_two_thousand_one_hundred_sixty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 489646080)
    (u : OrderPrimeSupportElements X P 3 18) :
    Nat.card
        (MulAction.stabilizer (ConjAct P) u) ∣
      2160 := by
  classical
  have hSupportDvd :=
    orderThreeSupportEighteen_stabilizer_card_dvd_support_centralizer
      X P hcard h5 hnotAlt u
  have hSupportCard :=
    orderThreeSupportEighteen_support_centralizer_card
      X P u
  dsimp only at hSupportDvd hSupportCard
  rw [hSupportCard] at hSupportDvd
  have hGroupDvd :
      Nat.card
          (MulAction.stabilizer (ConjAct P) u) ∣
        Nat.card (ConjAct P) :=
    Subgroup.card_subgroup_dvd_card _
  have hConjActCard :
      Nat.card (ConjAct P) = 489646080 := by
    rw [Nat.card_eq_fintype_card,
      ConjAct.card,
      ← Nat.card_eq_fintype_card,
      hPcard]
  rw [hConjActCard] at hGroupDvd
  have hGcd :=
    Nat.dvd_gcd hSupportDvd hGroupDvd
  norm_num at hGcd ⊢
  exact hGcd

end FiveTransitive.Degree24

end CFSG
