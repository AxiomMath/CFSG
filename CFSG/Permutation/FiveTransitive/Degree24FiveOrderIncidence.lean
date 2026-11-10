module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoDoubleCount

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

abbrev OrderFiveSupportElements
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ) :=
  {u : P //
    orderOf u = 5 ∧
      (u.1 : Equiv.Perm X).support.card = d}

abbrev OrderFiveSupportFixesEmbedding
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ)
    (e : Fin 5 ↪ X) :=
  {u : OrderFiveSupportElements X P d //
    (u.1 : P) ∈ fixingSubgroup P (Set.range e)}

abbrev LocalOrderFiveSupportElements
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    (d : ℕ) :=
  {u : fixingSubgroup P s //
    orderOf u = 5 ∧
      ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = d)}

noncomputable def localOrderFiveSupportEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    (d : ℕ) (e : Fin 5 ↪ X)
    (he : Set.range e = s) :
    LocalOrderFiveSupportElements X P s d ≃
      OrderFiveSupportFixesEmbedding X P d e where
  toFun u :=
    ⟨⟨(u.1 : fixingSubgroup P s),
        ⟨by
          calc
            orderOf
                ((u.1 : fixingSubgroup P s) : P) =
              orderOf u.1 :=
                Subgroup.orderOf_coe _
            _ = 5 := u.2.1,
        u.2.2⟩⟩,
      by
        rw [he]
        exact u.1.prop⟩
  invFun u := by
    have huFix :
        (u.1.1 : P) ∈ fixingSubgroup P s := by
      rw [← he]
      exact u.2
    let v : fixingSubgroup P s :=
      ⟨u.1.1, huFix⟩
    refine ⟨v, ⟨?_, ?_⟩⟩
    · calc
        orderOf v = orderOf (v : P) :=
          (Subgroup.orderOf_coe _).symm
        _ = orderOf u.1.1 := rfl
        _ = 5 := u.1.2.1
    · exact u.1.2.2
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def localOrderFiveElementsSupportEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (s : Set X)
    (hSupport :
      ∀ u : fixingSubgroup P s,
        orderOf u = 5 →
          ((((u : fixingSubgroup P s) : P) :
              Equiv.Perm X).support.card = 10) ∨
            ((((u : fixingSubgroup P s) : P) :
              Equiv.Perm X).support.card = 15)) :
    {u : fixingSubgroup P s // orderOf u = 5} ≃
      LocalOrderFiveSupportElements X P s 10 ⊕
        LocalOrderFiveSupportElements X P s 15 where
  toFun u :=
    if hTen :
        ((((u.1 : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card = 10) then
      Sum.inl ⟨u.1, ⟨u.2, hTen⟩⟩
    else
      Sum.inr
        ⟨u.1,
          ⟨u.2, (hSupport u.1 u.2).resolve_left hTen⟩⟩
  invFun z :=
    Sum.elim
      (fun u => ⟨u.1, u.2.1⟩)
      (fun u => ⟨u.1, u.2.1⟩) z
  left_inv u := by
    apply Subtype.ext
    by_cases hTen :
        ((((u.1 : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card = 10)
    · simp [hTen]
    · simp [hTen]
  right_inv z := by
    rcases z with u | u
    · simp [u.2.2]
    · have hTen :
          ((((u.1 : fixingSubgroup P s) : P) :
            Equiv.Perm X).support.card ≠ 10) := by
        rw [u.2.2]
        norm_num
      simp [hTen]

private noncomputable def orderFiveSupportFixesEmbeddingConjEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ)
    (g : P) (e : Fin 5 ↪ X) :
    OrderFiveSupportFixesEmbedding X P d e ≃
      OrderFiveSupportFixesEmbedding X P d (g • e) where
  toFun u :=
    ⟨⟨MulAut.conj g u.1.1,
        ⟨by
          rw [(MulAut.conj g).orderOf_eq]
          exact u.1.2.1,
        by
          change
            ((((g : P) : Equiv.Perm X) *
              (u.1.1 : P) *
              ((g : P) : Equiv.Perm X)⁻¹).support.card) = d
          rw [Equiv.Perm.card_support_conj]
          exact u.1.2.2⟩⟩,
      Set.conj_mem_fixingSubgroup
        (smul_range_fiveEmbedding g e) u.2⟩
  invFun u :=
    ⟨⟨MulAut.conj g⁻¹ u.1.1,
        ⟨by
          rw [(MulAut.conj g⁻¹).orderOf_eq]
          exact u.1.2.1,
        by
          change
            ((((g⁻¹ : P) : Equiv.Perm X) *
              (u.1.1 : P) *
              ((g⁻¹ : P) : Equiv.Perm X)⁻¹).support.card) = d
          rw [Equiv.Perm.card_support_conj]
          exact u.1.2.2⟩⟩,
      by
        apply Set.conj_mem_fixingSubgroup
          (M := P) (α := X)
        · rw [smul_range_fiveEmbedding]
          exact congrArg
            (fun f : Fin 5 ↪ X => Set.range f)
            (inv_smul_smul g e)
        · exact u.2⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change
      g⁻¹ * (g * u.1.val * g⁻¹) * g =
        u.1.val
    group
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change
      g * (g⁻¹ * u.1.val * g) * g⁻¹ =
        u.1.val
    group

private noncomputable def orderFiveSupportEmbeddingIncidenceEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (d : ℕ) :
    (Σ e : Fin 5 ↪ X,
        OrderFiveSupportFixesEmbedding X P d e) ≃
      (Σ u : OrderFiveSupportElements X P d,
        MulAction.fixedBy (Fin 5 ↪ X) u.1) where
  toFun z :=
    ⟨z.2.1,
      ⟨z.1, by
        apply Function.Embedding.ext
        intro i
        have hmem :
            z.1 i ∈ Set.range z.1 :=
          ⟨i, rfl⟩
        have hu :=
          (mem_fixingSubgroup_iff P).mp
            z.2.2 (z.1 i) hmem
        exact hu⟩⟩
  invFun z :=
    ⟨z.2.1,
      ⟨z.1, by
        rw [mem_fixingSubgroup_iff]
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact congrArg
          (fun e : Fin 5 ↪ X => e i) z.2.2⟩⟩
  left_inv z := by
    rcases z with ⟨e, u, hu⟩
    rfl
  right_inv z := by
    rcases z with ⟨u, e, he⟩
    rfl

theorem orderFiveSupport_incidence_count
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hP5 : MulAction.IsMultiplyPretransitive P X 5)
    (d fixedCount : ℕ)
    (hfixed :
      ∀ u : OrderFiveSupportElements X P d,
        Nat.card
          (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
            fixedCount)
    (e₀ : Fin 5 ↪ X) :
    Nat.card (Fin 5 ↪ X) *
        Nat.card
          (OrderFiveSupportFixesEmbedding
            X P d e₀) =
      Nat.card (OrderFiveSupportElements X P d) *
        fixedCount := by
  classical
  let E := Fin 5 ↪ X
  let A :=
    Σ e : E,
      OrderFiveSupportFixesEmbedding X P d e
  let B :=
    Σ u : OrderFiveSupportElements X P d,
      MulAction.fixedBy E u.1
  let c :=
    Nat.card
      (OrderFiveSupportFixesEmbedding X P d e₀)
  have hFiberA (e : E) :
      Nat.card
          (OrderFiveSupportFixesEmbedding X P d e) =
        c := by
    obtain ⟨g, hg⟩ :=
      hP5.exists_smul_eq e e₀
    subst e₀
    exact Nat.card_congr
      (orderFiveSupportFixesEmbeddingConjEquiv
        X P d g e)
  have hAcard :
      Nat.card A = Nat.card E * c := by
    rw [Nat.card_sigma]
    simp_rw [hFiberA]
    rw [Finset.sum_const,
      Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      nsmul_eq_mul]
    simp
  have hBcard :
      Nat.card B =
        Nat.card (OrderFiveSupportElements X P d) *
          fixedCount := by
    have hfixed' (u : OrderFiveSupportElements X P d) :
        Nat.card (MulAction.fixedBy E u.1) =
          fixedCount :=
      hfixed u
    rw [Nat.card_sigma]
    simp_rw [hfixed']
    rw [Finset.sum_const,
      Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      nsmul_eq_mul]
    simp
  calc
    Nat.card E * c = Nat.card A := hAcard.symm
    _ = Nat.card B :=
      Nat.card_congr
        (orderFiveSupportEmbeddingIncidenceEquiv
          X P d)
    _ =
        Nat.card (OrderFiveSupportElements X P d) *
          fixedCount :=
      hBcard

theorem order_five_mem_five_stabilizer_support_eq_ten_or_fifteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (u : fixingSubgroup P s)
    (huorder : orderOf u = 5) :
    ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = 10) ∨
      ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = 15) := by
  classical
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf (u : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := huorder
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
    have huSupportLe :
        (((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card ≤ 19 := by
      rw [Degree15.card_fixedBy_subgroup_perm,
        hcard] at hfixedAtLeast
      omega
    exact huSupportLe
  have hkCases :
      k + 1 = 1 ∨ k + 1 = 2 ∨ k + 1 = 3 := by
    have hkLe : k + 1 ≤ 3 := by
      by_contra hle
      have hfour : 4 ≤ k + 1 := by
        omega
      have htwenty :
          20 ≤ g.support.card := by
        calc
          20 = 4 * 5 := by norm_num
          _ ≤ (k + 1) * 5 :=
            Nat.mul_le_mul_right 5 hfour
          _ = g.support.card := hsum
      omega
    omega
  rcases hkCases with hkOne | hkTwo | hkThree
  · have hsupport : g.support.card = 5 := by
      omega
    exact False.elim
      (hnotAlt
        (alternatingGroup_le_of_nontrivial_support_le_seven
          X P hcard h5
          ((u : P).prop)
          (by
            intro hu
            have huP : (u : P) = 1 :=
              Subtype.ext hu
            have hgOne : g = 1 := by
              change
                ((u : P) : Equiv.Perm X) = 1
              exact congrArg Subtype.val huP
            rw [hgOne, orderOf_one] at hgorder
            norm_num at hgorder)
          (by
            change g.support.card ≤ 7
            omega)))
  · left
    simpa only [g] using
      (show g.support.card = 10 by omega)
  · right
    simpa only [g] using
      (show g.support.card = 15 by omega)

theorem sylow_five_card_eq_five_of_card_eq_five_mul
    (G : Type) [Group G] [Fintype G]
    (m : ℕ) (hm : m ≠ 0) (hnotFive : ¬5 ∣ m)
    (hGcard : Nat.card G = 5 * m)
    (S : Sylow 5 G) :
    Nat.card S = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfactorization :
      (5 * m).factorization 5 = 1 := by
    rw [Nat.factorization_mul (by norm_num) hm,
      Finsupp.add_apply,
      (show Nat.Prime 5 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hnotFive]
  rw [S.card_eq_multiplicity, hGcard,
    hfactorization]
  norm_num

private theorem card_sylow_five_eq_one_of_card_eq_fifteen_or_one_hundred_forty
    (G : Type) [Group G] [Fintype G]
    (hGcard : Nat.card G = 15 ∨ Nat.card G = 140) :
    Nat.card (Sylow 5 G) = 1 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 G := Classical.arbitrary (Sylow 5 G)
  have hScard : Nat.card S = 5 := by
    rcases hGcard with hFifteen | hOneHundredForty
    · exact
        sylow_five_card_eq_five_of_card_eq_five_mul
          G 3 (by norm_num) (by norm_num)
            (by simpa using hFifteen) S
    · exact
        sylow_five_card_eq_five_of_card_eq_five_mul
          G 28 (by norm_num) (by norm_num)
            (by simpa using hOneHundredForty) S
  have hSindex : S.index = 3 ∨ S.index = 28 := by
    have hproduct := S.index_mul_card
    rw [hScard] at hproduct
    rcases hGcard with hFifteen | hOneHundredForty
    · left
      rw [hFifteen] at hproduct
      omega
    · right
      rw [hOneHundredForty] at hproduct
      omega
  let n := Nat.card (Sylow 5 G)
  have hnDvd : n ∣ 3 ∨ n ∣ 28 := by
    have hdiv := S.card_dvd_index
    change n ∣ S.index at hdiv
    rcases hSindex with hThree | hTwentyEight
    · left
      simpa [hThree] using hdiv
    · right
      simpa [hTwentyEight] using hdiv
  have hnMod : n % 5 = 1 := by
    have hmod := card_sylow_modEq_one 5 G
    change n % 5 = 1 % 5 at hmod
    norm_num at hmod
    simpa only [n, Nat.card_eq_fintype_card] using hmod
  have hnLe : n ≤ 28 := by
    rcases hnDvd with hThree | hTwentyEight
    · exact Nat.le_trans
        (Nat.le_of_dvd (by norm_num) hThree) (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) hTwentyEight
  have hfinite :
      ∀ q : Fin 29,
        (q.1 ∣ 3 ∨ q.1 ∣ 28) →
          q.1 % 5 = 1 →
            q.1 = 1 := by
    decide
  exact hfinite ⟨n, by omega⟩ hnDvd hnMod

private theorem card_order_five_elements_of_card_sylow_eq_one
    (G : Type) [Group G] [Fintype G]
    (S : Sylow 5 G) (hScard : Nat.card S = 5)
    (hSylowCount : Nat.card (Sylow 5 G) = 1) :
    Nat.card {u : G // orderOf u = 5} = 4 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let A := Degree15.NonidentitySylowElements 5 G
  let B := {u : G // orderOf u = 5}
  let f : A → B :=
    fun a =>
      ⟨(a.2.1 : G), by
        calc
          orderOf (a.2.1 : G) =
              orderOf (a.2.1 : a.1) :=
            Subgroup.orderOf_coe _
          _ = 5 :=
            Degree15.orderOf_eq_prime_of_card_eq_prime
              (Degree15.sylow_card_eq_of_card_eq
                S hScard a.1) a.2.2⟩
  have hfInjective : Function.Injective f := by
    intro a b hab
    apply
      Degree15.nonidentitySylowElementVal_injective
        S hScard
    simpa only [f, Degree15.nonidentitySylowElementVal] using
      congrArg Subtype.val hab
  have hfSurjective : Function.Surjective f := by
    intro u
    have huNe : u.1 ≠ 1 := by
      intro hu
      have huOrder := u.2
      rw [hu, orderOf_one] at huOrder
      norm_num at huOrder
    let R : Subgroup G := Subgroup.zpowers u.1
    have hRcard : Nat.card R = 5 := by
      rw [Nat.card_zpowers, u.2]
    have hRisP : IsPGroup 5 R := by
      apply IsPGroup.of_card (n := 1)
      rw [hRcard]
      norm_num
    obtain ⟨T, hRT⟩ := hRisP.exists_le_sylow
    let v : T :=
      ⟨u.1, hRT (Subgroup.mem_zpowers u.1)⟩
    have hvNe : v ≠ 1 := by
      intro hv
      apply huNe
      exact congrArg Subtype.val hv
    refine ⟨⟨T, ⟨v, hvNe⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hAcard : Nat.card A = 4 := by
    rw [Nat.card_eq_fintype_card]
    change
      Fintype.card
          (Degree15.NonidentitySylowElements 5 G) =
        4
    rw [Degree15.card_nonidentitySylowElements S hScard,
      ← Nat.card_eq_fintype_card, hSylowCount]
  calc
    Nat.card B = Nat.card A :=
      (Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)).symm
    _ = 4 := hAcard

theorem five_point_stabilizer_card_ne_fifteen_and_ne_one_hundred_forty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 15 ∧
      Nat.card (fixingSubgroup P s) ≠ 140 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
  have hnotCases
      (hHcases : Nat.card H = 15 ∨ Nat.card H = 140) :
      False := by
    let S : Sylow 5 H := Sylow.nonempty.some
    have hScard : Nat.card S = 5 := by
      rcases hHcases with hFifteen | hOneHundredForty
      · exact
          sylow_five_card_eq_five_of_card_eq_five_mul
            H 3 (by norm_num) (by norm_num)
              (by simpa using hFifteen) S
      · exact
          sylow_five_card_eq_five_of_card_eq_five_mul
            H 28 (by norm_num) (by norm_num)
              (by simpa using hOneHundredForty) S
    have hSylowCount :
        Nat.card (Sylow 5 H) = 1 :=
      card_sylow_five_eq_one_of_card_eq_fifteen_or_one_hundred_forty
        H hHcases
    have hAllCard :
        Nat.card {u : H // orderOf u = 5} = 4 :=
      card_order_five_elements_of_card_sylow_eq_one
        H S hScard hSylowCount
    have hSupport
        (u : fixingSubgroup P s)
        (hu : orderOf u = 5) :
        ((((u : fixingSubgroup P s) : P) :
            Equiv.Perm X).support.card = 10) ∨
          ((((u : fixingSubgroup P s) : P) :
            Equiv.Perm X).support.card = 15) :=
      order_five_mem_five_stabilizer_support_eq_ten_or_fifteen
        X P hcard h5 hnotAlt s hs u hu
    have hPartition :=
      Nat.card_congr
        (localOrderFiveElementsSupportEquiv
          X P s hSupport)
    rw [Nat.card_sum, hAllCard] at hPartition
    have hLocalTen :
        Nat.card
            (LocalOrderFiveSupportElements
              X P s 10) =
          Nat.card
            (OrderFiveSupportFixesEmbedding
              X P 10 e₀) :=
      Nat.card_congr
        (localOrderFiveSupportEquiv
          X P s 10 e₀ he₀Range)
    have hLocalFifteen :
        Nat.card
            (LocalOrderFiveSupportElements
              X P s 15) =
          Nat.card
            (OrderFiveSupportFixesEmbedding
              X P 15 e₀) :=
      Nat.card_congr
        (localOrderFiveSupportEquiv
          X P s 15 e₀ he₀Range)
    have hfixedTen
        (u : OrderFiveSupportElements X P 10) :
        Nat.card
            (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
          240240 := by
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
            (Fintype.card
              (MulAction.fixedBy X u.1)).descFactorial
                (Fintype.card (Fin 5)) :=
          Degree15.card_fixedBy_embedding
            (G := P) (X := X) (I := Fin 5) u.1
        _ = 240240 := by
          rw [Degree15.card_fixedBy_subgroup_perm,
            hcard, u.2.2, Fintype.card_fin]
          norm_num [Nat.descFactorial]
    have hfixedFifteen
        (u : OrderFiveSupportElements X P 15) :
        Nat.card
            (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
          15120 := by
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) u.1) =
            (Fintype.card
              (MulAction.fixedBy X u.1)).descFactorial
                (Fintype.card (Fin 5)) :=
          Degree15.card_fixedBy_embedding
            (G := P) (X := X) (I := Fin 5) u.1
        _ = 15120 := by
          rw [Degree15.card_fixedBy_subgroup_perm,
            hcard, u.2.2, Fintype.card_fin]
          norm_num [Nat.descFactorial]
    have hEcard : Nat.card (Fin 5 ↪ X) = 5100480 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num [Nat.descFactorial]
    have hcountTen :=
      orderFiveSupport_incidence_count
        X P hP5 10 240240 hfixedTen e₀
    rw [hEcard, ← hLocalTen] at hcountTen
    have hcountFifteen :=
      orderFiveSupport_incidence_count
        X P hP5 15 15120 hfixedFifteen e₀
    rw [hEcard, ← hLocalFifteen] at hcountFifteen
    have hThirteen :
        13 ∣ Nat.card
          (LocalOrderFiveSupportElements X P s 10) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    have hThree :
        3 ∣ Nat.card
          (LocalOrderFiveSupportElements X P s 15) := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    obtain ⟨a, ha⟩ := hThirteen
    obtain ⟨b, hb⟩ := hThree
    omega
  constructor
  · intro hFifteen
    exact hnotCases (Or.inl hFifteen)
  · intro hOneHundredForty
    exact hnotCases (Or.inr hOneHundredForty)

end FiveTransitive.Degree24

end CFSG
