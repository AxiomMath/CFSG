module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoIncidence

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup
open scoped Pointwise

private abbrev FiveSubgroupCardTwentyFiveFixedNine
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) :=
  {U : Subgroup P //
    Nat.card U = 25 ∧
      Nat.card (MulAction.fixedPoints U X) = 9}

private abbrev FiveSubgroupFixesEmbedding
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (e : Fin 5 ↪ X) :=
  {U : FiveSubgroupCardTwentyFiveFixedNine X P //
    (U.1 : Subgroup P) ≤
      fixingSubgroup P (Set.range e)}

private theorem fixedPoints_map_subtype
    {G X : Type} [Group G] [MulAction G X]
    (H : Subgroup G) (T : Subgroup H) :
    MulAction.fixedPoints (T.map H.subtype) X =
      MulAction.fixedPoints T X := by
  ext x
  simp only [MulAction.mem_fixedPoints]
  constructor
  · intro hx t
    exact hx
      ⟨(t : H), ⟨t, t.prop, rfl⟩⟩
  · intro hx u
    obtain ⟨t, ht, htu⟩ := u.prop
    have hxt := hx ⟨t, ht⟩
    change ((t : H) : G) • x = x at hxt
    change (u.1 : G) • x = x
    rw [← htu]
    exact hxt

private theorem card_sylow_eq_of_mulEquiv
    {G K : Type} [Group G] [Group K]
    [Finite G] [Finite K]
    (p : ℕ) [Fact p.Prime]
    (e : G ≃* K) :
    Nat.card (Sylow p G) =
      Nat.card (Sylow p K) := by
  apply Nat.le_antisymm
  · refine Nat.card_le_card_of_surjective
      (fun S : Sylow p K =>
        Sylow.mapSurjective
          (f := e.symm.toMonoidHom)
          e.symm.surjective S) ?_
    exact Sylow.mapSurjective_surjective
      (f := e.symm.toMonoidHom)
      e.symm.surjective p
  · refine Nat.card_le_card_of_surjective
      (fun S : Sylow p G =>
        Sylow.mapSurjective
          (f := e.toMonoidHom)
          e.surjective S) ?_
    exact Sylow.mapSurjective_surjective
      (f := e.toMonoidHom)
      e.surjective p

private noncomputable def localSylowEquivFiveSubgroupFixesEmbedding
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (e : Fin 5 ↪ X)
    (hcard :
      ∀ T : Sylow 5
          (fixingSubgroup P (Set.range e)),
        Nat.card T = 25)
    (hfixed :
      ∀ T : Sylow 5
          (fixingSubgroup P (Set.range e)),
        Nat.card (MulAction.fixedPoints T X) = 9) :
    Sylow 5 (fixingSubgroup P (Set.range e)) ≃
      FiveSubgroupFixesEmbedding X P e := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P :=
    fixingSubgroup P (Set.range e)
  let forward :
      Sylow 5 H →
        FiveSubgroupFixesEmbedding X P e :=
    fun T =>
      ⟨⟨(T : Subgroup H).map H.subtype,
          ⟨by
            calc
              Nat.card
                    ((T : Subgroup H).map H.subtype) =
                  Nat.card T :=
                Nat.card_congr
                  ((T : Subgroup H).equivMapOfInjective
                    H.subtype
                    H.subtype_injective).toEquiv.symm
              _ = 25 := hcard T,
            by
              rw [fixedPoints_map_subtype]
              exact hfixed T⟩⟩,
        Subgroup.map_subtype_le
          (T : Subgroup H)⟩
  let backward :
      FiveSubgroupFixesEmbedding X P e →
        Sylow 5 H :=
    fun U =>
      Sylow.ofCard
        (U.1.1.subgroupOf H)
        (by
          let T : Sylow 5 H :=
            Sylow.nonempty.some
          calc
            Nat.card (U.1.1.subgroupOf H) =
                Nat.card U.1.1 :=
              Nat.card_congr
                (Subgroup.subgroupOfEquivOfLe
                  U.2).toEquiv
            _ = 25 := U.1.2.1
            _ = Nat.card T := (hcard T).symm
            _ =
                5 ^
                  (Nat.card H).factorization 5 :=
              T.card_eq_multiplicity)
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro T
      apply Sylow.ext
      change
        (((T : Subgroup H).map H.subtype).subgroupOf H) =
          (T : Subgroup H)
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hyx : y = x :=
          H.subtype_injective hxy
        subst y
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    right_inv := by
      intro U
      apply Subtype.ext
      apply Subtype.ext
      change
        (U.1.1.subgroupOf H).map H.subtype =
          U.1.1
      exact Subgroup.map_subgroupOf_eq_of_le U.2 }

noncomputable def fixedEmbeddingEquivEmbeddingFixedPoints
    {G X : Type} [Group G] [MulAction G X]
    (m : ℕ) (U : Subgroup G) :
    MulAction.fixedPoints U (Fin m ↪ X) ≃
      (Fin m ↪ MulAction.fixedPoints U X) where
  toFun e := {
    toFun := fun i =>
      ⟨e.1 i, by
        rw [MulAction.mem_fixedPoints]
        intro u
        have hu := e.2 u
        exact congrArg
          (fun f : Fin m ↪ X => f i) hu⟩
    inj' := by
      intro i j hij
      apply e.1.injective
      exact congrArg Subtype.val hij }
  invFun e := ⟨{
    toFun := fun i => (e i).1
    inj' := fun i j hij =>
      e.injective (Subtype.ext hij) },
    by
      rw [MulAction.mem_fixedPoints]
      intro u
      apply Function.Embedding.ext
      intro i
      exact (e i).2 u⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    rfl

private noncomputable def fiveSubgroupEmbeddingIncidenceEquiv
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) :
    (Σ e : Fin 5 ↪ X,
        FiveSubgroupFixesEmbedding X P e) ≃
      (Σ U : FiveSubgroupCardTwentyFiveFixedNine X P,
        MulAction.fixedPoints U.1 (Fin 5 ↪ X)) where
  toFun z :=
    ⟨z.2.1,
      ⟨z.1, by
        rw [MulAction.mem_fixedPoints]
        intro u
        apply Function.Embedding.ext
        intro i
        have hu := z.2.2 u.prop
        rw [mem_fixingSubgroup_iff] at hu
        exact hu (z.1 i) ⟨i, rfl⟩⟩⟩
  invFun z :=
    ⟨z.2.1,
      ⟨z.1, by
        intro u hu
        rw [mem_fixingSubgroup_iff]
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        have hfixed := z.2.2 ⟨u, hu⟩
        exact congrArg
          (fun e : Fin 5 ↪ X => e i) hfixed⟩⟩
  left_inv z := by
    rcases z with ⟨e, U, hU⟩
    rfl
  right_inv z := by
    rcases z with ⟨U, e, he⟩
    rfl

theorem smul_range_fiveEmbedding
    {G X : Type} [Group G] [MulAction G X]
    (g : G) (e : Fin 5 ↪ X) :
    g • Set.range e = Set.range (g • e) := by
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, ⟨i, rfl⟩, rfl⟩

theorem three_dvd_card_sylow_five_fixing_embedding
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (e₀ : Fin 5 ↪ X)
    (hlocalCard :
      ∀ (e : Fin 5 ↪ X)
        (T : Sylow 5
          (fixingSubgroup P (Set.range e))),
        Nat.card T = 25) :
    3 ∣ Nat.card
      (Sylow 5
        (fixingSubgroup P (Set.range e₀))) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let E := Fin 5 ↪ X
  let C :=
    FiveSubgroupCardTwentyFiveFixedNine X P
  let A :=
    Σ e : E, FiveSubgroupFixesEmbedding X P e
  let B :=
    Σ U : C,
      MulAction.fixedPoints U.1 E
  let n :=
    Nat.card
      (Sylow 5
        (fixingSubgroup P (Set.range e₀)))
  have hP5 :
      MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hlocalFixed
      (e : E)
      (T : Sylow 5
        (fixingSubgroup P (Set.range e))) :
      Nat.card (MulAction.fixedPoints T X) = 9 := by
    apply
      sylow_five_card_twenty_five_fixedPoints_eq_nine
        X P hcard h5 hnotAlt (Set.range e)
    · rw [Set.ncard_range_of_injective e.injective,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    · exact hlocalCard e T
  have hSylowFiber (e : E) :
      Nat.card
          (Sylow 5
            (fixingSubgroup P (Set.range e))) =
        n := by
    obtain ⟨q, hq⟩ :=
      hP5.exists_smul_eq e₀ e
    have hrange :
        q • Set.range e₀ = Set.range e := by
      rw [smul_range_fiveEmbedding]
      exact congrArg
        (fun f : Fin 5 ↪ X => Set.range f) hq
    let f :
        fixingSubgroup P (Set.range e₀) ≃*
          fixingSubgroup P (Set.range e) :=
      fixingSubgroupEquivFixingSubgroup hrange
    exact
      (card_sylow_eq_of_mulEquiv 5 f).symm
  have hFiberA (e : E) :
      Nat.card
          (FiveSubgroupFixesEmbedding X P e) =
        n := by
    calc
      Nat.card
          (FiveSubgroupFixesEmbedding X P e) =
          Nat.card
            (Sylow 5
              (fixingSubgroup P (Set.range e))) :=
        Nat.card_congr
          (localSylowEquivFiveSubgroupFixesEmbedding
            X P e (hlocalCard e)
              (hlocalFixed e)).symm
      _ = n := hSylowFiber e
  have hFiberB (U : C) :
      Nat.card
          (MulAction.fixedPoints U.1 E) =
        15120 := by
    calc
      Nat.card
          (MulAction.fixedPoints U.1 E) =
          Nat.card
            (Fin 5 ↪
              MulAction.fixedPoints U.1 X) :=
        Nat.card_congr
          (fixedEmbeddingEquivEmbeddingFixedPoints
            5 U.1)
      _ = 15120 := by
        rw [Nat.card_eq_fintype_card,
          Fintype.card_embedding_eq,
          Fintype.card_fin,
          ← Nat.card_eq_fintype_card,
          U.2.2]
        norm_num [Nat.descFactorial]
  have hAcard :
      Nat.card A = Nat.card E * n := by
    rw [Nat.card_sigma]
    simp_rw [hFiberA]
    rw [Finset.sum_const,
      Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      nsmul_eq_mul]
    simp
  have hBcard :
      Nat.card B = Nat.card C * 15120 := by
    rw [Nat.card_sigma]
    simp_rw [hFiberB]
    rw [Finset.sum_const,
      Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      nsmul_eq_mul]
    simp
  have hincidence :
      Nat.card A = Nat.card B :=
    Nat.card_congr
      (fiveSubgroupEmbeddingIncidenceEquiv X P)
  have hcount :
      Nat.card E * n =
        Nat.card C * 15120 := by
    rw [← hAcard, ← hBcard]
    exact hincidence
  have hEcard : Nat.card E = 5100480 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_embedding_eq,
      Fintype.card_fin,
      hcard]
    norm_num [Nat.descFactorial]
  rw [hEcard] at hcount
  change
    3 ∣ n
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

theorem sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
    (G : Type) [Group G] [Fintype G]
    (m : ℕ) (hm : m ≠ 0) (hnotFive : ¬5 ∣ m)
    (hGcard : Nat.card G = 25 * m)
    (S : Sylow 5 G) :
    Nat.card S = 25 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfactorization :
      (25 * m).factorization 5 = 2 := by
    rw [show 25 * m = 5 * (5 * m) by ring,
      Nat.factorization_mul
        (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hm),
      Finsupp.add_apply,
      (show Nat.Prime 5 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hm,
      Finsupp.add_apply,
      (show Nat.Prime 5 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hnotFive]
    norm_num
  rw [S.card_eq_multiplicity, hGcard,
    hfactorization]
  norm_num

theorem five_point_stabilizer_card_ne_eighty_nine_thousand_six_hundred_and_ne_fifty_one_thousand_two_hundred_and_ne_one_hundred_two_thousand_four_hundred
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 89600 ∧
      Nat.card (fixingSubgroup P s) ≠ 51200 ∧
      Nat.card (fixingSubgroup P s) ≠ 102400 := by
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
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change
      (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
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
      (hHcases :
        Nat.card H = 89600 ∨
          Nat.card H = 51200 ∨
          Nat.card H = 102400) :
      False := by
    have hlocalCard
        (e : Fin 5 ↪ X)
        (T : Sylow 5
          (fixingSubgroup P (Set.range e))) :
        Nat.card T = 25 := by
      let K : Subgroup P :=
        fixingSubgroup P (Set.range e)
      have hecard :
          (Set.range e).ncard = 5 := by
        rw [Set.ncard_range_of_injective e.injective,
          Nat.card_eq_fintype_card,
          Fintype.card_fin]
      have hKindexRaw :=
        hP5.index_of_fixingSubgroup_mul hecard
      rw [Nat.card_eq_fintype_card,
        hcard] at hKindexRaw
      norm_num at hKindexRaw
      have hKindex : K.index = 5100480 := by
        change
          (fixingSubgroup P
            (Set.range e)).index = 5100480
        omega
      have hKindexCard := K.index_mul_card
      have hKcard :
          Nat.card K = Nat.card H := by
        rw [hKindex] at hKindexCard
        rw [hHindex] at hHindexCard
        omega
      rcases hHcases with hFirst | hSecond | hThird
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            K 3584 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card K = Nat.card H := hKcard
            _ = 89600 := hFirst
            _ = 25 * 3584 := by norm_num)
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            K 2048 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card K = Nat.card H := hKcard
            _ = 51200 := hSecond
            _ = 25 * 2048 := by norm_num)
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            K 4096 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card K = Nat.card H := hKcard
            _ = 102400 := hThird
            _ = 25 * 4096 := by norm_num)
    have hthree :
        3 ∣ Nat.card (Sylow 5 H) := by
      have hthreeRange :=
        three_dvd_card_sylow_five_fixing_embedding
          X P hcard h5 hnotAlt e₀ hlocalCard
      rw [he₀Range] at hthreeRange
      exact hthreeRange
    let S : Sylow 5 H :=
      Sylow.nonempty.some
    have hScard : Nat.card S = 25 := by
      rcases hHcases with hFirst | hSecond | hThird
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            H 3584 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card H = 89600 := hFirst
            _ = 25 * 3584 := by norm_num)
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            H 2048 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card H = 51200 := hSecond
            _ = 25 * 2048 := by norm_num)
      · apply
          sylow_five_card_eq_twenty_five_of_card_eq_twenty_five_mul
            H 4096 (by norm_num) (by norm_num)
        exact
          (calc
            Nat.card H = 102400 := hThird
            _ = 25 * 4096 := by norm_num)
    have hSindexProduct := S.index_mul_card
    rw [hScard] at hSindexProduct
    have hSindex :
        S.index = 3584 ∨
          S.index = 2048 ∨
          S.index = 4096 := by
      omega
    have hthreeIndex :
        3 ∣ S.index :=
      hthree.trans S.card_dvd_index
    rcases hSindex with hFirst | hSecond | hThird
    · rw [hFirst] at hthreeIndex
      norm_num at hthreeIndex
    · rw [hSecond] at hthreeIndex
      norm_num at hthreeIndex
    · rw [hThird] at hthreeIndex
      norm_num at hthreeIndex
  constructor
  · intro hFirst
    exact hnotCases (Or.inl hFirst)
  constructor
  · intro hSecond
    exact hnotCases (Or.inr (Or.inl hSecond))
  · intro hThird
    exact hnotCases (Or.inr (Or.inr hThird))

end FiveTransitive.Degree24

end CFSG
