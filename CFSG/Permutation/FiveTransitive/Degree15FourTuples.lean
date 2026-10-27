module

public import CFSG.Permutation.FiveTransitive.Degree15FixedPoint

public section

namespace CFSG

namespace FiveTransitive.Degree15

private def fixedEmbeddingEquiv
    {G X I : Type} [Group G] [MulAction G X]
    (g : G) :
    MulAction.fixedBy (I ↪ X) g ≃
      (I ↪ MulAction.fixedBy X g) where
  toFun a :=
    { toFun := fun i => ⟨a.1 i, by
        rw [MulAction.mem_fixedBy]
        have hi := congrArg (fun f : I ↪ X => f i) a.2
        simpa [Function.Embedding.smul_apply] using hi⟩
      inj' := fun _ _ h => a.1.injective (congrArg Subtype.val h) }
  invFun a :=
    ⟨a.trans (Function.Embedding.subtype _), by
      rw [MulAction.mem_fixedBy]
      ext i
      exact (a i).prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fixedBy_embedding
    {G X I : Type} [Group G] [MulAction G X]
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    (g : G) :
    Fintype.card (MulAction.fixedBy (I ↪ X) g) =
      (Fintype.card (MulAction.fixedBy X g)).descFactorial
        (Fintype.card I) := by
  classical
  rw [Fintype.card_congr (fixedEmbeddingEquiv g),
    Fintype.card_embedding_eq]

private theorem stabilizer_factor_sixteen_impossible
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 360360 * 16) :
    False := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let S11 : Sylow 11 P := Sylow.nonempty.some
  have hS11card : Nat.card S11 = 11 := by
    rw [S11.card_eq_multiplicity, hPcard]
    rw [show 360360 = 11 * 32760 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  let C11 : Subgroup P :=
    Subgroup.centralizer (S11 : Set P)
  let N11 : Subgroup P :=
    Subgroup.normalizer (S11 : Set P)
  let d11 := C11.relIndex N11
  have h11 :
      d11 ∣ 10 ∧ 0 < d11 ∧ N11.index % 11 = 1 ∧
        d11 * N11.index * 11 = Nat.card P := by
    simpa only [C11, N11, d11] using
      sylow_normalizer_constraints_of_not_alternating
        X P hcard h5 hnotAlt (p := 11) (by norm_num)
          (Or.inl rfl) S11 hS11card
  have hd11le : d11 ≤ 10 :=
    Nat.le_of_dvd (by norm_num) h11.1
  have h11mod := h11.2.2.1
  have h11eq := h11.2.2.2
  rw [hPcard] at h11eq
  norm_num at h11mod h11eq
  have hd11 : d11 = 10 := by
    interval_cases d11 <;> omega
  have hN11index : N11.index = 52416 := by
    norm_num [hd11] at h11eq
    omega
  let A11 := NonidentitySylowElements 11 P
  let val11 : A11 → P := nonidentitySylowElementVal 11 P
  have hfixed11 (a : A11) :
      Fintype.card (MulAction.fixedBy X (val11 a)) = 4 := by
    rcases a with ⟨S, u⟩
    let g : Equiv.Perm X := ((u.1 : S) : P)
    have huorder : orderOf u.1 = 11 :=
      orderOf_eq_prime_of_card_eq_prime
        (sylow_card_eq_of_card_eq S11 hS11card S) u.2
    have hgorder : orderOf g = 11 := by
      change
        orderOf ((((u.1 : S) : P) : Equiv.Perm X)) = 11
      calc
        orderOf ((((u.1 : S) : P) : Equiv.Perm X)) =
            orderOf (((u.1 : S) : P)) :=
          Subgroup.orderOf_coe _
        _ = orderOf u.1 := Subgroup.orderOf_coe _
        _ = 11 := huorder
    have hgcycle : g.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order' (by
        rw [hgorder]
        norm_num) (by
          rw [hcard, hgorder]
          norm_num)
    have hgsupport : g.support.card = 11 := by
      rw [← hgcycle.orderOf, hgorder]
    rw [card_fixedBy_subgroup_perm, hcard]
    change 15 - g.support.card = 4
    rw [hgsupport]
  have hfixedEmbedding11 (a : A11) :
      Fintype.card
          (MulAction.fixedBy (Fin 4 ↪ X) (val11 a)) = 24 := by
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 4 ↪ X) (val11 a)) =
          Fintype.card
            (Fin 4 ↪ MulAction.fixedBy X (val11 a)) :=
        Fintype.card_congr (fixedEmbeddingEquiv (val11 a))
      _ = (Fintype.card
            (MulAction.fixedBy X (val11 a))).descFactorial 4 := by
        rw [Fintype.card_embedding_eq, Fintype.card_fin]
      _ = 24 := by
        rw [hfixed11]
        norm_num
  have hA11card :
      Fintype.card A11 = N11.index * 10 := by
    rw [show Fintype.card A11 =
        Fintype.card (Sylow 11 P) * (11 - 1) by
      exact card_nonidentitySylowElements S11 hS11card]
    rw [← Nat.card_eq_fintype_card,
      S11.card_eq_index_normalizer]
  have hselectedSum :
      (∑ a : A11,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val11 a))) =
        N11.index * 10 * 24 := by
    simp_rw [hfixedEmbedding11]
    simp [hA11card]
  have hvalInjective : Function.Injective val11 :=
    nonidentitySylowElementVal_injective S11 hS11card
  have hselectedLe :
      (∑ a : A11,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val11 a))) ≤
        ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) := by
    calc
      (∑ a : A11,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val11 a))) =
          ∑ q ∈ Finset.univ.image val11,
            Fintype.card
              (MulAction.fixedBy (Fin 4 ↪ X) q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5) (by omega) (by
        rw [Nat.card_eq_fintype_card, hcard]
        omega)
  letI : MulAction.IsMultiplyPretransitive P X 4 := hP4
  letI : Nonempty (Fin 4 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq, Fintype.card_fin, hcard]
      norm_num)
  letI : Unique
      (MulAction.orbitRel.Quotient P (Fin 4 ↪ X)) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P (Fin 4 ↪ X)).mp hP4)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      P (Fin 4 ↪ X)
  have hburnside' :
      (∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q)) =
        360360 * 16 := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card, hPcard] at hburnside
    exact hburnside
  rw [hselectedSum, hN11index] at hselectedLe
  rw [hburnside'] at hselectedLe
  norm_num at hselectedLe

theorem alternatingGroup_le_of_five_transitive_of_card_eq_fifteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 5) (by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      omega)
  let K : Subgroup P := fixingSubgroup P s
  have hKcard : Nat.card K = 16 :=
    five_point_stabilizer_card_eq_sixteen
      X P hcard h5 hnotAlt hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hKindex : K.index = 360360 := by
    change (fixingSubgroup P s).index = 360360
    omega
  have hKindexCard := K.index_mul_card
  have hPcard : Nat.card P = 360360 * 16 := by
    rw [hKindex, hKcard] at hKindexCard
    exact hKindexCard.symm
  exact stabilizer_factor_sixteen_impossible
    X P hcard h5 hnotAlt hPcard

theorem classification_of_five_transitive_of_card_eq_fifteen
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg⟩
  have hAlt : alternatingGroup X ≤ P :=
    alternatingGroup_le_of_five_transitive_of_card_eq_fifteen
      X P hcard h5P
  exact Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree15

end CFSG
