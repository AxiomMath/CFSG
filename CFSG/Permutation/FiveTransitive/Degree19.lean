module

public import CFSG.Permutation.FiveTransitive.Degree19CoprimeComplement
public import CFSG.Permutation.FiveTransitive.Degree19StabilizerCases
public import CFSG.Permutation.FiveTransitive.Degree19FourPointIncidence

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_nineteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq
      (s := (Set.univ : Set X)) (n := 5) (by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card,
          hcard]
        omega)
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hCases : h = 2 ∨ h = 72 := by
    simpa only [H, h] using
      five_point_stabilizer_card_eq_two_or_seventy_two
        X P hcard h5 hnotAlt s hs
  have hnotFive : ¬5 ∣ h := by
    simpa only [H, h] using
      five_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  have heNonempty : Nonempty (Fin 4 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num)
  let e : Fin 4 ↪ X := Classical.choice heNonempty
  let K : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hecard : (Set.range e).ncard = 4 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hKindexRaw :=
    hP4.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hKindexRaw
  norm_num at hKindexRaw
  have hKindex : K.index = 93024 := by
    change
      (fixingSubgroup P (Set.range e)).index = 93024
    omega
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 1395360 := by
    change (fixingSubgroup P s).index = 1395360
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 1395360 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hKindexCard := K.index_mul_card
  have hKcard : Nat.card K = 15 * h := by
    rw [hKindex, hPcard] at hKindexCard
    omega
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let T : Sylow 5 K := Sylow.nonempty.some
  have hTcard : Nat.card T = 5 :=
    sylow_five_card_eq_five_of_card_eq_fifteen_mul
      K h hKcard hnotFive T
  have hNormalizer :
      Nat.card
          (Subgroup.normalizer (T : Set K)) = 5 := by
    change
      Nat.card
          (Subgroup.normalizer
            (T : Set
              (fixingSubgroup P (Set.range e)))) = 5
    exact
      four_point_stabilizer_sylowFive_normalizer_card_eq_five
        X P hcard h5 hnotAlt s hs e T
  obtain ⟨Q, hQnormal, hComplement⟩ :=
    exists_normal_five_complement_of_normalizer_card_eq_five
      T hTcard hNormalizer
  letI : Q.Normal := hQnormal
  have hComplementCard := hComplement.card_mul
  have hQcard : Nat.card Q = 6 ∨ Nat.card Q = 216 := by
    rcases hCases with htwo | hseventyTwo
    · left
      rw [hTcard, hKcard, htwo] at hComplementCard
      omega
    · right
      rw [hTcard, hKcard, hseventyTwo] at hComplementCard
      omega
  exact
    no_self_normalizing_sylow_five_with_small_normal_complement
      T Q hTcard hNormalizer hComplement hQcard

theorem classification_of_five_transitive_of_card_eq_nineteen
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G =
          (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X :=
    MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X,
        Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    intro i
    exact hg i
  have hAlt : alternatingGroup X ≤ P :=
    alternatingGroup_le_of_five_transitive_of_card_eq_nineteen
      X P hcard h5P
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree19

end CFSG
