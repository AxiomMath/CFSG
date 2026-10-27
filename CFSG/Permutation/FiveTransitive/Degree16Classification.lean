module

public import CFSG.Permutation.FiveTransitive.Degree16SylowFiveGlobal
public import CFSG.Permutation.FiveTransitive.Degree16Centralizer28
public import CFSG.Permutation.FiveTransitive.Degree16SylowSeven

public section

namespace CFSG

namespace FiveTransitive.Degree16

open MulAction SubMulAction Subgroup

theorem classification_of_five_transitive_of_card_eq_sixteen
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X :=
    MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    ext i
    exact hg i
  have h5P :
      ∀ a b : Fin 5 → X,
        Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    intro i
    exact hg i
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq
      (s := (Set.univ : Set X)) (n := 5) (by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card,
          hcard]
        omega)
  let K : Subgroup P := fixingSubgroup P s
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hKindex : K.index = 524160 := by
    change (fixingSubgroup P s).index = 524160
    omega
  have hKindexCard := K.index_mul_card
  have hPcard :
      Nat.card P = 524160 * Nat.card K := by
    rw [hKindex] at hKindexCard
    exact hKindexCard.symm
  have hAlt : alternatingGroup X ≤ P := by
    by_contra hnotAlt
    letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨S, hcases⟩ :=
      sylow_seven_reduction
        X P hcard h5P hnotAlt hs
    dsimp only at hcases
    rcases hcases with htwentyFour | honeEighty
    · have hKcard : Nat.card K = 24 := htwentyFour.1
      have hPcardTwentyFour :
          Nat.card P = 12579840 := by
        calc
          Nat.card P = 524160 * Nat.card K := hPcard
          _ = 524160 * 24 :=
            congrArg (fun k => 524160 * k) hKcard
          _ = 12579840 := by norm_num
      have hScard : Nat.card S = 7 := by
        rw [S.card_eq_multiplicity, hPcardTwentyFour]
        rw [show 12579840 = 7 * 1797120 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply,
          (show Nat.Prime 7 by norm_num).factorization,
          Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
        norm_num
      exact hnotAlt
        (alternatingGroup_le_of_sylow_seven_centralizer_card_eq_twenty_eight
          X P hcard h5P S hScard htwentyFour.2.1)
    · have hKcard : Nat.card K = 180 := honeEighty.1
      have hPcardOneEighty :
          Nat.card P = 94348800 := by
        calc
          Nat.card P = 524160 * Nat.card K := hPcard
          _ = 524160 * 180 :=
            congrArg (fun k => 524160 * k) hKcard
          _ = 94348800 := by norm_num
      exact five_transitive_order_ninety_four_million_impossible
        X P hcard h5P hnotAlt hPcardOneEighty
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le
    G X (by omega) hAlt

end FiveTransitive.Degree16

end CFSG
