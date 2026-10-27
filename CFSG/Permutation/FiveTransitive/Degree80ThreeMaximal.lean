module

public import CFSG.Permutation.FiveTransitive.Degree80ThreeFixed
public import CFSG.Permutation.FiveTransitive.PrimeFiveTupleMinimalOrbitInduced
public import CFSG.Permutation.FiveTransitive.MaximalFixedSubgroupRealization
public import CFSG.Permutation.FiveTransitive.TupleSetSylowExact
public import CFSG.Permutation.FiveTransitive.ThreeCycleSemiregularDegree

public section

namespace CFSG

namespace FiveTransitive.Degree80ThreeMaximal

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem fixed_eight_and_alternating
    {X : Type} [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (U : Subgroup G) (hU : IsPGroup 3 U) (hne : U ≠ ⊥)
    (hfixU : 6 ≤ Nat.card (fixedPoints U X))
    (hmax : ∀ T : Subgroup G, IsPGroup 3 T → 6 ≤ Nat.card (fixedPoints T X) →
      Nat.card T ≤ Nat.card U) :
    let _ : Fintype (Fixed (X := X) U) := Fintype.ofFinite _
    Nat.card (Fixed (X := X) U) = 8 ∧
      alternatingGroup (Fixed (X := X) U) ≤ Image (X := X) U := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let F := Fixed (X := X) U
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨a,R,x,_,_,hx,hUP,hTx,hmin⟩ :=
    MaximalFixedSubgroupRealization.exists_minimal_orbit (k := 5) U hU hfixU hmax
  let A := ambientSylow a R
  obtain ⟨S,hS⟩ := TupleSetSylowExact.exists_set_sylow a R
  have hAcard : Nat.card A = Nat.card S := by
    change Nat.card (ambientSylow a R) = Nat.card S
    rw [← hS]
    exact Subgroup.card_map_of_injective (fixingSubgroup G (Set.range a)).subtype_injective
  have hUcard : 1 < Nat.card U := Finite.one_lt_card_iff_nontrivial.mpr
    (U.nontrivial_iff_ne_bot.mpr hne)
  have hSne : Nat.card S ≠ 1 := by
    have hb := Subgroup.card_le_of_le hUP
    change Nat.card U ≤ Nat.card A at hb
    omega
  have ha : (Set.range a).ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective a.injective
  have hfix := (Degree80ThreeFixed.three_fixed_card_and_image G hcard h5 hnotAlt (Set.range a) ha S hSne).1
  have heq : (SylowFixedActionCore.sylowFixedPoints X G (Set.range a) S : Set X) =
      fixedPoints A X := by
    have he : (SylowFixedActionCore.sylowFixedPoints X G (Set.range a) S : Set X) =
        fixedPoints (SylowFixedActionCore.sylowImage X G (Set.range a) S) X := FixedNormalizerAction.fixed_eq _
    exact he.trans (congrArg (fun Q : Subgroup G => fixedPoints Q X) hS)
  rw [heq] at hfix
  have hbase : fixedPoints A X = Set.range a := by
    have hsub : Set.range a ⊆ fixedPoints A X := PrimeTupleFixedCriterion.range_subset_fixed a R
    apply (Set.eq_of_subset_of_ncard_le hsub ?_).symm
    rw [← Nat.card_coe_set_eq,hfix,ha]
  have hx' : x ∉ fixedPoints A X := by rwa [hbase]
  have hmin' : ∀ y : X, y ∉ fixedPoints A X → Nat.card (orbit A x) ≤ Nat.card (orbit A y) := by
    simpa only [hbase] using hmin
  have hd := PrimeFiveTupleMinimalOrbitInduced.chosen h5 a R hfix x hx' hmin'
  dsimp only at hd
  rw [hTx] at hd
  obtain ⟨_,_,hlower,hdiv,htrans,hlocal,_⟩ := hd
  have hupper : Nat.card F ≤ 40 := by
    change Nat.card (Fixed (X := X) U) ≤ 40
    rw [FixedNormalizerAction.fixed_eq]
    have hh := MinimalOrbitFixedBounds.fixed_card_le_half X G (by omega) h5 hnotAlt U hne
    rwa [hcard] at hh
  change 6 ≤ Nat.card F at hlower
  change Nat.card F % 3 = 5 % 3 at hdiv
  let J := Image (X := X) U
  have hAlt : alternatingGroup F ≤ J := by
    by_cases h29 : Nat.card F = 29
    · exact Degree29Classification.alternatingGroup_le J
        (by rw [← Nat.card_eq_fintype_card,h29]) htrans
    by_cases h32 : Nat.card F = 32
    · exact PrimePredFour.alternatingGroup_le_of_sub_three_prime F J
        (by rw [← Nat.card_eq_fintype_card,h32]; norm_num) htrans
        (by rw [← Nat.card_eq_fintype_card,h32]; norm_num)
    by_cases h35 : Nat.card F = 35
    · exact PrimePredFour.alternatingGroup_le_of_sub_four_prime F J
        (by rw [← Nat.card_eq_fintype_card,h35]; norm_num) htrans
        (by rw [← Nat.card_eq_fintype_card,h35]; norm_num)
    by_cases h38 : Nat.card F = 38
    · exact TwoPrimeCycleClassification.alternatingGroup_le 17 4
        (by decide) (by decide) (Or.inr rfl) J
        (by rw [← Nat.card_eq_fintype_card,h38]) htrans
    apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F J
    · rw [← Nat.card_eq_fintype_card]; omega
    · rw [← Nat.card_eq_fintype_card]; omega
    · rw [← Nat.card_eq_fintype_card]; omega
    · rw [← Nat.card_eq_fintype_card]; omega
    · intro a b ha hb
      obtain ⟨g,hg⟩ := htrans.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ F) ⟨b,hb⟩
      exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  let b : Fin 5 ↪ F := (Fin.castLEEmb (by omega : 5 ≤ Nat.card F)).trans
    (Finite.equivFin F).symm.toEmbedding
  let T : Sylow 3 (stabilizer J b) := Sylow.nonempty.some
  obtain ⟨_,hTf,hTfree⟩ := hlocal b T
  have hle := ThreeCycleSemiregularDegree.card_le_fixed_add_three F J 5 htrans hAlt b T hTf hTfree
  rw [← Nat.card_eq_fintype_card] at hle
  change Nat.card F = 8 ∧ alternatingGroup F ≤ J
  exact ⟨by omega,hAlt⟩

end FiveTransitive.Degree80ThreeMaximal

end CFSG
