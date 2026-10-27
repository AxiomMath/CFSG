module

public import CFSG.Permutation.FiveTransitive.SylowFixedActionPrimeFree
public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction
import CFSG.Permutation.FiveTransitive.FixedActionGoursat
public import CFSG.Permutation.FiveTransitive.GlobalCoefficientReduction

public section

namespace CFSG

namespace FiveTransitive.SylowTwoFixedDegreeRefined

open MulAction Subgroup
open FiveTransitive.SylowFixedActionCore

private theorem fixed_degree_le_twentySeven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) ≤ 27 := by
  classical
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let : Fintype F := Fintype.ofFinite F
  let J := (MulAction.toPermHom N F).range
  let sF : Set F := {x | (x : X) ∈ s}
  have hsF : s ⊆ (F : Set X) :=
    FiveTransitive.SylowFixedActionPrimeFree.base_subset_fixedPoints X P s S
  let e : s ≃ sF :=
    { toFun := fun x ↦ ⟨⟨x.1, hsF x.2⟩, x.2⟩
      invFun := fun x ↦ ⟨x.1.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hsFcard : sF.ncard = 5 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e.symm,
      Nat.card_coe_set_eq, hs]
  have h5explicit :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ q : P, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ :=
      (MulAction.isMultiplyPretransitive_iff.mp h5) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨q, fun i ↦ DFunLike.congr_fun hq i⟩
  have hNfive : MulAction.IsMultiplyPretransitive N F 5 :=
    FiveTransitive.isMultiplyPretransitive_of_explicit N F 5
      (sylowNormalizer_five_transitive_on_fixedPoints X P h5explicit s hs S)
  have hJfive : MulAction.IsMultiplyPretransitive J F 5 :=
    FiveTransitive.isMultiplyPretransitive_range_toPermHom N F 5 hNfive
  have hfree :=
    FiveTransitive.SylowFixedActionPrimeFree.prime_not_dvd_fixedAction_stabilizer_card
      X P s S
  change ¬ 2 ∣ Nat.card (fixingSubgroup J sF) at hfree
  by_contra hlarge
  have hdegree : 28 ≤ Fintype.card F := by
    change ¬ Nat.card F ≤ 27 at hlarge
    rw [Nat.card_eq_fintype_card] at hlarge
    omega
  have heven :=
    Research.HighDegreeHallReduction.even_card_fixingSubgroup_of_five_transitive
      F J hdegree hJfive sF hsFcard
  obtain ⟨k, hk⟩ := heven
  exact hfree ⟨k, by omega⟩

theorem fixed_degree_le_eight_or_eq_twelve_of_bounded_classification
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 2 (fixingSubgroup P s))
    (hclassification :
      ∀ (Y : Type) [Fintype Y] [DecidableEq Y]
        (J : Subgroup (Equiv.Perm Y)),
        5 ≤ Fintype.card Y →
        Fintype.card Y ≤ 27 →
        MulAction.IsMultiplyPretransitive J Y 5 →
        Nat.card J = (Fintype.card Y).factorial ∨
          (7 ≤ Fintype.card Y ∧
            Nat.card J = (Fintype.card Y).factorial / 2) ∨
          (Fintype.card Y = 12 ∧ Nat.card J = 95040) ∨
          (Fintype.card Y = 24 ∧ Nat.card J = 244823040)) :
    Nat.card (sylowFixedPoints X P s S) ≤ 8 ∨
      Nat.card (sylowFixedPoints X P s S) = 12 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let : Fintype F := Fintype.ofFinite F
  let J : Subgroup (Equiv.Perm F) := (MulAction.toPermHom N F).range
  have hsF : s ⊆ (F : Set X) := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro z
    obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.mp z.prop
    have hfix := (mem_fixingSubgroup_iff P).mp u.prop x hx
    change ((z : N) : P) • x = x
    rw [show ((z : N) : P) = (u : H) by exact hu.symm]
    exact hfix
  have hFfive : 5 ≤ Fintype.card F := by
    have hle := Set.ncard_le_ncard hsF
    rw [hs, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hle
    exact hle
  have hFbound : Fintype.card F ≤ 27 := by
    simpa only [Nat.card_eq_fintype_card] using
      fixed_degree_le_twentySeven X P h5 s hs S
  have h5explicit :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ q : P, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ := (MulAction.isMultiplyPretransitive_iff.mp h5) ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨q, ?_⟩
    intro i
    exact DFunLike.congr_fun hq i
  have hNfive : MulAction.IsMultiplyPretransitive N F 5 :=
    FiveTransitive.isMultiplyPretransitive_of_explicit N F 5
      (sylowNormalizer_five_transitive_on_fixedPoints X P h5explicit s hs S)
  have hJfive : MulAction.IsMultiplyPretransitive J F 5 :=
    FiveTransitive.isMultiplyPretransitive_range_toPermHom N F 5 hNfive
  have hsmall_of_orders
      (horders : Nat.card J = (Fintype.card F).factorial ∨
        Nat.card J = (Fintype.card F).factorial / 2) :
      Fintype.card F ≤ 8 := by
    have hAlt : alternatingGroup F ≤ J :=
      FiveTransitive.FixedActionGoursat.alternatingGroup_le_of_card_eq_factorial_or_half
        F J hFfive horders
    have hbound :=
      FiveTransitive.SylowFixedActionCore.fixed_card_bound_of_alternating_normalizer_action
        X P s hs S (by simpa only [N, F, J] using hAlt)
    exact hbound.1 rfl
  change Nat.card F ≤ 8 ∨ Nat.card F = 12
  simp only [Nat.card_eq_fintype_card]
  rcases hclassification F J hFfive hFbound hJfive with hSym | hAlt | h12 | h24
  · exact Or.inl (hsmall_of_orders (Or.inl hSym))
  · exact Or.inl (hsmall_of_orders (Or.inr hAlt.2))
  · exact Or.inr h12.1
  · exfalso
    let sF : Set F := {x | (x : X) ∈ s}
    let e : s ≃ sF :=
      { toFun := fun x ↦ ⟨⟨x.1, hsF x.2⟩, x.2⟩
        invFun := fun x ↦ ⟨x.1.1, x.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hsFcard : sF.ncard = 5 := by
      rw [← Nat.card_coe_set_eq, Nat.card_congr e.symm,
        Nat.card_coe_set_eq, hs]
    let K : Subgroup J := fixingSubgroup J sF
    have hindex : K.index = (Fintype.card F).descFactorial 5 :=
      FiveTransitive.GlobalCoefficientReduction.index_fixingSubgroup_five_eq_descFactorial
        F J hJfive sF hsFcard
    rw [h24.1] at hindex
    norm_num [Nat.descFactorial] at hindex
    have hmul := K.index_mul_card
    rw [hindex, h24.2] at hmul
    have hKcard : Nat.card K = 48 := by omega
    have hfree :=
      FiveTransitive.SylowFixedActionPrimeFree.prime_not_dvd_fixedAction_stabilizer_card
        X P s S
    change ¬ 2 ∣ Nat.card K at hfree
    exact hfree (by rw [hKcard]; norm_num)

end FiveTransitive.SylowTwoFixedDegreeRefined

end CFSG
