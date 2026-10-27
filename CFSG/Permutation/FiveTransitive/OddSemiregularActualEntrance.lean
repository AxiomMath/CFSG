module

public import CFSG.Permutation.FiveTransitive.OddOriginalTupleEntrance
public import CFSG.Permutation.FiveTransitive.SemiregularTupleInvolution
public import CFSG.Permutation.FiveTransitive.SemiregularFiveHallObstruction
public import CFSG.Permutation.FiveTransitive.HighDegreeCommutingInvolution

public section

namespace CFSG

namespace FiveTransitive.OddSemiregularActualEntrance

open MulAction OyamaMinimalOrbitDescent

theorem exists_entrance
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X)) (e : Fin 5 ↪ X)
    (S : Sylow 2 (stabilizer G e))
    (hfree : ∀ q : G, q ∈ ambientSylow e S → q ≠ 1 →
      ∀ x : X, x ∉ Set.range e → q • x ≠ x) :
    ∃ a : G, a ∈ ambientSylow e S ∧ orderOf a = 2 ∧ a ≠ 1 ∧ a * a = 1 ∧
      fixedBy X a = Set.range e ∧ (fixedBy X a).ncard = 5 ∧
      (∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 5) ∧
      (∀ t : G, orderOf t = 2 → 4 ≤ (fixedBy X t).ncard → (fixedBy X t).ncard = 5) ∧
      (∀ (s : Set X), s.ncard = 4 → ∀ (K : Subgroup G), IsPGroup 2 K →
        (∀ k : G, k ∈ K → ∀ x ∈ s, k • x ∈ s) →
        ∃ b : G, orderOf b = 2 ∧ b ≠ 1 ∧ b * b = 1 ∧
          (fixedBy X b).ncard = 5 ∧ (∀ x ∈ s, b • x = x) ∧
          ∀ k : G, k ∈ K → Commute b k) ∧
      ¬ IsMultiplyPretransitive G X 6 := by
  obtain ⟨hS, hfixed⟩ := OddOriginalTupleEntrance.entrance X G hcard h5 hnotAlt hodd e S
  have hrange : (Set.range e).ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective e.injective
  have hfixcard : Nat.card (fixedPoints (ambientSylow e S) X) = 5 := by
    rw [hfixed, Nat.card_coe_set_eq, hrange]
  have hfree' : ∀ q : G, q ∈ ambientSylow e S → q ≠ 1 →
      ∀ x : X, x ∉ fixedPoints (ambientSylow e S) X → q • x ≠ x := by
    simpa only [hfixed] using hfree
  have hbound : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 5 :=
    SemiregularFiveHallObstruction.involution_fixed_le_five G X h5 e S hfixcard hfree'
  have hoddNat : Odd (Nat.card X) := by simpa only [Nat.card_eq_fintype_card] using hodd
  have hfour : ∀ t : G, orderOf t = 2 → 4 ≤ (fixedBy X t).ncard →
      (fixedBy X t).ncard = 5 :=
    SemiregularFiveHallObstruction.involution_fixed_five_of_four G X hoddNat hbound
  have hdegree : 29 ≤ Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    have ho := Nat.odd_iff.mp hodd
    omega
  obtain ⟨a, ha, ha2, hfixa⟩ := SemiregularTupleInvolution.exists_fixed_range
    5 e S hS hfixed hfree
  have ha1 : a ≠ 1 := by
    intro he
    rw [he, orderOf_one] at ha2
    omega
  have haa : a * a = 1 := by simpa only [ha2, pow_two] using pow_orderOf_eq_one a
  refine ⟨a, ha, ha2, ha1, haa, hfixa, hfixa ▸ hrange, hbound, hfour, ?_,
    SemiregularFiveHallObstruction.not_six_transitive G X hdegree hbound⟩
  intro s hs K hK hpreserves
  obtain ⟨b, _, hb2, hbfix, hbcomm⟩ :=
    HighDegreeCommutingInvolution.exists_of_five_transitive G X hcard h5 s hs K hK hpreserves
  have hb1 : b ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hb2
    omega
  have hbb : b * b = 1 := by simpa only [hb2, pow_two] using pow_orderOf_eq_one b
  have hsub : s ⊆ fixedBy X b := hbfix
  have hge := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hs] at hge
  exact ⟨b, hb2, hb1, hbb, hfour b hb2 hge, hbfix, hbcomm⟩

end FiveTransitive.OddSemiregularActualEntrance

end CFSG
