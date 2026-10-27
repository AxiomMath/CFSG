module

public import CFSG.Permutation.FiveTransitive.HallSixContradiction
public import CFSG.Permutation.FiveTransitive.HallSevenContradiction
import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy

public section

namespace CFSG

namespace FiveTransitive.Research.HighDegreeHallReduction

open MulAction Subgroup

private theorem range_snoc_eq_insert_image_range
    (G X : Type*) [Group G] [MulAction G X]
    {a : X} {n : ℕ}
    (e : Fin n ↪ SubMulAction.ofStabilizer G a) :
    Set.range (SubMulAction.ofStabilizer.snoc e) =
      insert a (Subtype.val '' Set.range e) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · right
      exact ⟨e j, ⟨j, rfl⟩,
        (SubMulAction.ofStabilizer.snoc_castSucc e j).symm⟩
    · left
      exact SubMulAction.ofStabilizer.snoc_last e
  · intro hx
    rcases hx with hx | ⟨y, ⟨j, rfl⟩, rfl⟩
    · exact ⟨Fin.last n,
        (SubMulAction.ofStabilizer.snoc_last e).trans hx.symm⟩
    · exact ⟨j.castSucc,
        SubMulAction.ofStabilizer.snoc_castSucc e j⟩

theorem natCard_stabilizer_snoc_eq
    (G X : Type*) [Group G] [MulAction G X]
    {a : X} {n : ℕ}
    (e : Fin n ↪ SubMulAction.ofStabilizer G a) :
    Nat.card (MulAction.stabilizer G
        (SubMulAction.ofStabilizer.snoc e)) =
      Nat.card (MulAction.stabilizer (MulAction.stabilizer G a) e) := by
  let t : Set (SubMulAction.ofStabilizer G a) := Set.range e
  have hleft :
      fixingSubgroup G (insert a (Subtype.val '' t)) =
        MulAction.stabilizer G (SubMulAction.ofStabilizer.snoc e) := by
    rw [← range_snoc_eq_insert_image_range G X e]
    exact FiveTransitive.BaseSylowConjugacy.fixing_range_eq_stabilizer G X _
  have hright :
      fixingSubgroup (MulAction.stabilizer G a) t =
        MulAction.stabilizer (MulAction.stabilizer G a) e :=
    FiveTransitive.BaseSylowConjugacy.fixing_range_eq_stabilizer
      (MulAction.stabilizer G a) (SubMulAction.ofStabilizer G a) e
  calc
    Nat.card (MulAction.stabilizer G
        (SubMulAction.ofStabilizer.snoc e)) =
        Nat.card (fixingSubgroup G (insert a (Subtype.val '' t))) := by
          rw [hleft]
    _ = Nat.card (fixingSubgroup (MulAction.stabilizer G a) t) :=
      Nat.card_congr (SubMulAction.fixingSubgroupInsertEquiv a t).toEquiv
    _ = Nat.card (MulAction.stabilizer (MulAction.stabilizer G a) e) := by
      rw [hright]

theorem fourTransitiveOddStabilizerImpossibleAtLeastTwentySeven :
    ∀ (G Y : Type) [Group G] [Finite G] [Fintype Y]
      [MulAction G Y],
      27 ≤ Nat.card Y →
      MulAction.IsMultiplyPretransitive G Y 4 →
      ∀ e : Fin 4 ↪ Y,
        ¬ Odd (Nat.card (MulAction.stabilizer G e)) := by
  intro G Y _ _ _ _ hdegree h4 e hodd
  have hdegree' : 27 ≤ Fintype.card Y := by
    simpa only [Nat.card_eq_fintype_card] using hdegree
  obtain ⟨a, b, p, q, haTwo, _haNe, hbTwo, _hbNe,
      _habTwo, _habNe, hab, haBase, hbBase, hconfiguration⟩ :=
    Research.HallConfiguration.exists_hall_configuration
      h4 (by omega) e hodd
  rcases hconfiguration with hsix | hseven
  · exact Research.HallSixContradiction.false_of_sixPointConfiguration_card_ge_twentySeven
        h4 hdegree' e hodd a b haTwo hbTwo hab haBase hbBase p q hsix
  · exact Research.HallSevenContradiction.false_of_sevenPointConfiguration_card_ge_twentySeven
        h4 hdegree' e hodd a b haTwo hbTwo hab haBase hbBase p q hseven

private theorem not_odd_card_fixingSubgroup_of_highDegreeHall
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) :
    ¬ Odd (Nat.card (fixingSubgroup P s)) := by
  have hall := FiveTransitive.Research.HighDegreeHallReduction.fourTransitiveOddStabilizerImpossibleAtLeastTwentySeven
  classical
  have hcardSubtype : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hs
  let es : Fin 5 ≃ s :=
    (Fintype.equivFinOfCardEq hcardSubtype).symm
  let e5 : Fin 5 ↪ X :=
    es.toEmbedding.trans (Function.Embedding.subtype _)
  have hrange : Set.range e5 = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es i).prop
    · intro hx
      obtain ⟨i, hi⟩ := es.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  intro hodd
  have hoddTuple : Odd (Nat.card (MulAction.stabilizer P e5)) := by
    have hEq :
        Nat.card (fixingSubgroup P (Set.range e5)) =
          Nat.card (MulAction.stabilizer P e5) :=
      congrArg (fun H : Subgroup P ↦ Nat.card H)
        (FiveTransitive.BaseSylowConjugacy.fixing_range_eq_stabilizer P X e5)
    rw [← hEq, hrange]
    exact hodd
  let _ : MulAction.IsMultiplyPretransitive P X 5 := h5
  have h2 : MulAction.IsMultiplyPretransitive P X 2 :=
    MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5)
      (by omega) (by
        rw [Nat.card_eq_fintype_card]
        omega)
  let _ : MulAction.IsMultiplyPretransitive P X 2 := h2
  let _ : MulAction.IsPretransitive P X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let a : X := e5 (Fin.last 4)
  let Y := SubMulAction.ofStabilizer P a
  let e4raw : Fin 4 ↪ X := Fin.Embedding.init e5
  have he4mem (i : Fin 4) : e4raw i ∈ Y := by
    rw [SubMulAction.mem_ofStabilizer_iff]
    change e5 i.castSucc ≠ e5 (Fin.last 4)
    exact e5.injective.ne (Fin.castSucc_ne_last i)
  let e4 : Fin 4 ↪ Y := e4raw.codRestrict Y he4mem
  have hsnoc : SubMulAction.ofStabilizer.snoc e4 = e5 := by
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [SubMulAction.ofStabilizer.snoc_castSucc]
      rfl
    · exact SubMulAction.ofStabilizer.snoc_last e4
  let K : Subgroup P := MulAction.stabilizer P a
  have h4 : MulAction.IsMultiplyPretransitive K Y 4 := by
    simpa only [K, Y] using
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := P) (α := X) (n := 4) (a := a)).mp h5
  have hodd4 : Odd (Nat.card (MulAction.stabilizer K e4)) := by
    rw [← natCard_stabilizer_snoc_eq P X e4, hsnoc]
    exact hoddTuple
  have hYcard : Nat.card Y = Fintype.card X - 1 := by
    simpa only [Y, Nat.card_eq_fintype_card] using
      SubMulAction.nat_card_ofStabilizer_eq P a
  apply hall K Y (by rw [hYcard]; omega) h4 e4
  exact hodd4

theorem even_card_fixingSubgroup_of_five_transitive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) :
    Even (Nat.card (fixingSubgroup P s)) := by
  apply Nat.not_odd_iff_even.mp
  exact not_odd_card_fixingSubgroup_of_highDegreeHall
    X P hdegree h5 s hs

end FiveTransitive.Research.HighDegreeHallReduction

end CFSG
