module

public import CFSG.Sporadic.M23.M23Certificate
public import CFSG.Sporadic.M23.Transitivity

public section

namespace CFSG

namespace M23.M23Group

noncomputable instance instFintypeH0 : Fintype H0 := Fintype.ofFinite H0

private lemma orbit_H0_eq : MulAction.orbit H0 (0 : Fin 23) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact ⟨t0 x, t0_maps x⟩

private lemma orbit_H1_eq : MulAction.orbit H1 (1 : Fin 23) = {x | x ≠ 0} := by
  ext x
  change x ∈ MulAction.orbit H1 (1 : Fin 23) ↔ x ≠ 0
  constructor
  · exact orbit_H1_ne_zero
  · intro hx
    exact ⟨t1 x, t1_maps x hx⟩

private lemma orbit_H2_eq :
    MulAction.orbit H2 (2 : Fin 23) = {x | x ≠ 0 ∧ x ≠ 1} := by
  ext x
  change x ∈ MulAction.orbit H2 (2 : Fin 23) ↔ x ≠ 0 ∧ x ≠ 1
  constructor
  · intro hx
    exact ⟨orbit_H2_ne_zero hx, orbit_H2_ne_one hx⟩
  · rintro ⟨hx0, hx1⟩
    exact ⟨t2 x, t2_maps x hx0 hx1⟩

private lemma orbit_H3_eq :
    MulAction.orbit H3 (3 : Fin 23) = {x | x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2} := by
  ext x
  change x ∈ MulAction.orbit H3 (3 : Fin 23) ↔ x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2
  constructor
  · intro hx
    exact ⟨orbit_H3_ne_zero hx, orbit_H3_ne_one hx, orbit_H3_ne_two hx⟩
  · rintro ⟨hx0, hx1, hx2⟩
    exact ⟨t3 x, t3_maps x hx0 hx1 hx2⟩

private lemma orbit_H4_eq : MulAction.orbit H4 (4 : Fin 23) = {x | Q x} := by
  ext x
  change x ∈ MulAction.orbit H4 (4 : Fin 23) ↔ Q x
  constructor
  · exact orbit_H4_Q
  · intro hx
    exact ⟨t4 x, t4_maps x hx⟩

private lemma orbit_H5_eq : MulAction.orbit H5 (5 : Fin 23) = {x | R x} := by
  ext x
  change x ∈ MulAction.orbit H5 (5 : Fin 23) ↔ R x
  constructor
  · exact orbit_H5_R
  · intro hx
    exact ⟨t5 x, t5_maps x hx⟩

private lemma card_orbit_H0 : Nat.card (MulAction.orbit H0 (0 : Fin 23)) = 23 := by
  rw [orbit_H0_eq]
  exact (Nat.card_congr (Equiv.Set.univ (Fin 23))).trans (Nat.card_fin 23)

private lemma card_orbit_H1 : Nat.card (MulAction.orbit H1 (1 : Fin 23)) = 22 := by
  rw [orbit_H1_eq]
  calc
    Nat.card {x : Fin 23 // x ≠ 0} =
        ((Finset.univ : Finset (Fin 23)).filter fun x ↦ x ≠ 0).card :=
      Nat.subtype_card _ (by simp)
    _ = 22 := by decide

private lemma card_orbit_H2 : Nat.card (MulAction.orbit H2 (2 : Fin 23)) = 21 := by
  rw [orbit_H2_eq]
  calc
    Nat.card {x : Fin 23 // x ≠ 0 ∧ x ≠ 1} =
        ((Finset.univ : Finset (Fin 23)).filter fun x ↦ x ≠ 0 ∧ x ≠ 1).card :=
      Nat.subtype_card _ (by simp)
    _ = 21 := by decide

private lemma card_orbit_H3 : Nat.card (MulAction.orbit H3 (3 : Fin 23)) = 20 := by
  rw [orbit_H3_eq]
  calc
    Nat.card {x : Fin 23 // x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2} =
        ((Finset.univ : Finset (Fin 23)).filter fun x ↦
          x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2).card :=
      Nat.subtype_card _ (by simp)
    _ = 20 := by decide

private lemma card_orbit_H4 : Nat.card (MulAction.orbit H4 (4 : Fin 23)) = 3 := by
  rw [orbit_H4_eq]
  calc
    Nat.card {x : Fin 23 // Q x} = ({4, 10, 16} : Finset (Fin 23)).card :=
      Nat.subtype_card _ (by intro x; simp [Q])
    _ = 3 := by decide

private lemma card_orbit_H5 : Nat.card (MulAction.orbit H5 (5 : Fin 23)) = 16 := by
  rw [orbit_H5_eq]
  calc
    Nat.card {x : Fin 23 // R x} =
        ({5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22} :
          Finset (Fin 23)).card :=
      Nat.subtype_card _ (by intro x; simp [R])
    _ = 16 := by decide

private lemma card_H6 : Nat.card H6 = 1 := by
  let : Subsingleton H6 := H6_subsingleton
  exact Nat.card_unique

theorem card_M23 : Fintype.card H0 = 10200960 := by
  have e0 : Nat.card (MulAction.orbit H0 (0 : Fin 23)) * Nat.card H1 =
      Nat.card H0 := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer H0 (0 : Fin 23)]
    exact Subgroup.index_mul_card H1
  have e1 : Nat.card (MulAction.orbit H1 (1 : Fin 23)) * Nat.card H2 =
      Nat.card H1 := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer H1 (1 : Fin 23)]
    exact Subgroup.index_mul_card H2
  have e2 : Nat.card (MulAction.orbit H2 (2 : Fin 23)) * Nat.card H3 =
      Nat.card H2 := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer H2 (2 : Fin 23)]
    exact Subgroup.index_mul_card H3
  have e3 : Nat.card (MulAction.orbit H3 (3 : Fin 23)) * Nat.card H4 =
      Nat.card H3 := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer H3 (3 : Fin 23)]
    exact Subgroup.index_mul_card H4
  have e4 : Nat.card (MulAction.orbit H4 (4 : Fin 23)) * Nat.card H5 =
      Nat.card H4 := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer H4 (4 : Fin 23)]
    exact Subgroup.index_mul_card H5
  have e5 : Nat.card (MulAction.orbit H5 (5 : Fin 23)) * Nat.card H6 =
      Nat.card H5 := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer H5 (5 : Fin 23)]
    exact Subgroup.index_mul_card H6
  simp only [card_orbit_H0, card_orbit_H1, card_orbit_H2, card_orbit_H3,
    card_orbit_H4, card_orbit_H5, card_H6] at e0 e1 e2 e3 e4 e5
  rw [← Nat.card_eq_fintype_card]
  omega

theorem four_pretransitive : MulAction.IsMultiplyPretransitive H0 (Fin 23) 4 :=
  M23.FourTransitivity.four_pretransitive_of_transversals
    t0 t1 t2 t3 t0_maps t1_maps t2_maps t3_maps

end M23.M23Group

end CFSG
