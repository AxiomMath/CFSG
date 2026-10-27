module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432E9Rot
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL52

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec4.Res417Four
  (a5 b5 r5 E9 card_E9 rs5_spec gl5EquivProjSL factorization_card_GL5 a5_mem b5_mem)

theorem ab_comm_gl5 : a5 * b5 = b5 * a5 := by
  decide +kernel

theorem closure_ab_eq_E9 : Subgroup.closure ({a5, b5} : Set (GL (Fin 5) (ZMod 2))) = E9 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact a5_mem
    · exact b5_mem
  · have ha : a5 ∈ Subgroup.closure ({a5, b5} : Set (GL (Fin 5) (ZMod 2))) :=
      Subgroup.subset_closure (by simp)
    have hb : b5 ∈ Subgroup.closure ({a5, b5} : Set (GL (Fin 5) (ZMod 2))) :=
      Subgroup.subset_closure (by simp)
    exact sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)

theorem card_closure_ab :
    Nat.card (Subgroup.closure ({a5, b5} : Set (GL (Fin 5) (ZMod 2)))) = 9 := by
  rw [closure_ab_eq_E9]
  exact card_E9

theorem not_27_dvd_card_gl5 : ¬ 27 ∣ Nat.card (GL (Fin 5) (ZMod 2)) := by
  intro h
  have hne : Nat.card (GL (Fin 5) (ZMod 2)) ≠ 0 := by
    intro h0
    have h2 := factorization_card_GL5
    rw [h0, Nat.factorization_zero] at h2
    simp at h2
  have h3 : 3 ^ 3 ∣ Nat.card (GL (Fin 5) (ZMod 2)) := h
  have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h3
  rw [factorization_card_GL5] at h4
  omega

theorem listRow_gl5 : ListRow (GL (Fin 5) (ZMod 2)) :=
  listRow_of_E9_rotation (a := a5) (b := b5) (r := r5) ab_comm_gl5 rs5_spec.1 rs5_spec.2.1
    card_closure_ab not_27_dvd_card_gl5

theorem listRow_l52 [Finite (projSL 5 (GaloisField 2 1))] :
    ListRow (projSL 5 (GaloisField 2 1)) :=
  ListRow.of_mulEquiv gl5EquivProjSL listRow_gl5

theorem outerRow_l52 [Finite (projSL 5 (GaloisField 2 1))] :
    OuterRow (projSL 5 (GaloisField 2 1)) :=
  outerRow_of_not_three_dvd_outer
    (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num))

theorem row_l52 : RowOf (projSL 5 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSL 5 (GaloisField 2 1)) := Finite.of_equiv S e.toEquiv
  exact GoodRow.of_mulEquiv e.symm ⟨listRow_l52, outerRow_l52⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
