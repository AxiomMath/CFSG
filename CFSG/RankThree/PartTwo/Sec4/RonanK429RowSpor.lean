module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem noE27_of_forall {X : Type} [Group X]
    (h : ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D ≠ 27) : NoE27 X :=
  fun D hD => h D hD.1 hD.2

theorem noCfgS429_of_mulEquiv {S T : Type} [Group S] [Finite S] [Group T] (e : S ≃* T)
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hout : ¬ 3 ∣ Nat.card (Outer T))
    (hE : NoE27 T) : NoCfgS429 S :=
  noCfgS429_of_autNoE27 (autNoE27_of_mulEquiv_of_noE27 e hs hna hout hE)

theorem spor_m11 :
    ¬ 3 ∣ Nat.card (Outer (Spor .M11)) ∧ NoE27 (Spor .M11) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have b' : NativeSporadic.M11 ≃* Spor .M11 := b
  have hcard : Nat.card (Spor .M11) = 7920 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M11]
  have : Finite (Spor .M11) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨?_, noE27_of_not_dvd (by rw [hcard]; norm_num)⟩
  refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
  rw [← Nat.card_congr (equivalence b').toEquiv]
  exact CFSG.Sporadic.Schreier.at_m11_schreier.1

theorem spor_m22 :
    ¬ 3 ∣ Nat.card (Outer (Spor .M22)) ∧ NoE27 (Spor .M22) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : NativeSporadic.M22 ≃* Spor .M22 := b
  have hcard : Nat.card (Spor .M22) = 443520 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
  have : Finite (Spor .M22) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨?_, noE27_of_not_dvd (by rw [hcard]; norm_num)⟩
  refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
  rw [← Nat.card_congr (equivalence b').toEquiv]
  exact Sec4.card_outer_le_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
    CFSG.Sporadic.Schreier.m22_mulAut_card

theorem spor_m23 :
    ¬ 3 ∣ Nat.card (Outer (Spor .M23)) ∧ NoE27 (Spor .M23) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : NativeSporadic.M23 ≃* Spor .M23 := b
  have hcard : Nat.card (Spor .M23) = 10200960 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Schreier.m23_card]
  have : Finite (Spor .M23) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨?_, noE27_of_not_dvd (by rw [hcard]; norm_num)⟩
  refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
  rw [← Nat.card_congr (equivalence b').toEquiv]
  exact CFSG.Sporadic.Schreier.at_m23_schreier.1

theorem spor_j1 :
    ¬ 3 ∣ Nat.card (Outer (Spor .J1)) ∧ NoE27 (Spor .J1) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have b' : NativeSporadic.J1 ≃* Spor .J1 := b
  have hcard : Nat.card (Spor .J1) = 175560 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J1.card_J1]
  have : Finite (Spor .J1) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨?_, noE27_of_not_dvd (by rw [hcard]; norm_num)⟩
  refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
  rw [← Nat.card_congr (equivalence b').toEquiv]
  exact CFSG.Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num)

theorem spor_hs :
    ¬ 3 ∣ Nat.card (Outer (Spor .HS)) ∧ NoE27 (Spor .HS) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .HS ≃* Spor .HS := b
  have hcard : Nat.card (Spor .HS) = 44352000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.HS.card_HS]
  have : Finite (Spor .HS) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨?_, noE27_of_not_dvd (by rw [hcard]; norm_num)⟩
  refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
  rw [← Nat.card_congr (equivalence b').toEquiv]
  exact CFSG.RankThree.PartOne.SPOR.card_outer_HS_le_two

theorem spor_m12 :
    ¬ 3 ∣ Nat.card (Outer (Spor .M12)) ∧ NoE27 (Spor .M12) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : NativeSporadic.M12 ≃* Spor .M12 := b
  have hcard : Nat.card (Spor .M12) = 95040 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
  have : Finite (Spor .M12) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h3 : (Nat.card (Spor .M12)).factorization 3 = 3 := by
    rw [hcard, show (95040 : ℕ) = 3 ^ 3 * 3520 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  have hloc := CFSG.RankThree.PartTwo.Toolkit.m12ThreeLocalData (Spor .M12) ⟨b'.symm⟩
  refine ⟨?_, noE27_of_forall (Item434Spor.noE27_of_extraspecial_sylow h3 fun P => (hloc P).1)⟩
  rw [← Nat.card_congr (equivalence b').toEquiv, CFSG.ComponentClassification.M12Cover.card_outer]
  norm_num

theorem spor_j2 :
    ¬ 3 ∣ Nat.card (Outer (Spor .J2)) ∧ NoE27 (Spor .J2) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b' : NativeSporadic.J2 ≃* Spor .J2 := b
  have hcard : Nat.card (Spor .J2) = 604800 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J2.card_J2]
  have : Finite (Spor .J2) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Finite NativeSporadic.J2 := Finite.of_equiv _ b'.symm.toEquiv
  have h3 : (Nat.card (Spor .J2)).factorization 3 = 3 := by
    rw [hcard, show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  refine ⟨?_, noE27_of_forall (Item434Spor.noE27_of_extraspecial_sylow h3 fun P =>
    (CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 (Spor .J2) ⟨b'.symm⟩ P _ rfl _
      rfl).1.1.1)⟩
  rw [← Nat.card_congr (equivalence b').toEquiv]
  exact Item434Spor.not_three_dvd_card_outer_of_le_two CFSG.Sporadic.Schreier.AT_J2_Schreier.1

theorem spor_m24 :
    ¬ 3 ∣ Nat.card (Outer (Spor .M24)) ∧ NoE27 (Spor .M24) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .M24 ≃* Spor .M24 := b
  have hcard : Nat.card (Spor .M24) = 244823040 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
  have : Finite (Spor .M24) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank := (CFSG.RankThree.Asc83Table.M24.table (L := Spor .M24) ⟨b'.symm⟩).2.1
  refine ⟨?_, noE27_of_forall (Item434Spor.noE27_of_pRank_le_two hrank.le)⟩
  rw [← Nat.card_congr (equivalence b').toEquiv, CFSG.Quasithin.A38c9.outer_card_M24]
  norm_num

theorem spor_j4 :
    ¬ 3 ∣ Nat.card (Outer (Spor .J4)) ∧ NoE27 (Spor .J4) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (Spor .J4) = 86775571046077562880 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.J4.card_J4]
  have : Finite (Spor .J4) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank := (CFSG.RankThree.Asc83Table.J4.table (L := Spor .J4) ⟨b'.symm⟩).2.1
  refine ⟨?_, noE27_of_forall (Item434Spor.noE27_of_pRank_le_two hrank.le)⟩
  rw [← Nat.card_congr (equivalence b').toEquiv]
  exact inputs47Core_outJ4

theorem spor_he :
    ¬ 3 ∣ Nat.card (Outer (Spor .He)) ∧ NoE27 (Spor .He) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .He ≃* Spor .He := b
  have hcard : Nat.card (Spor .He) = 4030387200 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.He.card_He]
  have : Finite (Spor .He) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Finite (NativeSporadic.Carrier .He) := Finite.of_equiv _ b'.symm.toEquiv
  have hrank := (CFSG.RankThree.Asc83Table.He.table (L := Spor .He) ⟨b'.symm⟩).2.1
  refine ⟨?_, noE27_of_forall (Item434Spor.noE27_of_pRank_le_two hrank.le)⟩
  rw [← Nat.card_congr (equivalence b').toEquiv]
  exact Item434Spor.not_three_dvd_card_outer_of_le_two CFSG.Sporadic.Schreier.AT_He_Schreier.1

theorem spor_ru :
    ¬ 3 ∣ Nat.card (Outer (Spor .Ru)) ∧ NoE27 (Spor .Ru) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .Ru ≃* Spor .Ru := b
  have bP : CFSG.Sporadic.RuSchreier.ruP ≃* Spor .Ru :=
    CFSG.Sporadic.RuSchreier.ruEquivP.symm.trans b
  have hcard : Nat.card (Spor .Ru) = 145926144000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Ru.card_Ru]
  have : Finite (Spor .Ru) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank := (CFSG.RankThree.Asc83Table.Ru.table (L := Spor .Ru) ⟨b'.symm⟩).2.1
  refine ⟨?_, noE27_of_forall (Item434Spor.noE27_of_pRank_le_two hrank.le)⟩
  rw [← Nat.card_congr (equivalence bP).toEquiv, CFSG.Sporadic.RuSchreier.card_outer_ruP]
  norm_num

section Rows

theorem rowSOf429_of_noE27 {T : Type} [Group T] (h : ¬ 3 ∣ Nat.card (Outer T) ∧ NoE27 T) :
    RowSOf429 T :=
  rowSOf429_of_noCfg fun _ _ _ hs hna ⟨e⟩ => noCfgS429_of_mulEquiv e hs hna h.1 h.2

theorem rowSOf429_m11 :
    RowSOf429 (Spor .M11) :=
  rowSOf429_of_noE27 spor_m11

theorem rowSOf429_m12 :
    RowSOf429 (Spor .M12) :=
  rowSOf429_of_noE27 spor_m12

theorem rowSOf429_m22 :
    RowSOf429 (Spor .M22) :=
  rowSOf429_of_noE27 spor_m22

theorem rowSOf429_m23 :
    RowSOf429 (Spor .M23) :=
  rowSOf429_of_noE27 spor_m23

theorem rowSOf429_m24 :
    RowSOf429 (Spor .M24) :=
  rowSOf429_of_noE27 spor_m24

theorem rowSOf429_j1 :
    RowSOf429 (Spor .J1) :=
  rowSOf429_of_noE27 spor_j1

theorem rowSOf429_j2 :
    RowSOf429 (Spor .J2) :=
  rowSOf429_of_noE27 spor_j2

theorem rowSOf429_j4 :
    RowSOf429 (Spor .J4) :=
  rowSOf429_of_noE27 spor_j4

theorem rowSOf429_hs :
    RowSOf429 (Spor .HS) :=
  rowSOf429_of_noE27 spor_hs

theorem rowSOf429_he :
    RowSOf429 (Spor .He) :=
  rowSOf429_of_noE27 spor_he

theorem rowSOf429_ru :
    RowSOf429 (Spor .Ru) :=
  rowSOf429_of_noE27 spor_ru

end Rows

end CFSG.RankThree.PartTwo.Sec4.RonanK429
