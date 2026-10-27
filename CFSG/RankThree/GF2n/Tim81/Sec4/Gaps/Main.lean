module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Data
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.DataA7
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.DataA8
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.DataA9
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.DataMathieu
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.RankThree.GF2n.Tim81.Gaps

open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75.WCCheck
open CFSG.CGT.Timmesfeld75
open CFSG.RankThree.GF2n.Tim81

abbrev a6a : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

abbrev a6b : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [1, 2, 3, 4, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

noncomputable def a6gen (l : ℤ) : alternatingGroup (Fin 6) :=
  if l = 1 then a6a else if l = -1 then a6a⁻¹ else if l = 2 then a6b else
    if l = -2 then a6b⁻¹ else 1

theorem rep_a6gen (l : ℤ) : CFSG.Sporadic.Th.Rep 6 (a6gens l) (a6gen l) := by
  unfold a6gens a6gen
  split_ifs
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · exact CFSG.Sporadic.Th.Rep.idT (by norm_num)

theorem a6gen_neg (l : ℤ) : a6gen (-l) = (a6gen l)⁻¹ := by
  unfold a6gen
  split_ifs <;> first | omega | simp_all

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) =
    2 ^ a6GData.D.pc.length * 45 := by
  rw [show 2 ^ a6GData.D.pc.length * 45 = 360 from rfl, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

abbrev a7a : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

abbrev a7b : alternatingGroup (Fin 7) :=
  ⟨List.formPerm [0, 1, 2, 3, 4, 5, 6], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

noncomputable def a7gen (l : ℤ) : alternatingGroup (Fin 7) :=
  if l = 1 then a7a else if l = -1 then a7a⁻¹ else if l = 2 then a7b else
    if l = -2 then a7b⁻¹ else 1

theorem rep_a7gen (l : ℤ) : CFSG.Sporadic.Th.Rep 7 (a7gens l) (a7gen l) := by
  unfold a7gens a7gen
  split_ifs
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · exact CFSG.Sporadic.Th.Rep.idT (by norm_num)

theorem a7gen_neg (l : ℤ) : a7gen (-l) = (a7gen l)⁻¹ := by
  unfold a7gen
  split_ifs <;> first | omega | simp_all

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) =
    2 ^ a7GData.D.pc.length * 315 := by
  rw [show 2 ^ a7GData.D.pc.length * 315 = 2520 from rfl, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

abbrev a8a : alternatingGroup (Fin 8) :=
  ⟨List.formPerm [0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

abbrev a8b : alternatingGroup (Fin 8) :=
  ⟨List.formPerm [1, 2, 3, 4, 5, 6, 7], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

noncomputable def a8gen (l : ℤ) : alternatingGroup (Fin 8) :=
  if l = 1 then a8a else if l = -1 then a8a⁻¹ else if l = 2 then a8b else
    if l = -2 then a8b⁻¹ else 1

theorem rep_a8gen (l : ℤ) : CFSG.Sporadic.Th.Rep 8 (a8gens l) (a8gen l) := by
  unfold a8gens a8gen
  split_ifs
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · exact CFSG.Sporadic.Th.Rep.idT (by norm_num)

theorem a8gen_neg (l : ℤ) : a8gen (-l) = (a8gen l)⁻¹ := by
  unfold a8gen
  split_ifs <;> first | omega | simp_all

theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) =
    2 ^ a8GData.D.pc.length * 315 := by
  rw [show 2 ^ a8GData.D.pc.length * 315 = 20160 from rfl, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

abbrev a9a : alternatingGroup (Fin 9) :=
  ⟨List.formPerm [0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

abbrev a9b : alternatingGroup (Fin 9) :=
  ⟨List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8],
    by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

noncomputable def a9gen (l : ℤ) : alternatingGroup (Fin 9) :=
  if l = 1 then a9a else if l = -1 then a9a⁻¹ else if l = 2 then a9b else
    if l = -2 then a9b⁻¹ else 1

theorem rep_a9gen (l : ℤ) : CFSG.Sporadic.Th.Rep 9 (a9gens l) (a9gen l) := by
  unfold a9gens a9gen
  split_ifs
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · exact CFSG.Sporadic.Th.Rep.idT (by norm_num)

theorem a9gen_neg (l : ℤ) : a9gen (-l) = (a9gen l)⁻¹ := by
  unfold a9gen
  split_ifs <;> first | omega | simp_all

theorem card_alt9 : Nat.card (alternatingGroup (Fin 9)) =
    2 ^ a9GData.D.pc.length * 2835 := by
  rw [show 2 ^ a9GData.D.pc.length * 2835 = 181440 from rfl, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_m22 : Nat.card NativeSporadic.M22 =
    2 ^ m22GData.D.pc.length * 3465 := by
  rw [show 2 ^ m22GData.D.pc.length * 3465 = 443520 from rfl]
  exact CFSG.Sporadic.Mathieu.card_M22

theorem card_m23 : Nat.card NativeSporadic.M23 =
    2 ^ m23GData.D.pc.length * 79695 := by
  rw [show 2 ^ m23GData.D.pc.length * 79695 = 10200960 from rfl]
  exact CFSG.Sporadic.Schreier.m23_card

theorem card_m24 : Nat.card NativeSporadic.M24 =
    2 ^ m24GData.D.pc.length * 239085 := by
  rw [show 2 ^ m24GData.D.pc.length * 239085 = 244823040 from rfl]
  exact CFSG.Sporadic.Mathieu.card_M24

end CFSG.RankThree.GF2n.Tim81.Gaps
