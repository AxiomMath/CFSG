module

public import CFSG.GH74.GLS.Stage4.Q9.ThetaModel
public import CFSG.GH74.GLS.Stage4.Q9.FrobCount
public import CFSG.GH74.GLS.Stage4.Q9.ThetaPropsInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBase
import CFSG.GH74.GLS.Stage4.Q9.ChatOrders
import CFSG.GH74.GLS.Stage4.Q9.Tables
public import CFSG.GH74.GLS.Stage4.Q9.DFactsInputs
import Mathlib.Data.List.Count

public section

namespace CertificateChecks.KernelDirect.C5103

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Q9
open CFSG.GH74.GLS.Stage4.Q9.ThetaProps
open CFSG Subgroup

theorem univ_val_of_list {α : Type} [Fintype α] [DecidableEq α] (L : List α) (hmem : ∀ x, x ∈ L)
    (hlen : L.length = Fintype.card α) : (Finset.univ : Finset α).val = (L : Multiset α) := by
  have hall : L.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (hmem x)
  have hd : L.dedup.length = L.length := by
    rw [← List.card_toFinset, hall, Finset.card_univ, hlen]
  have he : L.dedup = L := (List.dedup_sublist L).eq_of_length hd
  rw [← hall, List.toFinset_val, he]

theorem mem_f9List' (x : F9) : x ∈ DFacts.f9List := by
  rcases x with ⟨a, b⟩
  revert a b
  decide

theorem mem_sl2List' (M : SL2) : M ∈ DFacts.sl2List := by
  have h := M.det_coe
  rw [Matrix.det_fin_two] at h
  simp only [DFacts.sl2List, List.mem_flatMap, List.mem_filterMap]
  refine ⟨(M : Matrix (Fin 2) (Fin 2) F9) 0 0, mem_f9List' _, (M : Matrix (Fin 2) (Fin 2) F9) 0 1,
    mem_f9List' _, (M : Matrix (Fin 2) (Fin 2) F9) 1 0, mem_f9List' _,
    (M : Matrix (Fin 2) (Fin 2) F9) 1 1, mem_f9List' _, ?_⟩
  split
  · exact congrArg some (Subtype.ext (Matrix.eta_fin_two _).symm)
  · rename_i hne
    exact absurd h hne

@[expose] def lgList : List Lg :=
  DFacts.sl2List.flatMap fun M => [⟨M, 1⟩, ⟨M, Multiplicative.ofAdd 1⟩]

theorem mem_lgList (l : Lg) : l ∈ lgList := by
  rcases l with ⟨M, s⟩
  have hs : ∀ t : Multiplicative (ZMod 2), t = 1 ∨ t = Multiplicative.ofAdd 1 := by decide
  simp only [lgList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨M, mem_sl2List' M, ?_⟩
  rcases hs s with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

set_option maxRecDepth 100000 in
theorem lgList_length : lgList.length = 1440 := by decide +kernel

theorem univ_val_lg : (Finset.univ : Finset Lg).val = (lgList : Multiset Lg) :=
  univ_val_of_list lgList mem_lgList (by rw [lgList_length, ← Nat.card_eq_fintype_card, card_Lg])

theorem take_flatten_chunks {α : Type} (L : List α) (c : Nat) : ∀ m : Nat,
    ((List.range m).map fun j => (L.drop (j * c)).take c).flatten = L.take (m * c)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, take_flatten_chunks L c m,
      List.map_singleton, List.flatten_singleton, Nat.succ_mul, List.take_add]

theorem count_map_chunks {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) (b : β) (L : List α)
    (c m : Nat) (hlen : L.length ≤ m * c) :
    List.count b (L.map f) =
      ((List.range m).map fun j => List.count b (((L.drop (j * c)).take c).map f)).sum := by
  conv_lhs => rw [← List.take_of_length_le hlen, ← take_flatten_chunks L c m]
  rw [List.map_flatten, List.count_flatten, List.map_map, List.map_map]
  rfl

theorem getD_map_idxOf {α β : Type} [BEq α] [LawfulBEq α] (T : List α) (g : α → β) (d : β) {p : α}
    (hp : p ∈ T) : (T.map g).getD (T.idxOf p) d = g p := by
  have hlt : T.idxOf p < T.length := List.idxOf_lt_length_iff.2 hp
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some,
    Option.getD_some, List.getElem_idxOf]

@[expose] def cntR : List (List Nat) :=
  [[0, 0, 3, 3, 2, 2, 5, 10, 5, 5, 5, 5, 0, 0, 45],
    [0, 0, 2, 2, 2, 2, 13, 8, 4, 4, 4, 4, 2, 8, 35],
    [0, 0, 3, 3, 2, 2, 5, 10, 5, 5, 5, 5, 5, 20, 20],
    [0, 0, 2, 2, 2, 2, 13, 8, 4, 4, 4, 4, 5, 20, 20],
    [0, 0, 2, 2, 3, 3, 5, 10, 5, 5, 5, 5, 5, 20, 20],
    [1, 0, 7, 3, 5, 1, 4, 8, 4, 4, 4, 4, 5, 20, 20],
    [0, 0, 1, 1, 4, 4, 5, 10, 5, 5, 5, 5, 5, 20, 20],
    [0, 0, 3, 3, 1, 1, 4, 17, 4, 4, 4, 4, 5, 20, 20],
    [0, 0, 1, 1, 3, 3, 4, 17, 4, 4, 4, 4, 5, 20, 20],
    [0, 0, 3, 3, 2, 2, 5, 10, 5, 5, 5, 5, 5, 20, 20],
    [0, 1, 2, 6, 2, 6, 4, 8, 4, 4, 4, 4, 5, 20, 20],
    [0, 0, 3, 3, 2, 2, 5, 10, 5, 5, 5, 5, 5, 20, 20],
    [0, 0, 2, 2, 2, 2, 4, 17, 4, 4, 4, 4, 5, 20, 20],
    [0, 0, 2, 2, 3, 3, 5, 10, 5, 5, 5, 5, 5, 20, 20],
    [0, 0, 3, 3, 1, 1, 4, 17, 4, 4, 4, 4, 5, 20, 20],
    [0, 0, 1, 1, 4, 4, 5, 10, 5, 5, 5, 5, 5, 20, 20]]

@[expose] def chunkTyp (j : Nat) : List LTyp := ((lgList.drop (j * 90)).take 90).map typ

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem kC0 : (typTab.map fun p => List.count p.1 (chunkTyp 0)) = cntR.getD 0 [] := by
  decide +kernel

theorem kC1 : (typTab.map fun p => List.count p.1 (chunkTyp 1)) = cntR.getD 1 [] := by
  decide +kernel

theorem kC2 : (typTab.map fun p => List.count p.1 (chunkTyp 2)) = cntR.getD 2 [] := by
  decide +kernel

theorem kC3 : (typTab.map fun p => List.count p.1 (chunkTyp 3)) = cntR.getD 3 [] := by
  decide +kernel

theorem kC4 : (typTab.map fun p => List.count p.1 (chunkTyp 4)) = cntR.getD 4 [] := by
  decide +kernel

theorem kC5 : (typTab.map fun p => List.count p.1 (chunkTyp 5)) = cntR.getD 5 [] := by
  decide +kernel

theorem kC6 : (typTab.map fun p => List.count p.1 (chunkTyp 6)) = cntR.getD 6 [] := by
  decide +kernel

theorem kC7 : (typTab.map fun p => List.count p.1 (chunkTyp 7)) = cntR.getD 7 [] := by
  decide +kernel

theorem kC8 : (typTab.map fun p => List.count p.1 (chunkTyp 8)) = cntR.getD 8 [] := by
  decide +kernel

theorem kC9 : (typTab.map fun p => List.count p.1 (chunkTyp 9)) = cntR.getD 9 [] := by
  decide +kernel

theorem kC10 : (typTab.map fun p => List.count p.1 (chunkTyp 10)) = cntR.getD 10 [] := by
  decide +kernel

theorem kC11 : (typTab.map fun p => List.count p.1 (chunkTyp 11)) = cntR.getD 11 [] := by
  decide +kernel

theorem kC12 : (typTab.map fun p => List.count p.1 (chunkTyp 12)) = cntR.getD 12 [] := by
  decide +kernel

theorem kC13 : (typTab.map fun p => List.count p.1 (chunkTyp 13)) = cntR.getD 13 [] := by
  decide +kernel

theorem kC14 : (typTab.map fun p => List.count p.1 (chunkTyp 14)) = cntR.getD 14 [] := by
  decide +kernel

theorem kC15 : (typTab.map fun p => List.count p.1 (chunkTyp 15)) = cntR.getD 15 [] := by
  decide +kernel

theorem kCsum : typTab.all (fun p => decide (((List.range 16).map fun j =>
    (cntR.getD j []).getD (typTab.idxOf p) 0).sum = p.2)) = true := by
  decide +kernel

theorem typCountsOK_eq_1 : typCountsOK = true := by
  unfold typCountsOK
  simp only [univ_val_lg, Multiset.map_coe, Multiset.coe_count]
  rw [List.all_eq_true]
  intro p hp
  rw [decide_eq_true_iff, count_map_chunks typ p.1 lgList 90 16 (by rw [lgList_length])]
  have hc : ∀ j ∈ List.range 16, List.count p.1 (((lgList.drop (j * 90)).take 90).map typ) =
      (cntR.getD j []).getD (typTab.idxOf p) 0 := by
    intro j hj
    have hj' := List.mem_range.1 hj
    have hk : (typTab.map fun p => List.count p.1 (chunkTyp j)) = cntR.getD j [] := by
      match j, hj' with
        | 0, _ => exact kC0
        | 1, _ => exact kC1
        | 2, _ => exact kC2
        | 3, _ => exact kC3
        | 4, _ => exact kC4
        | 5, _ => exact kC5
        | 6, _ => exact kC6
        | 7, _ => exact kC7
        | 8, _ => exact kC8
        | 9, _ => exact kC9
        | 10, _ => exact kC10
        | 11, _ => exact kC11
        | 12, _ => exact kC12
        | 13, _ => exact kC13
        | 14, _ => exact kC14
        | 15, _ => exact kC15
        | k + 16, h => exact absurd h (by omega)
    rw [← hk, getD_map_idxOf typTab _ 0 hp]
    rfl
  rw [List.map_congr_left hc]
  exact of_decide_eq_true (List.all_eq_true.1 kCsum p hp)

theorem mem_of_sum_count {α : Type*} [DecidableEq α] (m : Multiset α) (S : Finset α)
    (h : ∑ a ∈ S, m.count a = Multiset.card m) : ∀ x ∈ m, x ∈ S := by
  intro x hx
  by_contra hxS
  have h1 : ∑ a ∈ insert x S, m.count a = m.count x + ∑ a ∈ S, m.count a := Finset.sum_insert hxS
  have h2 : ∑ a ∈ insert x S, m.count a ≤ Multiset.card m :=
    (Finset.sum_le_sum_of_ne_zero fun a _ ha =>
      Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 ha)).trans (Multiset.toFinset_sum_count_eq m).le
  have h3 : 0 < m.count x := Multiset.count_pos.2 hx
  omega

set_option maxRecDepth 100000 in
theorem typList_nodup : typList.Nodup := by
  decide +kernel

theorem mem_of_counts {β : Type} [DecidableEq β] (m : Multiset β) (T : List (β × ℕ))
    (hc : T.all (fun p => decide (m.count p.1 = p.2)) = true) (hnd : (T.map Prod.fst).Nodup)
    (hs : (T.map Prod.snd).sum = Multiset.card m) : ∀ x ∈ m, x ∈ T.map Prod.fst := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hc
  have hmap : (T.map Prod.fst).map (fun a => m.count a) = T.map Prod.snd := by
    rw [List.map_map]
    exact List.map_congr_left fun p hp => hc p hp
  have hsum : ∑ a ∈ (T.map Prod.fst).toFinset, m.count a = Multiset.card m := by
    rw [List.sum_toFinset _ hnd, hmap, hs]
  exact fun x hx => List.mem_toFinset.1 (mem_of_sum_count m _ hsum x hx)

theorem typTab_sum : (typTab.map Prod.snd).sum = 1440 := by decide +kernel

theorem card_univ_map {α β : Type} (inst : Fintype α) (f : α → β) :
    Multiset.card ((@Finset.univ α inst).val.map f) = Nat.card α := by
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Nat.card_eq_fintype_card]

theorem mem_univ_map {α β : Type} (inst : Fintype α) (f : α → β) (a : α) :
    f a ∈ (@Finset.univ α inst).val.map f :=
  Multiset.mem_map_of_mem f (Finset.mem_univ_val a)

theorem mem_of_counts_univ {α β : Type} (inst : Fintype α) (dec : DecidableEq β) (f : α → β)
    (T : List (β × ℕ))
    (hc : T.all (fun p => decide (((@Finset.univ α inst).val.map f).count p.1 = p.2)) = true)
    (hnd : (T.map Prod.fst).Nodup) (hs : (T.map Prod.snd).sum = Nat.card α) (a : α) :
    f a ∈ T.map Prod.fst :=
  mem_of_counts _ T hc hnd ((card_univ_map inst f).symm ▸ hs) (f a) (mem_univ_map inst f a)

theorem typ_memList_0 : ∀ l : Lg, typ l ∈ typList :=
  mem_of_counts_univ _ _ typ typTab typCountsOK_eq_1 typList_nodup (typTab_sum.trans card_Lg.symm)

end CertificateChecks.KernelDirect.C5103
