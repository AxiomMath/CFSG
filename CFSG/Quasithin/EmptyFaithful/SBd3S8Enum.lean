module

public import CFSG.Quasithin.EmptyFaithful.SBd3S8Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.SBd3S8

open Equiv CFSG.QuasithinUnique

attribute [local instance] decEqS8

set_option maxRecDepth 100000

@[expose] def AllW2 (Q : List (Fin 8) → Prop) : Prop :=
  ∀ a0 ∈ List.finRange 8,
  ∀ a1 ∈ List.finRange 8, a1 ≠ a0 → blk2 a1 = blk2 a0 →
  ∀ a2 ∈ List.finRange 8, a2 ≠ a0 → a2 ≠ a1 →
  ∀ a3 ∈ List.finRange 8, a3 ≠ a0 → a3 ≠ a1 → a3 ≠ a2 → blk2 a3 = blk2 a2 →
  ∀ a4 ∈ List.finRange 8, a4 ≠ a0 → a4 ≠ a1 → a4 ≠ a2 → a4 ≠ a3 →
  ∀ a5 ∈ List.finRange 8, a5 ≠ a0 → a5 ≠ a1 → a5 ≠ a2 → a5 ≠ a3 → a5 ≠ a4 → blk2 a5 = blk2 a4 →
  ∀ a6 ∈ List.finRange 8, a6 ≠ a0 → a6 ≠ a1 → a6 ≠ a2 → a6 ≠ a3 → a6 ≠ a4 → a6 ≠ a5 →
  ∀ a7 ∈ List.finRange 8, a7 ≠ a0 → a7 ≠ a1 → a7 ≠ a2 → a7 ≠ a3 → a7 ≠ a4 → a7 ≠ a5 → a7 ≠ a6 →
    blk2 a7 = blk2 a6 →
    Q [a0, a1, a2, a3, a4, a5, a6, a7]

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance (Q : List (Fin 8) → Prop) [DecidablePred Q] : Decidable (AllW2 Q) := by
  unfold AllW2; infer_instance

theorem allW2_apply {Q : List (Fin 8) → Prop} (h : AllW2 Q) {g : S8} (hg : PW2 g) :
    Q (tupleOf g) := by
  have hne : ∀ i j : Fin 8, i ≠ j → g i ≠ g j := fun i j hij hgij => hij (g.injective hgij)
  have hb : ∀ i j : Fin 8, blk2 i = blk2 j → blk2 (g i) = blk2 (g j) := fun i j hij =>
    (hg i j).1 hij
  exact h (g 0) (List.mem_finRange _)
    (g 1) (List.mem_finRange _) (hne 1 0 (by decide)) (hb 1 0 (by decide))
    (g 2) (List.mem_finRange _) (hne 2 0 (by decide)) (hne 2 1 (by decide))
    (g 3) (List.mem_finRange _) (hne 3 0 (by decide)) (hne 3 1 (by decide)) (hne 3 2 (by decide))
      (hb 3 2 (by decide))
    (g 4) (List.mem_finRange _) (hne 4 0 (by decide)) (hne 4 1 (by decide)) (hne 4 2 (by decide))
      (hne 4 3 (by decide))
    (g 5) (List.mem_finRange _) (hne 5 0 (by decide)) (hne 5 1 (by decide)) (hne 5 2 (by decide))
      (hne 5 3 (by decide)) (hne 5 4 (by decide)) (hb 5 4 (by decide))
    (g 6) (List.mem_finRange _) (hne 6 0 (by decide)) (hne 6 1 (by decide)) (hne 6 2 (by decide))
      (hne 6 3 (by decide)) (hne 6 4 (by decide)) (hne 6 5 (by decide))
    (g 7) (List.mem_finRange _) (hne 7 0 (by decide)) (hne 7 1 (by decide)) (hne 7 2 (by decide))
      (hne 7 3 (by decide)) (hne 7 4 (by decide)) (hne 7 5 (by decide)) (hne 7 6 (by decide))
      (hb 7 6 (by decide))

@[expose] def quadList1 : List S8 := permsOfList ([0, 1, 2, 3] : List (Fin 8))

@[expose] def quadList2 : List S8 := permsOfList ([4, 5, 6, 7] : List (Fin 8))

@[expose] def W4list : List S8 :=
  quadList1.flatMap fun a => quadList2.flatMap fun b => [a * b, vv * (a * b)]

@[expose] def pairPermsAux : List (Fin 8) → List S8
  | [] => [1]
  | a :: l => pairPermsAux l ++ l.flatMap fun b =>
      (pairPermsAux l).map fun f => (Equiv.swap a b * Equiv.swap (a + 1) (b + 1)) * f

@[expose] def pairPerms : List S8 := pairPermsAux [0, 2, 4, 6]

@[expose] def flipList : List S8 :=
  [1, Equiv.swap 0 1].flatMap fun f0 => [1, Equiv.swap 2 3].flatMap fun f1 =>
    [1, Equiv.swap 4 5].flatMap fun f2 => [1, Equiv.swap 6 7].map fun f3 => f0 * f1 * f2 * f3

@[expose] def W2list : List S8 := flipList.flatMap fun fl => pairPerms.map fun p => fl * p

@[expose] def W2tup : List (List (Fin 8)) := W2list.map tupleOf

theorem W2tup_complete : AllW2 (fun l => l ∈ W2tup) := by decide +kernel

theorem complete_W2 {g : S8} (hg : PW2 g) : g ∈ W2list := by
  have := allW2_apply W2tup_complete hg
  obtain ⟨t, ht, e⟩ := List.mem_map.1 this
  rw [← eq_of_tupleOf_eq e]
  exact ht

theorem W2list_sound : ∀ t ∈ W2list, PW2 t := by
  have h : (W2list.all fun t => decide (PW2 t)) = true := by decide +kernel
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.1 h t ht)

@[expose] def nodupB : List (List (Fin 8)) → Bool
  | [] => true
  | x :: xs => !(decide (x ∈ xs)) && nodupB xs

theorem nodupB_nodup : ∀ l : List (List (Fin 8)), nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    have h' : x ∉ xs ∧ nodupB xs = true := by simpa [nodupB] using h
    exact List.nodup_cons.2 ⟨h'.1, nodupB_nodup xs h'.2⟩

@[expose] def Tlist : List S8 := W2list.filter fun g => decide (PW4 g)

theorem Tlist_length : Tlist.length = 128 := by decide +kernel

theorem Tlist_nodup : (Tlist.map tupleOf).Nodup := nodupB_nodup _ (by decide +kernel)

theorem card_Tstd : Nat.card ↥Tstd = 2 ^ 7 := by
  have hmem : ∀ g, g ∈ Tstd ↔ g ∈ Tlist := by
    intro g
    simp only [Tlist, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨h2, h4⟩
      exact ⟨complete_W2 h2, h4⟩
    · rintro ⟨h2, h4⟩
      exact ⟨W2list_sound g h2, h4⟩
  have hnd : Tlist.Nodup := List.Nodup.of_map _ Tlist_nodup
  have h1 : Nat.card {g // g ∈ Tlist} = Tlist.toFinset.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun g => (List.mem_toFinset (a := g)).symm),
      Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), h1, List.toFinset_card_of_nodup hnd,
    Tlist_length]
  norm_num

theorem card_S8 : Nat.card S8 = 40320 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem isSylowTwoOf_Tstd : IsSylowTwoOf Tstd ⊤ := by
  refine ⟨le_top, IsPGroup.of_card card_Tstd, ?_⟩
  show ¬ 2 ∣ Tstd.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.index_mul_card (H := Tstd)
  rw [card_Tstd, card_S8] at h
  omega

theorem sign_check : (W2list.all fun t => decide (Equiv.Perm.sign t = 1 → PAff t)) = true := by
  decide +kernel

theorem even_W2_le_Aff (g : S8) (hg : PW2 g) (hs : Equiv.Perm.sign g = 1) : PAff g :=
  (of_decide_eq_true (List.all_eq_true.1 sign_check g (complete_W2 hg))) hs

@[expose] def quadTup1 : List (List (Fin 8)) := quadList1.map fun a => [a 0, a 1, a 2, a 3]

@[expose] def quadTup2 : List (List (Fin 8)) := quadList2.map fun b => [b 4, b 5, b 6, b 7]

@[expose] def AllBlk1 (Q : List (Fin 8) → Prop) : Prop :=
  ∀ a0 ∈ List.finRange 8, blk4 a0 = 0 →
  ∀ a1 ∈ List.finRange 8, a1 ≠ a0 → blk4 a1 = 0 →
  ∀ a2 ∈ List.finRange 8, a2 ≠ a0 → a2 ≠ a1 → blk4 a2 = 0 →
  ∀ a3 ∈ List.finRange 8, a3 ≠ a0 → a3 ≠ a1 → a3 ≠ a2 → blk4 a3 = 0 →
    Q [a0, a1, a2, a3]

@[expose] def AllBlk2 (Q : List (Fin 8) → Prop) : Prop :=
  ∀ a4 ∈ List.finRange 8, blk4 a4 = 1 →
  ∀ a5 ∈ List.finRange 8, a5 ≠ a4 → blk4 a5 = 1 →
  ∀ a6 ∈ List.finRange 8, a6 ≠ a4 → a6 ≠ a5 → blk4 a6 = 1 →
  ∀ a7 ∈ List.finRange 8, a7 ≠ a4 → a7 ≠ a5 → a7 ≠ a6 → blk4 a7 = 1 →
    Q [a4, a5, a6, a7]

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance (Q : List (Fin 8) → Prop) [DecidablePred Q] : Decidable (AllBlk1 Q) := by
  unfold AllBlk1; infer_instance

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance (Q : List (Fin 8) → Prop) [DecidablePred Q] : Decidable (AllBlk2 Q) := by
  unfold AllBlk2; infer_instance

theorem blk1_complete : AllBlk1 (fun l => l ∈ quadTup1) := by decide +kernel

theorem blk2_complete : AllBlk2 (fun l => l ∈ quadTup2) := by decide +kernel

theorem blk4_lt : ∀ x : Fin 8, blk4 x < 2 := by decide

theorem quad1_fix : ∀ a ∈ quadList1, ∀ i : Fin 8, 4 ≤ i.val → a i = i := by
  have h : (quadList1.all fun a => (List.finRange 8).all fun i => decide (4 ≤ i.val → a i = i)) =
      true := by decide +kernel
  intro a ha i hi
  exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h a ha) i (List.mem_finRange _)) hi

theorem quad2_fix : ∀ b ∈ quadList2, ∀ i : Fin 8, i.val < 4 → b i = i := by
  have h : (quadList2.all fun a => (List.finRange 8).all fun i => decide (i.val < 4 → a i = i)) =
      true := by decide +kernel
  intro a ha i hi
  exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h a ha) i (List.mem_finRange _)) hi

theorem quad2_maps : ∀ b ∈ quadList2, ∀ i : Fin 8, 4 ≤ i.val → 4 ≤ (b i).val := by
  have h : (quadList2.all fun a => (List.finRange 8).all fun i =>
      decide (4 ≤ i.val → 4 ≤ (a i).val)) = true := by decide +kernel
  intro a ha i hi
  exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h a ha) i (List.mem_finRange _)) hi

theorem vv_sq : vv * vv = 1 := by decide +kernel

theorem blk4_vv : ∀ x : Fin 8, blk4 (vv x) = 1 - blk4 x := by decide +kernel

theorem complete_B4 {g : S8} (hg : PW4 g) (h0 : blk4 (g 0) = 0) :
    ∃ a ∈ quadList1, ∃ b ∈ quadList2, g = a * b := by
  have hne : ∀ i j : Fin 8, i ≠ j → g i ≠ g j := fun i j hij hgij => hij (g.injective hgij)
  have hb : ∀ i j : Fin 8, blk4 i = blk4 j → blk4 (g i) = blk4 (g j) := fun i j hij =>
    (hg i j).1 hij
  have hb' : ∀ i j : Fin 8, blk4 i ≠ blk4 j → blk4 (g i) ≠ blk4 (g j) := fun i j hij hgij =>
    hij ((hg i j).2 hgij)
  have h1 : blk4 (g 1) = 0 := by rw [← h0]; exact hb 1 0 (by decide)
  have h2 : blk4 (g 2) = 0 := by rw [← h0]; exact hb 2 0 (by decide)
  have h3 : blk4 (g 3) = 0 := by rw [← h0]; exact hb 3 0 (by decide)
  have h4 : blk4 (g 4) = 1 := by
    have := hb' 4 0 (by decide)
    have := blk4_lt (g 4)
    omega
  have h5 : blk4 (g 5) = 1 := by rw [← h4]; exact hb 5 4 (by decide)
  have h6 : blk4 (g 6) = 1 := by rw [← h4]; exact hb 6 4 (by decide)
  have h7 : blk4 (g 7) = 1 := by rw [← h4]; exact hb 7 4 (by decide)
  have hA := blk1_complete (g 0) (List.mem_finRange _) h0
    (g 1) (List.mem_finRange _) (hne 1 0 (by decide)) h1
    (g 2) (List.mem_finRange _) (hne 2 0 (by decide)) (hne 2 1 (by decide)) h2
    (g 3) (List.mem_finRange _) (hne 3 0 (by decide)) (hne 3 1 (by decide)) (hne 3 2 (by decide)) h3
  have hB := blk2_complete (g 4) (List.mem_finRange _) h4
    (g 5) (List.mem_finRange _) (hne 5 4 (by decide)) h5
    (g 6) (List.mem_finRange _) (hne 6 4 (by decide)) (hne 6 5 (by decide)) h6
    (g 7) (List.mem_finRange _) (hne 7 4 (by decide)) (hne 7 5 (by decide)) (hne 7 6 (by decide)) h7
  obtain ⟨a, ha, hae⟩ := List.mem_map.1 hA
  obtain ⟨b, hb2, hbe⟩ := List.mem_map.1 hB
  simp only [List.cons.injEq, and_true] at hae hbe
  obtain ⟨a0, a1', a2', a3'⟩ := hae
  obtain ⟨b4, b5, b6, b7⟩ := hbe
  refine ⟨a, ha, b, hb2, Equiv.ext fun i => ?_⟩
  have key : ∀ j : Fin 8, j.val < 4 → (a * b) j = a j := fun j hj => by
    show a (b j) = a j
    rw [quad2_fix b hb2 j hj]
  have key' : ∀ j : Fin 8, 4 ≤ j.val → (a * b) j = b j := fun j hj => by
    show a (b j) = b j
    exact quad1_fix a ha (b j) (quad2_maps b hb2 j hj)
  fin_cases i
  · exact (key 0 (by decide)).trans a0 |>.symm
  · exact (key 1 (by decide)).trans a1' |>.symm
  · exact (key 2 (by decide)).trans a2' |>.symm
  · exact (key 3 (by decide)).trans a3' |>.symm
  · exact (key' 4 (by decide)).trans b4 |>.symm
  · exact (key' 5 (by decide)).trans b5 |>.symm
  · exact (key' 6 (by decide)).trans b6 |>.symm
  · exact (key' 7 (by decide)).trans b7 |>.symm

theorem vv_pw4 : PW4 vv := by decide +kernel

theorem complete_W4 {g : S8} (hg : PW4 g) : g ∈ W4list := by
  rcases Nat.lt_or_ge (blk4 (g 0)) 1 with h | h
  · obtain ⟨a, ha, b, hb, rfl⟩ := complete_B4 hg (by omega)
    simp only [W4list, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨a, ha, b, hb, Or.inl rfl⟩
  · have hvg : PW4 (vv * g) := W4.mul_mem vv_pw4 hg
    have h0 : blk4 ((vv * g) 0) = 0 := by
      show blk4 (vv (g 0)) = 0
      rw [blk4_vv]
      have := blk4_lt (g 0)
      omega
    obtain ⟨a, ha, b, hb, e⟩ := complete_B4 hvg h0
    have hg' : g = vv * (a * b) := by
      calc g = (vv * vv) * g := by rw [vv_sq, one_mul]
        _ = vv * (vv * g) := mul_assoc _ _ _
        _ = vv * (a * b) := by rw [e]
    simp only [W4list, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨a, ha, b, hb, Or.inr hg'⟩

@[expose] def compT (u v : List (Fin 8)) : List (Fin 8) := v.map fun j => u.getD j.val 0

@[expose] def idT : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def sqT : ℕ → List (Fin 8) → List (Fin 8)
  | 0, t => t
  | k + 1, t => let s := sqT k t; compT s s

theorem getD_tupleOf (x : S8) (j : Fin 8) : (tupleOf x).getD j.val 0 = x j := by
  fin_cases j <;> rfl

theorem tupleOf_mul (x y : S8) : tupleOf (x * y) = compT (tupleOf x) (tupleOf y) := by
  have h1 : tupleOf (x * y) = (tupleOf y).map (fun j => x j) := rfl
  rw [h1, compT]
  exact List.map_congr_left (fun j _ => (getD_tupleOf x j).symm)

theorem tupleOf_pow_two (k : ℕ) (x : S8) : tupleOf (x ^ 2 ^ k) = sqT k (tupleOf x) := by
  induction k with
  | zero => simp [sqT]
  | succ k ih =>
    have e : x ^ 2 ^ (k + 1) = x ^ 2 ^ k * x ^ 2 ^ k := by
      rw [pow_succ, pow_mul, sq]
    rw [e, tupleOf_mul, ih]
    rfl

theorem sqT_of_pow {x : S8} (h : x ^ 128 = 1) : sqT 7 (tupleOf x) = idT := by
  have := tupleOf_pow_two 7 x
  rw [show (2 : ℕ) ^ 7 = 128 by norm_num, h] at this
  exact this.symm

@[expose] def aGens : List S8 := [a1, a2, a3, a4]

@[expose] def twoChk (x : S8) : Bool :=
  !(sqT 7 (tupleOf x) == idT) ||
    !(aGens.all fun a => sqT 7 (tupleOf (x * a * x⁻¹ * a⁻¹)) == idT) ||
      Elist.any fun e => tupleOf e == tupleOf x

theorem twoChk_spec {x : S8} (h : twoChk x = true) (h2 : sqT 7 (tupleOf x) = idT)
    (hc : ∀ a ∈ aGens, sqT 7 (tupleOf (x * a * x⁻¹ * a⁻¹)) = idT) : x ∈ Elist := by
  simp only [twoChk, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    List.any_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | ⟨e, he, h⟩
  · exact absurd h2 h
  · exfalso
    have hall : (aGens.all fun a => sqT 7 (tupleOf (x * a * x⁻¹ * a⁻¹)) == idT) = true :=
      List.all_eq_true.2 fun a ha => beq_iff_eq.2 (hc a ha)
    rw [hall] at h
    exact Bool.noConfusion h
  · rw [← eq_of_tupleOf_eq h]
    exact he

theorem two_check : (W4list.all twoChk) = true := by decide +kernel

theorem two_element_mem_Elist (x : S8) (hx : PW4 x) (h2 : x ^ 128 = 1)
    (hc : ∀ a ∈ aGens, (x * a * x⁻¹ * a⁻¹) ^ 128 = 1) : x ∈ Elist :=
  twoChk_spec (List.all_eq_true.1 two_check x (complete_W4 hx)) (sqT_of_pow h2)
    fun a ha => sqT_of_pow (hc a ha)

end CFSG.Quasithin.SBd3S8
