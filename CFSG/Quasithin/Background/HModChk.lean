module

public import CFSG.Quasithin.Background.HMathieuMask

public section

namespace CFSG.Quasithin.H.ModChk

open CFSG.Quasithin.H.Mathieu

@[expose] def idArr : Array ℕ := (List.range 24).toArray

@[expose] def cArr (a b : Array ℕ) : Array ℕ := ((List.range 24).map fun i => a[b[i]!]!).toArray

theorem idArr_get {i : ℕ} (hi : i < 24) : idArr[i]! = i := by
  rw [idArr, getElem!_pos _ i (by simpa using hi)]
  simp

theorem cArr_get (a b : Array ℕ) {i : ℕ} (hi : i < 24) : (cArr a b)[i]! = a[b[i]!]! := by
  rw [cArr, getElem!_pos _ i (by simpa using hi)]
  simp

theorem hasArr_one : HasArr (1 : Equiv.Perm (Fin 24)) idArr := fun i => by
  rw [idArr_get i.2]
  rfl

theorem hasArr_mul {σ τ : Equiv.Perm (Fin 24)} {a b : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ b) : HasArr (σ * τ) (cArr a b) := fun i => by
  rw [cArr_get a b i.2, Equiv.Perm.mul_apply, hσ, hτ]

theorem perm_eq_of_hasArr {σ τ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ a) : σ = τ :=
  Equiv.ext fun i => Fin.ext ((hσ i).trans (hτ i).symm)

@[expose] def wArr (gs : List (Array ℕ)) : List ℕ → Array ℕ
  | [] => idArr
  | i :: w => cArr (gs.getD i idArr) (wArr gs w)

@[expose] def wPerm (ps : List (Equiv.Perm (Fin 24))) : List ℕ → Equiv.Perm (Fin 24)
  | [] => 1
  | i :: w => ps.getD i 1 * wPerm ps w

theorem hasArr_wPerm {ps : List (Equiv.Perm (Fin 24))} {gs : List (Array ℕ)}
    (h : ∀ i, HasArr (ps.getD i 1) (gs.getD i idArr)) :
    ∀ w, HasArr (wPerm ps w) (wArr gs w)
  | [] => hasArr_one
  | i :: w => hasArr_mul (h i) (hasArr_wPerm h w)

theorem hasArr_getD {ps : List (Equiv.Perm (Fin 24))} {gs : List (Array ℕ)}
    (hlen : ps.length = gs.length) (h : ∀ i (hi : i < ps.length),
      HasArr (ps.get ⟨i, hi⟩) (gs.get ⟨i, hlen ▸ hi⟩)) :
    ∀ i, HasArr (ps.getD i 1) (gs.getD i idArr) := by
  intro i
  by_cases hi : i < ps.length
  · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (hlen ▸ hi)]
    exact h i hi
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    exact hasArr_one

theorem wPerm_mem {ps : List (Equiv.Perm (Fin 24))} {K : Subgroup (Equiv.Perm (Fin 24))}
    (h : ∀ p ∈ ps, p ∈ K) : ∀ w, wPerm ps w ∈ K
  | [] => K.one_mem
  | i :: w => by
    refine K.mul_mem ?_ (wPerm_mem h w)
    by_cases hi : i < ps.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact K.one_mem

theorem map_wPerm {G : Type*} [Group G] (f : Equiv.Perm (Fin 24) →* G)
    (ps : List (Equiv.Perm (Fin 24))) : ∀ w,
    f (wPerm ps w) = (w.map fun i => f (ps.getD i 1)).prod
  | [] => map_one f
  | i :: w => by rw [wPerm, map_mul, map_wPerm f ps w, List.map_cons, List.prod_cons]

@[expose] def nodupB : List ℕ → ℕ → Bool
  | [], _ => true
  | m :: l, b => !b.testBit m && nodupB l (b ||| 1 <<< m)

theorem nodup_of_nodupB : ∀ (l : List ℕ) (b : ℕ), nodupB l b = true →
    l.Nodup ∧ ∀ m ∈ l, b.testBit m = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => by simp at h⟩
  | m :: l, b, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨hm, hl⟩ := nodup_of_nodupB l _ h.2
    have hmb : (b ||| 1 <<< m).testBit m = true := by
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.or_true]
    refine ⟨List.nodup_cons.2 ⟨fun hml => ?_, hm⟩, fun m' hm' => ?_⟩
    · have := hl m hml
      rw [hmb] at this
      exact Bool.noConfusion this
    · rcases List.mem_cons.1 hm' with rfl | hm'
      · exact h.1
      · have h2 := hl m' hm'
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at h2
        exact h2.1

@[expose] def treeB (act : ℕ → ℕ → ℕ) : List (ℕ × ℕ × ℕ) → ℕ → Bool
  | [], _ => true
  | (m, p, g) :: l, seen =>
    seen.testBit p && !seen.testBit m && m == act g p && treeB act l (seen ||| 1 <<< m)

theorem treeB_spec (act : ℕ → ℕ → ℕ) (P : ℕ → Prop) (hP : ∀ g m, P m → P (act g m)) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (seen : ℕ), (∀ m, seen.testBit m = true → P m) →
      treeB act l seen = true →
      (∀ e ∈ l, P e.1) ∧ (l.map Prod.fst).Nodup ∧ ∀ e ∈ l, seen.testBit e.1 = false
  | [], _, _, _ => ⟨fun _ h => by simp at h, List.nodup_nil, fun _ h => by simp at h⟩
  | (m, p, g) :: l, seen, hs, h => by
    simp only [treeB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hp, hm⟩, hmeq⟩, hl⟩ := h
    have hPm : P m := hmeq ▸ hP g p (hs p hp)
    have hs' : ∀ m', (seen ||| 1 <<< m).testBit m' = true → P m' := by
      intro m' hm'
      rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at hm'
      rcases hm' with hm' | hm'
      · exact hs m' hm'
      · rw [← of_decide_eq_true hm']
        exact hPm
    obtain ⟨h1, h2, h3⟩ := treeB_spec act P hP l _ hs' hl
    have hmb : (seen ||| 1 <<< m).testBit m = true := by
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.or_true]
    refine ⟨fun e he => ?_, ?_, fun e he => ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact hPm
      · exact h1 e he
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hml => ?_, h2⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hml
      have := h3 e he
      rw [hmb] at this
      exact Bool.noConfusion this
    · rcases List.mem_cons.1 he with rfl | he
      · exact hm
      · have h4 := h3 e he
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at h4
        exact h4.1

@[expose] def derivB (act : ℕ → ℕ → ℕ) (start : List ℕ) : List (ℕ × ℕ) → List ℕ
  | [] => start
  | (g, i) :: D => derivB act (start ++ [act g (start.getD i 0)]) D

theorem mem_of_derivB (act : ℕ → ℕ → ℕ) (P : ℕ → Prop) (hP : ∀ g m, P m → P (act g m))
    (h0 : P 0) : ∀ (D : List (ℕ × ℕ)) (start : List ℕ), (∀ m ∈ start, P m) →
      ∀ m ∈ derivB act start D, P m
  | [], start, hs => hs
  | (g, i) :: D, start, hs => by
    refine mem_of_derivB act P hP h0 D _ fun m hm => ?_
    rcases List.mem_append.1 hm with hm | hm
    · exact hs m hm
    · rw [List.mem_singleton] at hm
      rw [hm]
      refine hP g _ ?_
      by_cases hi : i < start.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hs _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact h0

theorem mem_of_combos (P : ℕ → Prop) (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b)) :
    ∀ (l : List ℕ), (∀ a ∈ l, P a) → ∀ m ∈ combos l, P m
  | [], _, m, hm => by
    simp only [combos, List.mem_singleton] at hm
    rw [hm]
    exact h0
  | a :: l, h, m, hm => by
    rw [combos, List.mem_append, List.mem_map] at hm
    have hl := mem_of_combos P h0 hx l fun b hb => h b (List.mem_cons_of_mem a hb)
    rcases hm with hm | ⟨y, hy, rfl⟩
    · exact hl m hm
    · exact hx _ _ (hl y hy) (h a List.mem_cons_self)

theorem zero_mem_combos : ∀ l : List ℕ, 0 ∈ combos l
  | [] => List.mem_singleton.2 rfl
  | _ :: l => List.mem_append_left _ (zero_mem_combos l)

theorem xor_mem_combos : ∀ (l : List ℕ) {a b : ℕ}, a ∈ combos l → b ∈ combos l →
    a ^^^ b ∈ combos l
  | [], a, b, ha, hb => by
    simp only [combos, List.mem_singleton] at ha hb ⊢
    rw [ha, hb, Nat.xor_self]
  | x :: l, a, b, ha, hb => by
    rw [combos, List.mem_append, List.mem_map] at ha hb ⊢
    rcases ha with ha | ⟨a', ha', rfl⟩ <;> rcases hb with hb | ⟨b', hb', rfl⟩
    · exact Or.inl (xor_mem_combos l ha hb)
    · exact Or.inr ⟨a ^^^ b', xor_mem_combos l ha hb', by rw [Nat.xor_assoc]⟩
    · exact Or.inr ⟨a' ^^^ b, xor_mem_combos l ha' hb, by
        rw [Nat.xor_assoc, Nat.xor_comm b x, ← Nat.xor_assoc]⟩
    · left
      have h := xor_mem_combos l ha' hb'
      have e : a' ^^^ x ^^^ (b' ^^^ x) = a' ^^^ b' := by
        rw [Nat.xor_assoc, Nat.xor_comm b' x, ← Nat.xor_assoc x x b', Nat.xor_self,
          Nat.zero_xor]
      rw [e]
      exact h

theorem actM_mem_combos {l : List ℕ} : ∀ {cs : List ℕ}, (∀ c ∈ cs, c ∈ combos l) →
    ∀ m, actM cs m ∈ combos l
  | [], _, _ => zero_mem_combos l
  | c :: cs, h, m => by
    rw [actM]
    refine xor_mem_combos l ?_ (actM_mem_combos (fun d hd => h d (List.mem_cons_of_mem c hd)) _)
    split_ifs
    · exact h c List.mem_cons_self
    · exact zero_mem_combos l

theorem mem_combos_of_xorLin {f : ℕ → ℕ} (hf : XorLin f) {l : List ℕ} {n : ℕ}
    (h : ∀ j < n, f (2 ^ j) ∈ combos l) : ∀ m < 2 ^ n, f m ∈ combos l := by
  intro m hm
  rw [← actM_matOf hf n m hm]
  refine actM_mem_combos (fun c hc => ?_) m
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
  exact h j (List.mem_range.1 hj)

@[expose] def maskSub (n : ℕ) (l : List ℕ) : Subgroup (Wn n) where
  carrier := {v | ∃ m ∈ combos l, toW n m = v}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ^^^ b, xor_mem_combos l ha hb, toW_xor n a b⟩
  one_mem' := ⟨0, zero_mem_combos l, toW_zero n⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ha, (inv_eq_of_mul_eq_one_right ?_).symm⟩
    have h := toW_xor n a a
    rw [Nat.xor_self, toW_zero] at h
    exact h.symm

theorem mem_maskSub {n : ℕ} {l : List ℕ} {v : Wn n} :
    v ∈ maskSub n l ↔ ∃ m ∈ combos l, toW n m = v := Iff.rfl

theorem toW_mem_maskSub {n : ℕ} {l : List ℕ} {m : ℕ} (hm : m ∈ combos l) :
    toW n m ∈ maskSub n l := ⟨m, hm, rfl⟩

theorem card_maskSub {n : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a < 2 ^ n) (hnd : (combos l).Nodup) :
    Nat.card (maskSub n l) = 2 ^ l.length := by
  classical
  have hlt := combos_lt hl
  have hinj : ((combos l).map (toW n)).Nodup :=
    hnd.map_on fun a ha b hb hab => toW_inj (hlt a ha) (hlt b hb) hab
  have hset : ((maskSub n l : Subgroup (Wn n)) : Set (Wn n)) =
      (((combos l).map (toW n)).toFinset : Set (Wn n)) := by
    ext v
    simp only [SetLike.mem_coe, mem_maskSub, List.coe_toFinset, List.mem_map, Set.mem_ofPred_eq]
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hinj, List.length_map, length_combos]

end CFSG.Quasithin.H.ModChk
