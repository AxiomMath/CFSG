module

public import CFSG.Quasithin.Recognition.CertU33Dc
public import CFSG.Quasithin.Recognition.CertPermSimple

public section

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.Sporadic.Bridge CFSG.Monster.B.Co2

@[expose] def u33J : Subgroup (Equiv.Perm (Fin 28)) :=
  Subgroup.closure {g | ∃ k < u33Gens.size, permOfArr 28 u33Gens[k]! = g}

@[expose] def u33SA0 : Equiv.Perm (Fin 28) := wordProd u33GenP (u33W "yBXYxY")

@[expose] def u33SB0 : Equiv.Perm (Fin 28) := wordProd u33GenP (u33W "xAy")

@[expose] def u33SGenWords : List String :=
  ["ABABaBab", "aBabABAB", "aBABBBaB", "bbAbaBA", "baBaBABab"]

@[expose] def u33STWord : String := "x"

@[expose] def u33SHWords : List String :=
  ["", "xYs", "syX", "sBxa", "xY", "XYBX", "ayXy", "syXyX", "aYxB", "s", "bXyA", "yX", "ysx",
    "xYxY", "yXyX", "sxY", "bxYAX", "Bxa", "aXyXyAX", "axyx", "xYsxY", "ysXY", "AXb", "YAy",
    "sAXb", "Yay", "aYAXY"]

@[expose] def u33SAL : List Nat := u33WordL (u33W "yBXYxY")

@[expose] def u33SBL : List Nat := u33WordL (u33W "xAy")

@[expose] def u33SAiL : List Nat := u33WordL (u33InvW (u33W "yBXYxY"))

@[expose] def u33SBiL : List Nat := u33WordL (u33InvW (u33W "xAy"))

@[expose] def u33SWL (w : List (ℕ × Bool)) : List Nat :=
  w.foldr (fun l acc => compL (if l.2 then (if l.1 = 0 then u33SAL else u33SBL)
    else (if l.1 = 0 then u33SAiL else u33SBiL)) acc) (List.range 28)

theorem u33S_letters : (∀ l ∈ u33W "yBXYxY", l.1 < 5) ∧ (∀ l ∈ u33W "xAy", l.1 < 5) := by
  decide +kernel

theorem u33S_rep_a
    : RepL u33SAL u33SA0 := u33_wordL_rep _ u33S_letters.1

theorem u33S_rep_b
    : RepL u33SBL u33SB0 := u33_wordL_rep _ u33S_letters.2

theorem u33S_rep_ai : RepL u33SAiL u33SA0⁻¹ := by
  have h := u33_wordL_rep (u33InvW (u33W "yBXYxY")) (by
    intro l hl
    simp only [u33InvW, List.mem_map, List.mem_reverse] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact u33S_letters.1 l' hl')
  rwa [wordProd_invW] at h

theorem u33S_rep_bi : RepL u33SBiL u33SB0⁻¹ := by
  have h := u33_wordL_rep (u33InvW (u33W "xAy")) (by
    intro l hl
    simp only [u33InvW, List.mem_map, List.mem_reverse] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact u33S_letters.2 l' hl')
  rwa [wordProd_invW] at h

theorem u33S_rep_word
    (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 2) :
    RepL (u33SWL w) (wordProd (fun i => if i = 0 then u33SA0 else u33SB0) w) := by
  induction w with
  | nil => exact repL_one 28
  | cons l w ih =>
    simp only [u33SWL, List.foldr_cons, wordProd, List.map_cons, List.prod_cons] at ih ⊢
    have hl : l.1 < 2 := hw l List.mem_cons_self
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    rcases l with ⟨i, b⟩
    have hi : i = 0 ∨ i = 1 := by
      have h2 : i < 2 := hl
      omega
    rcases hi with rfl | rfl <;> cases b
    · exact repL_mul u33S_rep_ai ih'
    · exact repL_mul u33S_rep_a ih'
    · exact repL_mul u33S_rep_bi ih'
    · exact repL_mul u33S_rep_b ih'

theorem u33S_orders_L :
    (compL u33SAL u33SAL ≠ List.range 28 ∧
      (List.replicate 4 u33SAL).foldr compL (List.range 28) = List.range 28) ∧
    (u33SBL ≠ List.range 28 ∧ (List.replicate 7 u33SBL).foldr compL (List.range 28) = List.range 28) ∧
    (compL u33SAL u33SBL ≠ List.range 28 ∧
      (List.replicate 7 (compL u33SAL u33SBL)).foldr compL (List.range 28) = List.range 28) := by
  decide +kernel

theorem u33S_orders :
    (u33SA0 ^ 2 ≠ 1 ∧ u33SA0 ^ 4 = 1) ∧ (u33SB0 ≠ 1 ∧ u33SB0 ^ 7 = 1) ∧
      (u33SA0 * u33SB0 ≠ 1 ∧ (u33SA0 * u33SB0) ^ 7 = 1) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := u33S_orders_L
  have ha := u33S_rep_a
  have hb := u33S_rep_b
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [pow_two]
    exact ne_of_repL_ne (repL_mul ha ha) (repL_one 28) a1
  · have := repL_pow ha 4
    rw [a2] at this
    exact eq_of_repL this (repL_one 28)
  · exact ne_of_repL_ne hb (repL_one 28) b1
  · have := repL_pow hb 7
    rw [b2] at this
    exact eq_of_repL this (repL_one 28)
  · exact ne_of_repL_ne (repL_mul ha hb) (repL_one 28) c1
  · have := repL_pow (repL_mul ha hb) 7
    rw [c2] at this
    exact eq_of_repL this (repL_one 28)

theorem u33S_genwords_letters : ∀ k < 5, ∀ l ∈ u33W (u33SGenWords.getD k ""), l.1 < 2 := by
  decide +kernel

theorem u33S_genwords_L : ∀ k < 5,
    u33SWL (u33W (u33SGenWords.getD k "")) = u33GenTab.getD k [] := by
  decide +kernel

theorem u33S_genwords : ∀ k : Fin 5,
    wordProd (fun i => if i = 0 then u33SA0 else u33SB0) (u33W (u33SGenWords.getD k "")) =
      u33GenP k := by
  intro k
  have h := u33S_rep_word _ (u33S_genwords_letters k k.2)
  rw [u33S_genwords_L k k.2] at h
  exact eq_of_repL h (u33_genTab_rep k k.2)

theorem u33S_trans_letters : (∀ l ∈ u33W u33STWord, l.1 < 5) ∧
    ∀ p < 27, ∀ l ∈ u33W (u33SHWords.getD p ""), l.1 < 5 := by
  decide +kernel

theorem u33S_trans_L :
    (u33WordL (u33W u33STWord)).getD 0 0 = 1 ∧
      ∀ p < 27, (u33WordL (u33W (u33SHWords.getD p ""))).getD 0 0 = 0 ∧
        (u33WordL (u33W (u33SHWords.getD p ""))).getD 1 0 = p + 1 := by
  decide +kernel

theorem u33S_trans :
    ((wordProd u33GenP (u33W u33STWord)) 0).val = 1 ∧
      ∀ p < 27, ((wordProd u33GenP (u33W (u33SHWords.getD p ""))) 0).val = 0 ∧
        ((wordProd u33GenP (u33W (u33SHWords.getD p ""))) 1).val = p + 1 := by
  obtain ⟨h1, h2⟩ := u33S_trans_L
  obtain ⟨l1, l2⟩ := u33S_trans_letters
  refine ⟨?_, fun p hp => ?_⟩
  · exact ((u33_wordL_rep _ l1).2 0).symm.trans h1
  · obtain ⟨h3, h4⟩ := h2 p hp
    have hr := u33_wordL_rep _ (l2 p hp)
    refine ⟨?_, ?_⟩
    · exact (hr.2 0).symm.trans h3
    · exact (hr.2 1).symm.trans h4

theorem u33GenP_mem (i : ℕ) : u33GenP i ∈ u33J := by
  unfold u33GenP
  split_ifs with h
  · obtain ⟨hsz, -⟩ := u33Chain_check
    exact Subgroup.subset_closure ⟨i, by rw [hsz]; exact h, permOfArr_u33Gens ⟨i, h⟩⟩
  · exact Subgroup.one_mem _

@[expose] def u33SElt (w : List (ℕ × Bool)) : ↥u33J :=
  ⟨wordProd u33GenP w, wordProd_mem u33GenP_mem w⟩

theorem card_u33J : Nat.card ↥u33J = 6048 := card_u33Perm

theorem closure_a0_b0
    : Subgroup.closure ({u33SA0, u33SB0} : Set (Equiv.Perm (Fin 28))) = u33J := by
  have ha0 : u33SA0 ∈ u33J := wordProd_mem u33GenP_mem _
  have hb0 : u33SB0 ∈ u33J := wordProd_mem u33GenP_mem _
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl)
    · exact ha0
    · exact hb0
  · unfold u33J
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, hk, rfl⟩
    obtain ⟨hsz, -⟩ := u33Chain_check
    rw [hsz] at hk
    have hg : permOfArr 28 u33Gens[k]! = u33GenP k := by
      rw [show u33GenP k = u33Img ⟨k, hk⟩ by simp [u33GenP, hk]]
      exact permOfArr_u33Gens ⟨k, hk⟩
    rw [hg, SetLike.mem_coe, ← u33S_genwords ⟨k, hk⟩]
    refine wordProd_mem (K := Subgroup.closure ({u33SA0, u33SB0} : Set (Equiv.Perm (Fin 28))))
      (x := fun i => if i = 0 then u33SA0 else u33SB0) (fun i => ?_) _
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem exists_stab
    (p : Fin 28) (hp : p ≠ 0) :
    ∃ h : ↥u33J, h • (0 : Fin 28) = 0 ∧ h • (1 : Fin 28) = p := by
  have hp1 : 1 ≤ p.val := by
    rcases Nat.eq_zero_or_pos p.val with h | h
    · exact absurd (Fin.ext h) hp
    · exact h
  obtain ⟨-, htr⟩ := u33S_trans
  obtain ⟨h0, h1⟩ := htr (p.val - 1) (by omega)
  refine ⟨u33SElt (u33W (u33SHWords.getD (p.val - 1) "")), Fin.ext ?_, Fin.ext ?_⟩
  · exact h0
  · rw [show p.val = (p.val - 1) + 1 by omega]
    exact h1

theorem exists_zero_one :
    ∃ t : ↥u33J, t • (0 : Fin 28) = 1 := by
  obtain ⟨ht, -⟩ := u33S_trans
  exact ⟨u33SElt (u33W u33STWord), Fin.ext ht⟩

theorem u33J_pretransitive
    : MulAction.IsPretransitive ↥u33J (Fin 28) := by
  obtain ⟨t, ht⟩ := exists_zero_one
  have key : ∀ p : Fin 28, ∃ g : ↥u33J, g • (0 : Fin 28) = p := by
    intro p
    by_cases hp : p = 0
    · exact ⟨1, by rw [hp]; exact one_smul _ _⟩
    · obtain ⟨h, -, h1⟩ := exists_stab p hp
      exact ⟨h * t, by rw [mul_smul, ht, h1]⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := key p
  obtain ⟨g', hg'⟩ := key q
  refine ⟨g' * g⁻¹, ?_⟩
  rw [mul_smul, inv_smul_eq_iff.2 hg.symm, hg']

theorem u33J_preprimitive
    : MulAction.IsPreprimitive ↥u33J (Fin 28) := by
  have := u33J_pretransitive
  refine isPreprimitive_of_suborbit_labels' (G := ↥u33J) (X := Fin 28) (0 : Fin 28)
    (MulAction.stabilizer ↥u33J (0 : Fin 28)) (fun h hh => hh) (k := 2)
    (fun p => if p = 0 then (0 : Fin 2) else 1) ?_ ?_
  · intro p q hpq
    by_cases hp : p = 0
    · have hq : q = 0 := by
        by_contra hq
        rw [ite_eq_left hp, ite_eq_right hq] at hpq
        exact absurd hpq (by decide)
      exact ⟨1, one_mem _, by rw [hp, hq]; exact one_smul _ _⟩
    · have hq : q ≠ 0 := by
        intro hq
        rw [ite_eq_right hp, ite_eq_left hq] at hpq
        exact absurd hpq (by decide)
      obtain ⟨h, hh0, hh1⟩ := exists_stab p hp
      obtain ⟨h', hh0', hh1'⟩ := exists_stab q hq
      refine ⟨h' * h⁻¹, ?_, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff.2 hh0.symm, hh0']
      · rw [mul_smul, inv_smul_eq_iff.2 hh1.symm, hh1']
  · intro S hx hdvd
    revert S
    decide +kernel

theorem isSimpleGroup_u33J :
    IsSimpleGroup ↥u33J := by
  have := u33J_pretransitive
  have := u33J_preprimitive
  obtain ⟨⟨ha2, ha4⟩, ⟨hb1, hb7⟩, ⟨hab1, hab7⟩⟩ := u33S_orders
  have ha0 : u33SA0 ∈ u33J := wordProd_mem u33GenP_mem _
  have hb0 : u33SB0 ∈ u33J := wordProd_mem u33GenP_mem _
  set a : ↥u33J := ⟨u33SA0, ha0⟩ with ha
  set b : ↥u33J := ⟨u33SB0, hb0⟩ with hb
  have hoa : orderOf a = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using ha2) (by simpa using ha4)
  have hob : orderOf b = 7 := by
    rw [← Subgroup.orderOf_coe]
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hb7 hb1
  have hoab : orderOf (a * b) = 7 := by
    rw [← Subgroup.orderOf_coe]
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hab7 hab1
  have hgen : Subgroup.closure ({a, b} : Set ↥u33J) = ⊤ := by
    apply Subgroup.map_injective u33J.subtype_injective
    rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top, Subgroup.range_subtype]
    exact closure_a0_b0
  have hstab : Nat.card (MulAction.stabilizer ↥u33J (0 : Fin 28)) = 216 := by
    have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥u33J (0 : Fin 28))
    rw [Nat.card_prod, MulAction.orbit_eq_univ, Nat.card_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, card_u33J] at h1
    omega
  exact CFSG.GroupActions.isSimpleGroup_of_preprimitive_of_coprime_generator_orders (G := ↥u33J) (Ω := Fin 28)
    (by simp) a b hgen 0 (by rw [hoa, hob]; norm_num) (by rw [hoab, hstab]; norm_num)

theorem isSimpleGroup_u33Pres
    : IsSimpleGroup (PG 5 u33PresRels) := by
  obtain ⟨e⟩ := u33Pres_mulEquiv_perm
  have : IsSimpleGroup ↥(Subgroup.closure {g | ∃ k < u33Gens.size, permOfArr 28 u33Gens[k]! = g}) :=
    isSimpleGroup_u33J
  exact e.isSimpleGroup

end CFSG.Quasithin
