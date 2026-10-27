module

public import CFSG.Quasithin.Background.F918W1

public section

namespace CFSG.Quasithin.D35ValChk

attribute [local irreducible] btab gdata ptab ctab rtab

theorem listEqN_iff (l l' : List Nat) : listEqN l l' = true ↔ l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp [listEqN]
  | cons a as ih => cases l' <;> simp [listEqN, ih, Nat.beq_eq]

theorem listEqP_iff (l l' : List (Nat × Nat)) : listEqP l l' = true ↔ l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp [listEqP]
  | cons a as ih => cases l' <;> simp [listEqP, ih, Nat.beq_eq, Prod.ext_iff, and_assoc]

theorem listEqT_iff (l l' : List (Nat × Nat × Nat)) : listEqT l l' = true ↔ l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp [listEqT]
  | cons a as ih => cases l' <;> simp [listEqT, ih, Nat.beq_eq, Prod.ext_iff, and_assoc]

private theorem testBit_eq_mod (a k : Nat) : a.testBit k = decide ((a >>> k) % 2 = 1) := by
  rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]

private theorem bit_eq_ite (a k : Nat) : bit a k = if a.testBit k then 1 else 0 := by
  simp only [bit, Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, testBit_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one (a >>> k) with h | h <;> simp [h]

private theorem bitSet_eq (s e : Nat) : bitSet s e = s.testBit e := by
  have h : bitSet s e = Nat.beq (bit s e) 1 := rfl
  rw [h, bit_eq_ite]
  cases s.testBit e <;> rfl

private theorem testBit_shiftLeft_one (n k : Nat) : (Nat.shiftLeft 1 n).testBit k = decide (n = k) := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

private theorem bitSet_lor_shl (s e x : Nat) :
    bitSet (Nat.lor s (Nat.shiftLeft 1 e)) x = (bitSet s x || Nat.beq x e) := by
  have h : Nat.beq x e = decide (e = x) := by
    rw [Bool.eq_iff_iff]
    simp only [Nat.beq_eq, decide_eq_true_eq]
    exact eq_comm
  rw [h]
  simp only [bitSet_eq, Nat.lor_eq, Nat.testBit_or, testBit_shiftLeft_one]

private def GInv (vis : Nat) (L : List Nat) : Prop :=
  (∀ x, bitSet vis x = true ↔ x ∈ L) ∧ L.Nodup ∧ ∀ x ∈ L, InClos x ∧ x < 262144

private theorem goG_inv : ∀ (data : List (Nat × Nat × Nat)) (vis : Nat) (L : List Nat) (vis' : Nat),
    GInv vis L → goG vis data = some vis' → GInv vis' (L ++ data.map fun e => e.1)
  | [], vis, L, vis', hI, h => by
    simp only [goG, Option.some.injEq] at h
    subst h
    simpa using hI
  | e :: rest, vis, L, vis', hI, h => by
    simp only [goG] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.beq_eq] at hc
      obtain ⟨⟨⟨⟨hp, hn⟩, hlt⟩, hi⟩, hk⟩ := hc
      have hnL : e.1 ∉ L := fun hm => by
        have := (hI.1 e.1).mpr hm
        rw [hn] at this
        exact Bool.false_ne_true this
      have hpL : e.2.1 ∈ L := (hI.1 _).mp hp
      have hI' : GInv (Nat.lor vis (Nat.shiftLeft 1 e.1)) (L ++ [e.1]) := by
        refine ⟨fun x => ?_, ?_, ?_⟩
        · rw [bitSet_lor_shl, Bool.or_eq_true, hI.1 x, Nat.beq_eq, List.mem_append, List.mem_singleton]
        · rw [List.nodup_append]
          refine ⟨hI.2.1, List.nodup_singleton _, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          exact fun hab => hnL (hab ▸ ha)
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hI.2.2 x hx
          · rw [List.mem_singleton] at hx
            subst hx
            refine ⟨?_, hlt⟩
            rw [← hk]
            exact InClos.mul _ hi (hI.2.2 _ hpL).1
      have := goG_inv rest _ (L ++ [e.1]) vis' hI' h
      simpa [List.append_assoc] using this
    · simp at h

private theorem chkG_facts (h : chkG = true) :
    (∀ x, bitSet glMask x = true ↔ x ∈ gl) ∧ gl.Nodup ∧ (∀ g ∈ gl, InClos g ∧ g < 262144) ∧
      gl.length = 1080 ∧ bitSet glMask u0 = true ∧ bitSet glMask a0 = true ∧ bitSet glMask b0 = true ∧
      ∀ g ∈ gl, ∀ i, i < 3 → bitSet glMask (kmul g (genK i)) = true := by
  unfold chkG at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hs, hlen⟩, hu⟩, ha⟩, hb⟩, hcl⟩ := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  have hmask : glMask = v := by
    unfold glMask
    rw [hv]
    rfl
  rw [hmask] at hu ha hb hcl
  have hbase : GInv (Nat.shiftLeft 1 kid) [kid] := by
    refine ⟨fun x => ?_, List.nodup_singleton _, ?_⟩
    · rw [bitSet_eq, testBit_shiftLeft_one, List.mem_singleton, decide_eq_true_iff, eq_comm]
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨InClos.one, by decide⟩
  have hI := goG_inv gdata _ [kid] v hbase hv
  have hgl : gl = [kid] ++ gdata.map (fun e => e.1) := rfl
  rw [hmask]
  refine ⟨?_, ?_, ?_, ?_, hu, ha, hb, ?_⟩
  · rw [hgl]
    exact hI.1
  · rw [hgl]
    exact hI.2.1
  · rw [hgl]
    exact hI.2.2
  · exact Nat.eq_of_beq_eq_true hlen
  · intro g hg i hi
    have := (List.all_eq_true.mp hcl) g hg
    have h3 := (List.all_eq_true.mp this) i (by simp; omega)
    exact h3

private theorem beq_eq_false_iff (a b : Nat) : Nat.beq a b = false ↔ a ≠ b := by
  rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]

theorem mem_invList {g : Nat} : g ∈ invList ↔ g ∈ gl ∧ g ≠ kid ∧ kmul g g = kid := by
  unfold invList
  rw [List.mem_filter]
  simp [Nat.beq_eq, beq_eq_false_iff]

theorem classPres_iff {x y : Nat} :
    classPres x y = true ↔ ∃ p ∈ offPairs, memF p.1 p.2 x = true ∧ memF p.1 p.2 y = true := by
  unfold classPres offTriples
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact ⟨p, hp, by simpa [Bool.and_eq_true, memT, memF] using h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨_, List.mem_map_of_mem hp, by simpa [Bool.and_eq_true, memT, memF] using h⟩

theorem mem_offPairs {a b : Nat} : (a, b) ∈ offPairs ↔
    a ∈ invList ∧ b ∈ invList ∧ a ≠ b ∧ comm a b = true ∧ 16 ≤ popc (Nat.land (fixMask a) (fixMask b)) := by
  unfold offPairs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨a', ha', hm⟩
    obtain ⟨b', hb', hab⟩ := List.mem_map.mp hm
    rw [List.mem_filter] at hb'
    obtain ⟨hbI, hc⟩ := hb'
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.ble_eq] at hc
    exact ⟨ha', hbI, (beq_eq_false_iff _ _).mp hc.1.1, hc.1.2, hc.2⟩
  · rintro ⟨ha, hb, hab, hc, h16⟩
    refine ⟨a, ha, List.mem_map.mpr ⟨b, ?_, rfl⟩⟩
    rw [List.mem_filter]
    refine ⟨hb, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.ble_eq]
    exact ⟨⟨(beq_eq_false_iff _ _).mpr hab, hc⟩, h16⟩

private theorem mem_neigh {x1 x : Nat} : x ∈ neigh x1 ↔ x ∈ invList ∧ x ≠ x1 ∧ rel12 x1 x = true := by
  unfold neigh
  rw [List.mem_filter]
  simp [beq_eq_false_iff]

private theorem mem_tripleList {x1 x2 x3 : Nat} : (x1, x2, x3) ∈ tripleList ↔
    x1 ∈ invList ∧ (x2 ∈ invList ∧ x2 ≠ x1 ∧ rel12 x1 x2 = true) ∧ (x3 ∈ invList ∧ x3 ≠ x1 ∧ rel12 x1 x3 = true) ∧
      x3 ≠ x2 ∧ rel23 x2 x3 = true ∧ rel123 x1 x2 x3 = true := by
  unfold tripleList
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, mem_neigh, Prod.mk.injEq, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff]
  constructor
  · rintro ⟨a, ha, b, hb, c, ⟨hc, hc1, hc2⟩, h1, h2, h3⟩
    subst h1 h2 h3
    exact ⟨ha, hb, hc, hc1.1, hc1.2, hc2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨x1, h1, x2, h2, x3, ⟨h3, ⟨h4, h5⟩, h6⟩, rfl, rfl, rfl⟩

theorem mem_presList {x1 x2 x3 : Nat} : (x1, x2, x3) ∈ presList ↔
    x1 ∈ invList ∧ (x2 ∈ invList ∧ x2 ≠ x1 ∧ rel12 x1 x2 = true) ∧ (x3 ∈ invList ∧ x3 ≠ x1 ∧ rel12 x1 x3 = true) ∧
      x3 ≠ x2 ∧ rel23 x2 x3 = true ∧ rel123 x1 x2 x3 = true ∧
      classPres x2 (kmul (kmul x3 x2) x3) = true := by
  unfold presList
  rw [List.mem_filter, mem_tripleList]
  simp only [and_assoc]

private theorem genK_cases (i : Nat) : genK i = u0 ∨ genK i = a0 ∨ genK i = b0 := by
  unfold genK
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem run_facts (h : run = true) : D35Facts := by
  unfold run at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hB, hP⟩, hG⟩, hZ⟩, hO1⟩, hO2⟩, hC⟩, hR⟩ := h
  obtain ⟨hmem, hnodup, hlt, hlen, hu, ha, hb, hcl⟩ := chkG_facts hG
  refine
    { conj_u0 := ?_, pair_bij := ?_, gl_mem := ?_, gl_nodup := hnodup, gl_length := hlen,
      gl_lt := fun g hg => (hlt g hg).2, gl_closed := ?_, gl_gen := fun g hg => (hlt g hg).1, scal_mem := ?_,
      scal_central := ?_, center_scal := ?_, inv_fix := ?_, no_rank3 := ?_, off_ref := ?_, off_conj := ?_,
      triple_bij := ?_ }
  · unfold chkB at hB
    simp only [Bool.and_eq_true] at hB
    obtain ⟨hl, hall⟩ := hB
    intro x hx
    have hx' : x ∈ btab.map fun e => e.1 := (listEqN_iff _ _).mp hl ▸ hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx'
    have := List.all_eq_true.mp hall e he
    unfold entryB at this
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    exact ⟨e.2.1, e.2.2, h1, h2, h3, h4⟩
  ·
    unfold chkP at hP
    simp only [Bool.and_eq_true] at hP
    obtain ⟨hl, hall⟩ := hP
    intro x2 hx2 x3 hx3 h2u h3u h23 hs2 hs3 h4 h5
    have hs2' : x2 ∈ sList := by
      unfold sList
      rw [List.mem_filter]
      refine ⟨hx2, ?_⟩
      simp [(beq_eq_false_iff _ _).mpr h2u, hs2]
    have hs3' : x3 ∈ sList := by
      unfold sList
      rw [List.mem_filter]
      refine ⟨hx3, ?_⟩
      simp [(beq_eq_false_iff _ _).mpr h3u, hs3]
    have hmem' : (x2, x3) ∈ pairList := by
      unfold pairList
      rw [List.mem_flatMap]
      refine ⟨x2, hs2', List.mem_map.mpr ⟨x3, ?_, rfl⟩⟩
      rw [List.mem_filter]
      refine ⟨hs3', ?_⟩
      unfold condP
      simp [(beq_eq_false_iff _ _).mpr h23, h4, h5]
    rw [(listEqP_iff _ _).mp hl] at hmem'
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hmem'
    simp only [Prod.mk.injEq] at hee
    obtain ⟨rfl, rfl⟩ := hee
    have := List.all_eq_true.mp hall e he
    unfold entryP at this
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
    have h36 : (2 : Nat) ^ 36 = 68719476736 := by norm_num
    exact ⟨e.2.2.1, e.2.2.2.1, e.2.2.2.2, h1, by omega, by omega, h4, h5, h6, h7⟩
  ·
    exact ⟨List.mem_cons_self, (hmem _).mp hu, (hmem _).mp ha, (hmem _).mp hb⟩
  ·
    intro g hg i hi
    exact (hmem _).mp (hcl g hg i hi)
  ·
    unfold chkZ at hZ
    simp only [Bool.and_eq_true] at hZ
    obtain ⟨⟨⟨⟨hk0, hk1⟩, hk2⟩, hcomm⟩, hcen⟩ := hZ
    exact ⟨(hmem _).mp hk1, (hmem _).mp hk2⟩
  ·
    unfold chkZ at hZ
    simp only [Bool.and_eq_true] at hZ
    obtain ⟨⟨⟨⟨hk0, hk1⟩, hk2⟩, hcomm⟩, hcen⟩ := hZ
    intro i hi
    have hall := List.all_eq_true.mp hcomm
    have key : ∀ s ∈ [kom, kom2], kmul s (genK i) = kmul (genK i) s := by
      intro s hs
      have h1 := List.all_eq_true.mp (hall s hs)
      have hg : genK i ∈ [u0, a0, b0] := by
        rcases genK_cases i with h | h | h <;> simp [h]
      have := h1 _ hg
      unfold comm at this
      exact Nat.eq_of_beq_eq_true this
    exact ⟨key kom (by simp), key kom2 (by simp)⟩
  ·
    unfold chkZ at hZ
    simp only [Bool.and_eq_true] at hZ
    obtain ⟨⟨⟨⟨hk0, hk1⟩, hk2⟩, hcomm⟩, hcen⟩ := hZ
    intro g hg hc
    have h1 := List.all_eq_true.mp hcen g hg
    have c0 : comm g u0 = true := Nat.beq_eq_true_eq _ _ ▸ (hc 0 (by norm_num))
    have c1 : comm g a0 = true := Nat.beq_eq_true_eq _ _ ▸ (hc 1 (by norm_num))
    have c2 : comm g b0 = true := Nat.beq_eq_true_eq _ _ ▸ (hc 2 (by norm_num))
    simpa [c0, c1, c2] using h1
  ·
    unfold chkO1 at hO1
    intro a ha
    have := List.all_eq_true.mp hO1 a ha
    simpa using this
  ·
    unfold chkO2 at hO2
    intro a ha b hb hab hcab c hc hac hbc
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hO2 a ha) b hb
    have hab' : Nat.beq a b = false := (beq_eq_false_iff _ _).mpr hab
    rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · simp [hab', hcab] at h1
    · have h2 := List.all_eq_true.mp h1 c hc
      simpa [hac, hbc, Nat.beq_eq, or_assoc] using h2
  ·
    unfold chkC at hC
    simp only [Bool.and_eq_true] at hC
    obtain ⟨⟨hl, hall⟩, hany⟩ := hC
    obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, Nat.beq_eq] at hpe
    obtain ⟨h1, h2⟩ := hpe
    have : p = (e1, e2) := Prod.ext h1 h2
    rw [← this]
    exact hp
  ·
    unfold chkC at hC
    simp only [Bool.and_eq_true] at hC
    obtain ⟨⟨hl, hall⟩, hany⟩ := hC
    intro p hp
    rw [(listEqP_iff _ _).mp hl] at hp
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hp
    have := List.all_eq_true.mp hall e he
    unfold entryC at this
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at this
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
    subst hee
    exact ⟨e.2.2.1, e.2.2.2, (hmem _).mp h1, (hmem _).mp h2, h3, h4, h5, (beq_eq_false_iff _ _).mp h6⟩
  ·
    unfold chkR at hR
    simp only [Bool.and_eq_true] at hR
    obtain ⟨hl, hall⟩ := hR
    intro x1 x2 x3 hx
    rw [(listEqT_iff _ _).mp hl] at hx
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hx
    simp only [Prod.mk.injEq] at hee
    obtain ⟨rfl, rfl, rfl⟩ := hee
    have := List.all_eq_true.mp hall e he
    unfold entryR at this
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
    have h36 : (2 : Nat) ^ 36 = 68719476736 := by norm_num
    exact ⟨e.2.2.2.1, e.2.2.2.2, by omega, by omega, h3, h4, h5, h6⟩

end CFSG.Quasithin.D35ValChk
