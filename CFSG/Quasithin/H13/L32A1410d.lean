module

public import CFSG.Quasithin.H13.L32A1410c

public section

namespace CFSG.Quasithin.H13.G5ACert

open Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert S8Cert G5Cert CFSG.Quasithin

@[expose] def KA5 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub kAG

theorem kA_spec :
    subB kAG kAE = true ∧ kAE.length = 60 ∧ (∀ p ∈ kAP, mul8 p.1 p.2 = one8 ∧ Valid8 p.2) ∧
      (∀ b : Bool, (∀ g ∈ kAG, g ∈ gEA b) ∧
        ∀ g ∈ gGA b, ∀ k ∈ kAE, mul8 g k ∈ kAE.map fun k => mul8 k g) ∧
      (∀ x ∈ kAE, x = one8 ∨
        (subB (conjA x) (elemsOf (conjA x)) = true ∧ (elemsOf (conjA x)).length = 60)) ∧
      (∃ k ∈ kAE, mv8 k vA ≠ vA) ∧
      ∀ b : Bool, ∀ p ∈ kAP, (∀ q ∈ kAE, q ∈ pEA b →
          mul8 (mul8 p.1 q) p.2 ∈ kAE ∧ mul8 (mul8 p.1 q) p.2 ∈ pEA b) → p.1 ∈ mEA b 1 := by
  have h := g5aCheck_parts.2.2.2.2
  simp only [kAB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, by simpa using h2, fun p hp => ?_, fun b => ?_, fun x hx => ?_, ?_,
    fun b p hp hn => ?_⟩
  · simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h3
    obtain ⟨h3a, h3b⟩ := h3 p hp
    exact ⟨h3a, by simpa [validB, Valid8] using h3b⟩
  · simp only [List.all_eq_true, Bool.and_eq_true, Std.HashSet.contains_ofList,
      List.contains_iff_mem] at h4
    obtain ⟨h4a, h4b⟩ := h4 b (mem_tf b)
    exact ⟨h4a, fun g hg k hk => h4b g hg k hk⟩
  · simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h5
    exact h5 x hx
  · simp only [List.any_eq_true, bne_iff_ne, ne_eq] at h6
    exact h6
  · simp only [List.all_eq_true] at h7
    have h8 := h7 b (mem_tf b) p hp
    rw [Bool.or_eq_true, List.any_eq_true] at h8
    rcases h8 with h | ⟨q, hq, hq'⟩
    · exact List.contains_iff_mem.mp h
    · exfalso
      rw [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hq'
      obtain ⟨hqP, hc⟩ := hq'
      have hcq := hn q hq (List.contains_iff_mem.mp hqP)
      rcases hc with hc | hc
      · rw [← Bool.not_eq_true, List.contains_iff_mem] at hc
        exact hc hcq.1
      · rw [← Bool.not_eq_true, List.contains_iff_mem] at hc
        exact hc hcq.2

theorem mem_kAP {k : List ℕ} (hk : k ∈ kAE) :
    ∃ k' : List ℕ, (k, k') ∈ kAP :=
  ⟨_, List.mem_map.mpr ⟨k, hk, rfl⟩⟩

theorem KA5_gens_mem (b : Bool) : ∀ g ∈ kAG, g ∈ gEA b :=
  ((kA_spec).2.2.2.1 b).1

theorem KA5_le (b : Bool) : KA5 ≤ g5 b false :=
  genSub_le_gA5 b (KA5_gens_mem b)

theorem kA_unit :
    ∀ g ∈ kAG, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  unit_of_gEA true (KA5_gens_mem true)

theorem mem_KA5_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ KA5 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ kAE :=
  mem_genSub_iff_of kA_spec.1 kA_unit u

theorem card_KA5 : Nat.card KA5 = 60 := by
  rw [KA5, card_genSub_of kA_spec.1 kA_unit]
  exact kA_spec.2.1

theorem exists_KA5_of {c : List ℕ} (hc : c ∈ kAE) :
    ∃ u ∈ KA5, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  exact exists_evalW _ (subB_spec kA_spec.1).2.2.2.2 kA_unit w

theorem valid8_of_kAE {c : List ℕ} (hc : c ∈ kAE) : Valid8 c :=
  (subB_spec kA_spec.1).1 c hc

theorem kAP_inv {u : GL (Fin 8) (ZMod 2)} {c : List ℕ}
    (hp : (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)), c) ∈ kAP) :
    c = colsOf ((u⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  obtain ⟨h1, h2⟩ := kA_spec.2.2.1 _ hp
  have h3 : dec8 (mul8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) c) = 1 := by
    rw [h1, dec8_one8]
  rw [dec8_mul8 _ _ h2.1, dec8_colsOf] at h3
  have h4 : dec8 c = ((u⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
    calc dec8 c = ((u⁻¹ * u : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 c := by
          rw [inv_mul_cancel, Units.val_one, one_mul]
      _ = ((u⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
          rw [Units.val_mul, mul_assoc, h3, mul_one]
  rw [← h4, colsOf_dec8 h2]

theorem KA5_normal (b : Bool) :
    g5 b false ≤ Subgroup.normalizer (KA5 : Set (GL (Fin 8) (ZMod 2))) := by
  rw [gA5_eq]
  refine (Subgroup.closure_le _).mpr fun γ hγ => Subgroup.mem_normalizer_fintype fun k hk => ?_
  have hγc : colsOf (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gGA b := hγ
  have hkc := (mem_KA5_iff k).mp hk
  obtain ⟨k', hk', he⟩ := List.mem_map.mp ((kA_spec).2.2.2.1 b |>.2 _ hγc _ hkc)
  obtain ⟨v, hv, hv'⟩ := exists_KA5_of hk'
  have hγk : γ * k = v * γ := by
    apply eq_of_colsOf_eq
    rw [Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul, ← he, hv',
      colsOf_dec8 (valid8_of_kAE hk')]
  rw [hγk, mul_assoc, mul_inv_cancel, mul_one]
  exact hv

theorem exists_KA5_moves :
    ∃ k ∈ KA5, (k : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vA) ≠ vec8 vA := by
  obtain ⟨c, hc, hcv⟩ := kA_spec.2.2.2.2.2.1
  obtain ⟨u, hu, hu'⟩ := exists_KA5_of hc
  refine ⟨u, hu, fun h => hcv ?_⟩
  rw [hu', dec8_mulVec] at h
  exact vec8_inj (mv8_lt (valid8_of_kAE hc) _) (by decide) h

theorem KA5_borel (b : Bool) {k : GL (Fin 8) (ZMod 2)}
    (hk : k ∈ KA5) (hn : ∀ q ∈ KA5 ⊓ PA5 b, k * q * k⁻¹ ∈ KA5 ⊓ PA5 b) : k ∈ MA5 b 1 := by
  have hkc := (mem_KA5_iff k).mp hk
  obtain ⟨c, hc⟩ := mem_kAP hkc
  have hci := kAP_inv hc
  rw [mem_MA5_iff b (by norm_num)]
  refine kA_spec.2.2.2.2.2.2 b _ hc fun q hq hqP => ?_
  obtain ⟨v, hv, hv'⟩ := exists_KA5_of hq
  have hvP : v ∈ PA5 b := by
    rw [mem_PA5_iff, hv', colsOf_dec8 (valid8_of_kAE hq)]
    exact hqP
  have h := hn v ⟨hv, hvP⟩
  have he : mul8 (mul8 (colsOf (k : Matrix (Fin 8) (Fin 8) (ZMod 2))) q) c =
      colsOf ((k * v * k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
    rw [hci, Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul, hv',
      colsOf_dec8 (valid8_of_kAE hq)]
  rw [he]
  exact ⟨(mem_KA5_iff _).mp h.1, (mem_PA5_iff b _).mp h.2⟩

theorem isSimpleGroup_KA5 : IsSimpleGroup ↥KA5 := by
  have hcard := card_KA5
  have : Nontrivial ↥KA5 := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  refine ⟨fun N hN => ?_⟩
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨x, hxN⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hxc := (mem_KA5_iff (x : GL (Fin 8) (ZMod 2))).mp x.2
  rcases kA_spec.2.2.2.2.1 _ hxc with h | ⟨hsub, hlen⟩
  · exfalso
    apply hx1
    exact Subtype.ext (eq_of_colsOf_eq (by rw [h]; simp [colsOf_one]))
  have hconj : ∀ g ∈ conjA
      (colsOf ((x : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))),
      ∃ u : GL (Fin 8) (ZMod 2), ∃ hu : u ∈ KA5, (⟨u, hu⟩ : ↥KA5) ∈ N ∧
        (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨v, hv, hv'⟩ := exists_KA5_of hk
    have hkv : k = colsOf (v : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
      rw [hv', colsOf_dec8 (valid8_of_kAE hk)]
    have hp' : (colsOf (v : Matrix (Fin 8) (Fin 8) (ZMod 2)),
        (kAE.find? fun y => mul8 k y == one8).getD one8) ∈ kAP := by
      rw [← hkv]; exact hp
    have hci := kAP_inv hp'
    refine ⟨v * x * v⁻¹, KA5.mul_mem (KA5.mul_mem hv x.2) (KA5.inv_mem hv), ?_, ?_⟩
    · have := hN.conj_mem x hxN ⟨v, hv⟩
      exact this
    · show _ = dec8 (mul8 (mul8 k _) _)
      rw [hci, hkv, ← colsOf_mul, ← colsOf_mul, dec8_colsOf, Units.val_mul, Units.val_mul]
  set gs := conjA (colsOf ((x : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) with hgs
  have hunit : ∀ g ∈ gs, ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
    fun g hg => let ⟨u, _, _, hu⟩ := hconj g hg; ⟨u, hu⟩
  have hc60 : Nat.card (genSub gs) = 60 := by
    rw [card_genSub_of hsub hunit]
    exact hlen
  have hle : genSub gs ≤ N.map KA5.subtype := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    obtain ⟨u', hu', huN, hu''⟩ := hconj _ hu
    have : u = u' := by
      apply Units.ext
      rw [hu'', dec8_colsOf]
    exact ⟨⟨u', hu'⟩, huN, by rw [this]; rfl⟩
  have hNc : 60 ≤ Nat.card N := by
    have := Subgroup.card_le_of_le hle
    rw [hc60, Subgroup.card_map_of_injective KA5.subtype_injective] at this
    exact this
  rw [← Subgroup.card_eq_iff_eq_top]
  exact le_antisymm (Subgroup.card_le_card_group N) (hcard ▸ hNc)

end CFSG.Quasithin.H13.G5ACert

end
