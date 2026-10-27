module

public import CFSG.Sporadic.Co2Smith.GlU62Spec
public import CFSG.Sporadic.Co2Smith.GlDataChain
public import CFSG.Sporadic.Co2Smith.GlRootD1Card

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def u62L1 : Subgroup K :=
  Subgroup.closure {g | ∃ w ∈ Native.u62L1Words, glE w = g}

theorem u62L1Words_lt : ∀ w ∈ Native.u62L1Words, ∀ k ∈ w, k < 22 := by decide +kernel

theorem u62L1_spec :
    Native.glChainOK Native.u62L1Words Native.u62L1Base Native.u62L1W 26542080 = true ∧
      (∀ w ∈ Native.u62L1Words, Native.glMaps (Native.glR w) 80 80 = true ∧
        Native.commRows (Native.glR w) Native.glZ = true) ∧
      Native.u62L1Words.length = 22 ∧ Native.u62L1Words.getD 21 [] = Native.glD0hWord ∧
      ∀ i < 21, Native.glR (Native.u62L1Words.getD i []) =
        Native.glRootRows (Native.u62L1Ids.getD i (0, 0)).1 (Native.u62L1Ids.getD i (0, 0)).2 := by
  have h := u62_parts.2.2.1
  rw [Native.u62L1OK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    List.all_eq_true, List.all_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun w hw => ?_, h3, h4, fun i hi => beq_iff_eq.1 (h5 i (List.mem_range.2 hi))⟩
  have := h2 w hw
  rw [Bool.and_eq_true] at this
  exact this

theorem u62L1Ids_lt : ∀ i < 21, (Native.u62L1Ids.getD i (0, 0)).1 < 18 ∧
    (Native.u62L1Ids.getD i (0, 0)).2 < 4 := by
  decide

theorem u62L1_gen {w : List ℕ}
    (hw : w ∈ Native.u62L1Words) : glE w = δ0hK ∨ ∃ r < 18, ∃ t < 4, glE w = xRootK r t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
  have hi22 : i < 22 := by rw [← u62L1_spec.2.2.1]; exact hi
  rw [← List.getD_eq_getElem _ [] hi]
  by_cases h21 : i = 21
  · subst h21
    left
    rw [u62L1_spec.2.2.2.1]
    rfl
  · right
    have hi21 : i < 21 := by omega
    refine ⟨_, (u62L1Ids_lt i hi21).1, _, (u62L1Ids_lt i hi21).2,
      eq_of_val_rows (glE_val (u62L1Words_lt _ ?_)) (xRootK_val _ _) (u62L1_spec.2.2.2.2 i hi21)⟩
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem _

theorem map_psiK_u62L1 :
    u62L1.map psiK = Subgroup.closure {σ | ∃ w ∈ Native.u62L1Words, psiK (glE w) = σ} := by
  rw [u62L1, MonoidHom.map_closure]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem natCard_u62L1 :
    Nat.card u62L1 = 26542080 := by
  have h := closure_psiK_card (bs := ([1, 3, 2, 4, 5, 8] : List (Fin 2300))) (by decide)
    u62L1Words_lt (by
      rw [show ([1, 3, 2, 4, 5, 8] : List (Fin 2300)).map Fin.val = Native.u62L1Base from rfl]
      exact u62L1_spec.1)
  rw [← map_psiK_u62L1, Subgroup.card_map_of_injective psiK_injective] at h
  exact h

theorem u62L1_le :
    u62L1 ≤ G1c ⊓ Cz := by
  rw [u62L1, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨co2PermHom_apply_of_maps (glE_val (u62L1Words_lt w hw)) (by norm_num) (by norm_num)
      (u62L1_spec.2.1 w hw).1,
    mem_Cz_of_comm (comm_of_commRows (glE_val (u62L1Words_lt w hw)) z0_val'
      (u62L1_spec.2.1 w hw).2)⟩

@[expose] noncomputable def u62G1K (j : ℕ) : K :=
  glE (Native.u62G1Words.getD j [])

theorem u62G1Words_lt : ∀ w ∈ Native.u62G1Words, ∀ k ∈ w, k < 22 := by decide +kernel

theorem u62C1Words_lt : ∀ w ∈ Native.u62C1Words, ∀ k ∈ w, k < 22 := by decide +kernel

theorem u62InvOK_spec {ws : List (List ℕ)} (h : Native.u62InvOK ws = true) :
    ∀ w ∈ ws, mulRows 22 (Native.glR w) (Native.glR w) = idRows 22 ∧
      Native.glMaps (Native.glR w) 80 80 = true := by
  rw [Native.u62InvOK, List.all_eq_true] at h
  intro w hw
  have := h w hw
  rw [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem u62DistOK_spec {n : ℕ} {O : Array (Array ℕ)} (h : Native.u62DistOK n O = true) :
    O.size = n ∧ (∀ R ∈ O, Native.validM R = true) ∧
      ∀ i < n, ∀ k < i, O.getD i #[] ≠ O.getD k #[] := by
  rw [Native.u62DistOK, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨beq_iff_eq.1 h1, Array.all_eq_true_iff_forall_mem.1 h2, fun i hi k hk => ?_⟩
  exact bne_iff_ne.1 (List.all_eq_true.1 (List.all_eq_true.1 h3 i (List.mem_range.2 hi)) k
    (List.mem_range.2 hk))

theorem getD_mem_of_size {α : Type*} {O : Array α} {n i : ℕ} (hn : O.size = n) (hi : i < n)
    (d : α) : O.getD i d ∈ O := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]
  exact Array.getElem_mem _

theorem glE_getD_val {ws : List (List ℕ)}
    (hws : ∀ w ∈ ws, ∀ k ∈ w, k < 22) (j : ℕ) :
    (glE (ws.getD j [])).val.val =
      rowsMatrix 22 ((ws.toArray.map Native.glR).getD j (idRows 22)) := by
  by_cases hj : j < ws.length
  · rw [List.getD_eq_getElem _ _ hj, glE_val (hws _ (List.getElem_mem hj))]
    congr 1
    simp [Array.getD_eq_getD_getElem?, hj]
  · rw [List.getD_eq_default _ _ (by omega), glE_nil, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simp; omega), Option.getD_none, rowsMatrix_idRows]
    rfl

theorem u62G1K_val (j : ℕ) :
    (u62G1K j).val.val = rowsMatrix 22 (Native.u62G1R.getD j (idRows 22)) :=
  glE_getD_val u62G1Words_lt j

theorem glE_getD_mul_self {ws : List (List ℕ)}
    (hws : ∀ w ∈ ws, ∀ k ∈ w, k < 22) (h : Native.u62InvOK ws = true) (j : ℕ) :
    glE (ws.getD j []) * glE (ws.getD j []) = 1 := by
  by_cases hj : j < ws.length
  · rw [List.getD_eq_getElem _ _ hj]
    have hw := List.getElem_mem hj
    apply eq_of_val_eq
    rw [val_val_mul, glE_val (hws _ hw), ← rowsMatrix_mulRows, (u62InvOK_spec h _ hw).1,
      rowsMatrix_idRows]
    rfl
  · rw [List.getD_eq_default _ _ (by omega), glE_nil, mul_one]

theorem glE_getD_mem_G1c
    {ws : List (List ℕ)} (hws : ∀ w ∈ ws, ∀ k ∈ w, k < 22) (h : Native.u62InvOK ws = true)
    (j : ℕ) : glE (ws.getD j []) ∈ G1c := by
  by_cases hj : j < ws.length
  · rw [List.getD_eq_getElem _ _ hj]
    have hw := List.getElem_mem hj
    exact co2PermHom_apply_of_maps (glE_val (hws _ hw)) (by norm_num) (by norm_num)
      (u62InvOK_spec h _ hw).2
  · rw [List.getD_eq_default _ _ (by omega), glE_nil]
    exact G1c.one_mem

theorem prod_inv_of_involutions {f : ℕ → K} (hf : ∀ j, f j * f j = 1) (l : List ℕ) :
    ((l.map f).prod)⁻¹ = (l.reverse.map f).prod := by
  rw [List.prod_inv_reverse, List.map_map, ← List.map_reverse]
  congr 2
  funext j
  exact inv_eq_of_mul_eq_one_right (hf j)

@[expose] noncomputable def u62OrbK (i : ℕ) : K :=
  ((Native.u62Orb.getD i []).map u62G1K).prod

theorem u62Orb_spec :
    Native.u62InvOK Native.u62G1Words = true ∧ Native.u62DistOK 693 Native.u62OrbR = true := by
  have h := u62_parts.2.2.2.1
  rw [Native.u62OrbOK, Bool.and_eq_true] at h
  exact h

theorem u62OrbK_conj_val {i : ℕ}
    (hi : i < 693) :
    (u62OrbK i * z0 * (u62OrbK i)⁻¹).val.val = rowsMatrix 22 (Native.u62OrbR.getD i #[]) := by
  have hsz := (u62DistOK_spec u62Orb_spec.2).1
  have hi' : i < Native.u62Orb.size := by
    rw [show Native.u62Orb.size = Native.u62OrbR.size by simp [Native.u62OrbR], hsz]
    exact hi
  have e : Native.u62OrbR.getD i #[] = mulRows 22 (mulRows 22
      (Native.u62WR Native.u62G1R (Native.u62Orb.getD i [])) Native.glZ)
      (Native.u62WR Native.u62G1R (Native.u62Orb.getD i []).reverse) := by
    simp [Native.u62OrbR, Array.getD_eq_getD_getElem?, hi']
  rw [e, u62OrbK, prod_inv_of_involutions (f := u62G1K)
    (glE_getD_mul_self u62G1Words_lt u62Orb_spec.1)]
  exact val_mul3 (prod_map_val _ _ u62G1K_val _) z0_val' (prod_map_val _ _ u62G1K_val _)

theorem u62OrbK_mem
    (i : ℕ) : u62OrbK i ∈ G1c :=
  G1c.list_prod_mem fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact glE_getD_mem_G1c u62G1Words_lt u62Orb_spec.1 j

theorem natCard_G1c_inf_Cz_le :
    Nat.card (G1c ⊓ Cz : Subgroup K) ≤ 26542080 := by
  obtain ⟨hsz, hval, hdist⟩ := u62DistOK_spec u62Orb_spec.2
  have hne : ∀ i < 693, ∀ k < i,
      u62OrbK i * z0 * (u62OrbK i)⁻¹ ≠ u62OrbK k * z0 * (u62OrbK k)⁻¹ := by
    intro i hi k hk e
    apply hdist i hi k hk
    exact eq_of_rowsMatrix_eq (hval _ (getD_mem_of_size hsz hi _))
      (hval _ (getD_mem_of_size hsz (by omega) _))
      (by rw [← u62OrbK_conj_val hi, ← u62OrbK_conj_val (by omega), e])
  have h := card_mul_le_of_distinct (H := G1c ⊓ Cz) (L := G1c) inf_le_left (n := 693) u62OrbK
    (fun i _ => u62OrbK_mem i) (fun i hi k hk hik hmem => by
      have hc := comm_of_mem_Cz hmem.2
      have e : u62OrbK i * z0 * (u62OrbK i)⁻¹ = u62OrbK k * z0 * (u62OrbK k)⁻¹ := by
        have hi' : u62OrbK i = u62OrbK k * ((u62OrbK k)⁻¹ * u62OrbK i) := by group
        rw [hi', show u62OrbK k * ((u62OrbK k)⁻¹ * u62OrbK i) * z0 *
          (u62OrbK k * ((u62OrbK k)⁻¹ * u62OrbK i))⁻¹ = u62OrbK k * (((u62OrbK k)⁻¹ *
            u62OrbK i) * z0) * ((u62OrbK k)⁻¹ * u62OrbK i)⁻¹ * (u62OrbK k)⁻¹ by group, hc]
        group
      rcases Nat.lt_or_gt_of_ne hik with h | h
      · exact hne k hk i h e.symm
      · exact hne i hi k h e)
  rw [card_G1c] at h
  exact Nat.le_of_mul_le_mul_right (h.trans (by norm_num)) (by norm_num : 0 < 693)

theorem u62L1_eq :
    u62L1 = G1c ⊓ Cz :=
  Subgroup.eq_of_le_of_card_ge u62L1_le (by rw [natCard_u62L1]; exact natCard_G1c_inf_Cz_le)

@[expose] noncomputable def u62C1K (j : ℕ) : K :=
  glE (Native.u62C1Words.getD j [])

theorem u62C1_spec :
    Native.u62InvOK Native.u62C1Words = true ∧
      (∀ w ∈ Native.u62C1Words, ∀ k ∈ w, k ∈ Native.glC0Let) ∧
      Native.u62DistOK 1296 Native.u62C1E = true ∧ Native.u62C1Words.length = 8 ∧
      Native.u62C1Words.getD 6 [] = Native.glD0hWord ∧
      Native.u62C1Words.getD 7 [] = Native.glD1hWord ∧
      ∀ j < 6, Native.glR (Native.u62C1Words.getD j []) =
        Native.glLongRows (Native.u62C1Frame.getD j 0) := by
  have h := u62_parts.2.2.2.2
  rw [Native.u62C1OK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, fun w hw k hk => ?_, h3, h4, h5, h6, fun j hj => beq_iff_eq.1
    (List.all_eq_true.1 h7 j (List.mem_range.2 hj))⟩
  have := List.all_eq_true.1 (List.all_eq_true.1 h2 w hw) k hk
  exact List.contains_iff_mem.1 this

theorem u62C1K_mem
    (j : ℕ) : u62C1K j ∈ C1c := by
  refine ⟨?_, glE_getD_mem_G1c u62C1Words_lt u62C1_spec.1 j⟩
  by_cases hj : j < Native.u62C1Words.length
  · rw [u62C1K, List.getD_eq_getElem _ _ hj]
    exact glE_mem_C0c (u62C1_spec.2.1 _ (List.getElem_mem hj))
  · rw [u62C1K, List.getD_eq_default _ _ (by omega), glE_nil]
    exact C0c.one_mem

theorem u62C1K_val (j : ℕ) :
    (u62C1K j).val.val = rowsMatrix 22 (Native.u62C1R.getD j (idRows 22)) :=
  glE_getD_val u62C1Words_lt j

@[expose] noncomputable def u62C1EK (i : ℕ) : K :=
  ((Native.u62C1.getD i []).map u62C1K).prod

theorem u62C1EK_val {i : ℕ}
    (hi : i < 1296) : (u62C1EK i).val.val = rowsMatrix 22 (Native.u62C1E.getD i #[]) := by
  have hsz := (u62DistOK_spec u62C1_spec.2.2.1).1
  have hi' : i < Native.u62C1.size := by
    rw [show Native.u62C1.size = Native.u62C1E.size by simp [Native.u62C1E], hsz]
    exact hi
  have e : Native.u62C1E.getD i #[] =
      Native.u62WR Native.u62C1R (Native.u62C1.getD i []) := by
    simp [Native.u62C1E, Array.getD_eq_getD_getElem?, hi']
  rw [e, u62C1EK]
  exact prod_map_val _ _ u62C1K_val _

theorem closure_u62C1K :
    Subgroup.closure (Set.range u62C1K) = C1c := by
  obtain ⟨hsz, hval, hdist⟩ := u62DistOK_spec u62C1_spec.2.2.1
  have hle : Subgroup.closure (Set.range u62C1K) ≤ C1c := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact u62C1K_mem j
  refine (Subgroup.eq_of_le_of_card_ge hle ?_)
  have h := card_mul_le_of_distinct (H := ⊥) (L := Subgroup.closure (Set.range u62C1K))
    bot_le (n := 1296) u62C1EK
    (fun i _ => (Subgroup.closure (Set.range u62C1K)).list_prod_mem fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure ⟨j, rfl⟩)
    (fun i hi k hk hik hmem => by
      rw [Subgroup.mem_bot, inv_mul_eq_one] at hmem
      rcases Nat.lt_or_gt_of_ne hik with h | h
      · exact hdist k hk i h (eq_of_rowsMatrix_eq (hval _ (getD_mem_of_size hsz hk _))
          (hval _ (getD_mem_of_size hsz hi _))
          (by rw [← u62C1EK_val hk, ← u62C1EK_val hi, hmem]))
      · exact hdist i hi k h (eq_of_rowsMatrix_eq (hval _ (getD_mem_of_size hsz hi _))
          (hval _ (getD_mem_of_size hsz hk _))
          (by rw [← u62C1EK_val hi, ← u62C1EK_val hk, hmem])))
  rw [Subgroup.card_bot, one_mul] at h
  rw [card_C1c]
  exact h

end CFSG.Sporadic.Co2Smith
