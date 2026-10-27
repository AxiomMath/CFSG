module

public import CFSG.Sporadic.Co2Smith.GlRootD1Spec
public import CFSG.Sporadic.Co2Smith.CBound

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem le_relIndex_of_distinct {G : Type*} [Group G] [Finite G] {H L : Subgroup G} {n : ℕ}
    (a : ℕ → G) (ha : ∀ i < n, a i ∈ L)
    (hd : ∀ i < n, ∀ k < n, i ≠ k → (a k)⁻¹ * a i ∉ H) : n ≤ H.relIndex L := by
  classical
  rw [relIndex, index_eq_card]
  let f : Fin n → ↥L ⧸ H.subgroupOf L := fun i => QuotientGroup.mk ⟨a i, ha i i.isLt⟩
  have hf : Function.Injective f := by
    intro i k e
    by_contra hne
    have := QuotientGroup.eq.1 e
    rw [mem_subgroupOf] at this
    apply hd k k.isLt i i.isLt (fun h => hne (Fin.ext h).symm)
    simpa using this
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem card_mul_relIndex_of_le {G : Type*} [Group G] {H L : Subgroup G} (h : H ≤ L) :
    Nat.card H * H.relIndex L = Nat.card L := by
  rw [relIndex, ← card_mul_index (H.subgroupOf L)]
  congr 1
  exact (Nat.card_congr (subgroupOfEquivOfLe h).toEquiv).symm

theorem card_mul_le_of_distinct {G : Type*} [Group G] [Finite G] {H L : Subgroup G}
    (hHL : H ≤ L) {n : ℕ} (a : ℕ → G) (ha : ∀ i < n, a i ∈ L)
    (hd : ∀ i < n, ∀ k < n, i ≠ k → (a k)⁻¹ * a i ∉ H) : Nat.card H * n ≤ Nat.card L := by
  rw [← card_mul_relIndex_of_le hHL]
  exact Nat.mul_le_mul_left _ (le_relIndex_of_distinct a ha hd)

theorem xLongK_one : xLongK 1 = x25K := rfl

theorem F0c_one_conj_mem
    {a : K} (ha : a ∈ Ax25) {f : K} (hf : f ∈ F0c 1) :
    a * f * a⁻¹ ∈ F0c 1 :=
  conj_mem_F0c (k := 1) (by decide) (mem_Ax25.1 ha).1
    (by rw [xLongK_one]; exact (mem_Ax25.1 ha).2) hf

theorem Qsub_conj_mem
    {a : K} (ha : a ∈ Cz) {q : K} (hq : q ∈ Qsub) :
    a * q * a⁻¹ ∈ Qsub :=
  (Qsub_subgroupOf_normal).conj_mem ⟨q, Qsub_le_Cz hq⟩ hq ⟨a, ha⟩

theorem Qx25_conj_mem
    {a : K} (ha : a ∈ Ax25) {q : K} (hq : q ∈ Qx25) :
    a * q * a⁻¹ ∈ Qx25 := by
  refine mem_Qx25.2 ⟨Qsub_conj_mem (mem_Ax25.1 ha).1 (mem_Qx25.1 hq).1, ?_⟩
  have c1 : Commute a x25K := (mem_Ax25.1 ha).2
  have c2 : Commute q x25K := (mem_Qx25.1 hq).2
  exact (c1.mul_left c2).mul_left c1.inv_left

theorem X0g_le_F0c :
    X0g ≤ F0c 1 := fun _ hx => ⟨Qsub_le_Cz hx.1, hx.2⟩

theorem X0g_conj_mem
    {a : K} (ha : a ∈ Ax25) {x : K} (hx : x ∈ X0g) :
    a * x * a⁻¹ ∈ X0g :=
  ⟨Qsub_conj_mem (mem_Ax25.1 ha).1 hx.1, (F0c_one_conj_mem ha (X0g_le_F0c hx)).2⟩

theorem X0g_le_Qx25 :
    X0g ≤ Qx25 := fun _ hx =>
  mem_Qx25.2 ⟨hx.1, (mem_Ax25.1 (F0c_one_le_Ax25 (X0g_le_F0c hx))).2⟩

theorem d1Orb_spec : Native.d1Orb.size = 1260 ∧
    (∀ p ∈ Native.d1Orb, (∀ k ∈ p, k ∈ Native.glCzLet) ∧
      mulRows 22 (Native.glR p) (Native.glR (Native.d1Inv p)) = idRows 22) ∧
    (∀ R ∈ Native.d1ORA, Native.validM R = true) ∧
    ∀ i < 1260, ∀ k < i, Native.d1ORA.getD i #[] ≠ Native.d1ORA.getD k #[] := by
  have h := d1_parts.2.2.2.2.2.1
  rw [Native.d1OrbOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨beq_iff_eq.1 h1, fun p hp => ?_, fun R hR => Array.all_eq_true_iff_forall_mem.1 h3 R hR,
    fun i hi k hk => ?_⟩
  · have := Array.all_eq_true_iff_forall_mem.1 h2 p hp
    rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at this
    exact ⟨fun k hk => List.contains_iff_mem.1 (this.1 k hk), this.2⟩
  · have := List.all_eq_true.1 (List.all_eq_true.1 h4 i (List.mem_range.2 hi)) k
      (List.mem_range.2 hk)
    exact bne_iff_ne.1 this

theorem d1Orb_getD_mem {i : ℕ} (hi : i < 1260) :
    Native.d1Orb.getD i [] ∈ Native.d1Orb := by
  have hi' : i < Native.d1Orb.size := by rw [d1Orb_spec.1]; exact hi
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
  exact Array.getElem_mem hi'

theorem d1ORA_getD {i : ℕ} (hi : i < 1260) :
    Native.d1ORA.getD i #[] = Native.d1OR (Native.d1Orb.getD i []) := by
  have hi' : i < Native.d1Orb.size := by rw [d1Orb_spec.1]; exact hi
  simp [Native.d1ORA, Array.getD_eq_getD_getElem?, hi']

@[expose] noncomputable def d1OrbK (i : ℕ) : K :=
  glE (Native.d1Orb.getD i [])

theorem d1OrbK_letters (i : ℕ) :
    ∀ k ∈ Native.d1Orb.getD i [], k ∈ Native.glCzLet := by
  by_cases hi : i < 1260
  · exact (d1Orb_spec.2.1 _ (d1Orb_getD_mem hi)).1
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [d1Orb_spec.1]; omega),
      Option.getD_none]
    intro k hk
    exact absurd hk List.not_mem_nil

theorem d1OrbK_mem
    (i : ℕ) : d1OrbK i ∈ Cz :=
  glE_mem_Cz (d1OrbK_letters i)

theorem d1OrbK_inv {i : ℕ}
    (hi : i < 1260) : glE (Native.d1Inv (Native.d1Orb.getD i [])) = (d1OrbK i)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (eq_of_val_eq ?_)
  rw [val_val_mul, d1OrbK, glE_val fun k hk => glCzLet_lt (d1OrbK_letters i k hk),
    glE_val fun k hk => glCzLet_lt (d1OrbK_letters i k (mem_d1Inv hk)), ← rowsMatrix_mulRows,
    (d1Orb_spec.2.1 _ (d1Orb_getD_mem hi)).2, rowsMatrix_idRows]
  rfl

theorem d1OrbK_conj_val {i : ℕ}
    (hi : i < 1260) :
    (d1OrbK i * x25K * (d1OrbK i)⁻¹).val.val = rowsMatrix 22 (Native.d1ORA.getD i #[]) := by
  rw [← d1OrbK_inv hi, d1ORA_getD hi, Native.d1OR, d1OrbK]
  exact val_mul3 (glE_val fun k hk => glCzLet_lt (d1OrbK_letters i k hk)) x25K_val
    (glE_val fun k hk => glCzLet_lt (d1OrbK_letters i k (mem_d1Inv hk)))

theorem d1OrbK_conj_ne {i k : ℕ}
    (hi : i < 1260) (hk : k < i) :
    d1OrbK i * x25K * (d1OrbK i)⁻¹ ≠ d1OrbK k * x25K * (d1OrbK k)⁻¹ := by
  intro e
  have hk' : k < 1260 := by omega
  apply d1Orb_spec.2.2.2 i hi k hk
  refine eq_of_rowsMatrix_eq (d1Orb_spec.2.2.1 _ ?_) (d1Orb_spec.2.2.1 _ ?_) ?_
  · rw [d1ORA_getD hi]
    exact Array.mem_map_of_mem (d1Orb_getD_mem hi)
  · rw [d1ORA_getD hk']
    exact Array.mem_map_of_mem (d1Orb_getD_mem hk')
  · rw [← d1OrbK_conj_val hi, ← d1OrbK_conj_val hk', e]

set_option maxRecDepth 10000 in
theorem natCard_Ax25_le :
    Nat.card Ax25 ≤ 589824 := by
  have h := card_mul_le_of_distinct (H := Ax25) (L := Cz) inf_le_left (n := 1260) d1OrbK
    (fun i _ => d1OrbK_mem i) (fun i hi k hk hik hmem => by
      have hc := (mem_Ax25.1 hmem).2
      have e : d1OrbK i * x25K * (d1OrbK i)⁻¹ = d1OrbK k * x25K * (d1OrbK k)⁻¹ := by
        have hi' : d1OrbK i = d1OrbK k * ((d1OrbK k)⁻¹ * d1OrbK i) := by group
        rw [hi', show d1OrbK k * ((d1OrbK k)⁻¹ * d1OrbK i) * x25K *
          (d1OrbK k * ((d1OrbK k)⁻¹ * d1OrbK i))⁻¹ = d1OrbK k * (((d1OrbK k)⁻¹ * d1OrbK i) *
            x25K) * ((d1OrbK k)⁻¹ * d1OrbK i)⁻¹ * (d1OrbK k)⁻¹ by group, hc]
        group
      rcases Nat.lt_or_gt_of_ne hik with h | h
      · exact d1OrbK_conj_ne hk h e.symm
      · exact d1OrbK_conj_ne hi h e)
  rw [natCard_Cz] at h
  omega

theorem d1Tree_spec : Native.d1Tree.size = 576 ∧
    (∀ R ∈ Native.d1X0R, Native.validM R = true) ∧
    (∀ i < 576, ∀ j < 4, Native.validM (Native.d1UR i j) = true) ∧
    ∀ i < 576, ∀ k < i, ∃ j < 4,
      Native.d1X0R.contains (mulRows 22 (Native.d1UR i j) (Native.d1UR k j)) = false := by
  have h := d1_parts.2.2.2.2.1
  rw [Native.d1TreeOK, Bool.and_eq_true, Bool.and_eq_true, Native.d1TreeChk,
    Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨beq_iff_eq.1 h1, List.all_eq_true.1 h2, fun i hi j hj => ?_, fun i hi k hk => ?_⟩
  · exact List.all_eq_true.1 (List.all_eq_true.1 h3 i (List.mem_range.2 hi)) j
      (List.mem_range.2 hj)
  · obtain ⟨j, hj, hc⟩ := List.any_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h4 i
      (List.mem_range.2 hi)) k (List.mem_range.2 hk))
    rw [Bool.not_eq_true'] at hc
    exact ⟨j, List.mem_range.1 hj, hc⟩

@[expose] noncomputable def q4K (j : ℕ) : K :=
  xRootK (if j < 2 then 1 else 2) (j % 2 + 1)

theorem q4K_mul_self (j : ℕ) :
    q4K j * q4K j = 1 := by
  have hp : j % 2 + 1 ∈ [1, 2, 3] := by
    have := Nat.mod_lt j (by norm_num : 0 < 2)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  rw [q4K, xRootK_mul (by split_ifs <;> norm_num) hp hp, Nat.xor_self]
  simp [xRootK]

theorem q4K_val (j : ℕ) :
    (q4K j).val.val = rowsMatrix 22 (Native.d1Q4 j) :=
  xRootK_val _ _

@[expose] noncomputable def W25 :
    Subgroup K where
  carrier := {a | a ∈ Ax25 ∧ ∀ j < 4, a * q4K j * a⁻¹ * q4K j ∈ X0g}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Ax25.mul_mem ha hb, fun j hj => ?_⟩
    have e : a * b * q4K j * (a * b)⁻¹ * q4K j =
        a * (b * q4K j * b⁻¹ * q4K j) * a⁻¹ * (a * q4K j * a⁻¹ * q4K j) := by
      rw [show a * (b * q4K j * b⁻¹ * q4K j) * a⁻¹ * (a * q4K j * a⁻¹ * q4K j) =
        a * b * q4K j * b⁻¹ * (q4K j * q4K j) * a⁻¹ * q4K j by group, q4K_mul_self, mul_one]
      group
    rw [e]
    exact X0g.mul_mem (X0g_conj_mem ha (hb' j hj)) (ha' j hj)
  one_mem' := ⟨Ax25.one_mem, fun j _ => by
    rw [inv_one, mul_one, one_mul, q4K_mul_self]
    exact X0g.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Ax25.inv_mem ha, fun j hj => ?_⟩
    have hq : (q4K j)⁻¹ = q4K j := inv_eq_of_mul_eq_one_right (q4K_mul_self j)
    have e : a⁻¹ * q4K j * a⁻¹⁻¹ * q4K j = a⁻¹ * (a * q4K j * a⁻¹ * q4K j)⁻¹ * a⁻¹⁻¹ := by
      rw [show (a * q4K j * a⁻¹ * q4K j)⁻¹ = (q4K j)⁻¹ * a * (q4K j)⁻¹ * a⁻¹ by group, hq]
      group
    rw [e]
    exact X0g_conj_mem (Ax25.inv_mem ha) (X0g.inv_mem (ha' j hj))

theorem W25_le :
    W25 ≤ Ax25 := fun _ h => h.1

theorem prod_map_val (f : ℕ → K) (F : ℕ → Array ℕ)
    (hf : ∀ j, (f j).val.val = rowsMatrix 22 (F j)) (l : List ℕ) :
    ((l.map f).prod).val.val =
      rowsMatrix 22 (l.foldl (fun a j => mulRows 22 a (F j)) (idRows 22)) := by
  rw [List.prod_eq_foldl, List.foldl_map]
  suffices h : ∀ (x : K) (A : Array ℕ), x.val.val = rowsMatrix 22 A →
      (l.foldl (fun a j => a * f j) x).val.val =
        rowsMatrix 22 (l.foldl (fun a j => mulRows 22 a (F j)) A) by
    refine h 1 _ ?_
    rw [rowsMatrix_idRows]
    rfl
  induction l with
  | nil => exact fun x A h => h
  | cons j l ih =>
    intro x A h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (by rw [val_val_mul, h, hf, rowsMatrix_mulRows])

@[expose] noncomputable def d1TreeK (i : ℕ) : K :=
  ((Native.d1Tree.getD i []).map d1E).prod

theorem d1TreeK_mem
    (i : ℕ) : d1TreeK i ∈ Ax25 :=
  Ax25.list_prod_mem fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact d1E_mem j

theorem d1TreeK_inv (i : ℕ) :
    (d1TreeK i)⁻¹ = ((Native.d1Tree.getD i []).reverse.map d1EI).prod := by
  rw [d1TreeK, List.prod_inv_reverse, List.map_map, ← List.map_reverse]
  congr 2
  funext j
  exact (d1EI_eq_inv j).symm

theorem d1UR_val {i j : ℕ}
    (hi : i < 576) (hj : j < 4) :
    (d1TreeK i * q4K j * (d1TreeK i)⁻¹).val.val = rowsMatrix 22 (Native.d1UR i j) := by
  have hi' : i < Native.d1Tree.size := by rw [d1Tree_spec.1]; exact hi
  have e : Native.d1UR i j = mulRows 22 (mulRows 22 (Native.d1PR (Native.d1Tree.getD i []))
      (Native.d1Q4 j)) (Native.d1PIR (Native.d1Tree.getD i [])) := by
    simp [Native.d1UR, Native.d1U, Native.d1UNode, Array.getD_eq_getD_getElem?, hi', hj]
  rw [e, d1TreeK_inv, d1TreeK]
  exact val_mul3 (prod_map_val d1E Native.d1ER d1E_val _) (q4K_val j)
    (prod_map_val d1EI Native.d1EIR d1EI_val _)

theorem d1TreeK_not_mem
    {i k : ℕ} (hi : i < 576) (hk : k < i) :
    (d1TreeK k)⁻¹ * d1TreeK i ∉ W25 := by
  rintro ⟨-, hb⟩
  obtain ⟨j, hj, hc⟩ := d1Tree_spec.2.2.2 i hi k hk
  have hk' : k < 576 := by omega
  have hx : d1TreeK i * q4K j * (d1TreeK i)⁻¹ * (d1TreeK k * q4K j * (d1TreeK k)⁻¹) ∈ X0g := by
    have e : d1TreeK i * q4K j * (d1TreeK i)⁻¹ * (d1TreeK k * q4K j * (d1TreeK k)⁻¹) =
        d1TreeK k * ((d1TreeK k)⁻¹ * d1TreeK i * q4K j * ((d1TreeK k)⁻¹ * d1TreeK i)⁻¹ *
          q4K j) * (d1TreeK k)⁻¹ := by group
    rw [e]
    exact X0g_conj_mem (d1TreeK_mem k) (hb j hj)
  obtain ⟨t, ht, ht'⟩ := mem_X0g.1 hx
  have hv : Native.validM (mulRows 22 (Native.d1UR i j) (Native.d1UR k j)) = true :=
    validM_mulRows (d1Tree_spec.2.2.1 i hi j hj) (d1Tree_spec.2.2.1 k hk' j hj)
  have hmem : Native.glRootRows 0 t ∈ Native.d1X0R := by
    rw [Native.d1X0R]
    exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩
  have hR := eq_of_rowsMatrix_eq hv (d1Tree_spec.2.1 _ hmem) (by
    rw [rowsMatrix_mulRows, ← d1UR_val hi hj, ← d1UR_val hk' hj, ← val_val_mul, ← ht',
      xRootK_val])
  rw [hR, List.contains_iff_mem.2 hmem] at hc
  exact absurd hc (by decide)

set_option maxRecDepth 10000 in
theorem natCard_W25_le :
    Nat.card W25 ≤ 1024 := by
  have h := card_mul_le_of_distinct W25_le (n := 576) d1TreeK (fun i _ => d1TreeK_mem i)
    (fun i hi k hk hik hmem => by
      rcases Nat.lt_or_gt_of_ne hik with h | h
      · apply d1TreeK_not_mem hk h
        have := W25.inv_mem hmem
        rwa [_root_.mul_inv_rev, inv_inv] at this
      · exact d1TreeK_not_mem hi h hmem)
  have := natCard_Ax25_le
  omega

end CFSG.Sporadic.Co2Smith
