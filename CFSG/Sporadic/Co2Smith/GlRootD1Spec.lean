module

public import CFSG.Sporadic.Co2Smith.GlRootTmap
public import CFSG.Sporadic.Co2Smith.GlU62D1Check

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem d1_parts :
    Native.d1EltOK = true ∧ Native.d1Lam1OK = true ∧ Native.d1Lam2OK = true ∧
      Native.d1DecOK = true ∧ Native.d1TreeOK = true ∧ Native.d1OrbOK = true ∧
      Native.d1PhiOK = true ∧ Native.d1RootOK = true ∧ Native.d1BreakOK = true := by
  have h := d1_check
  simp only [Native.d1OK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem d1Elt_spec :
    Native.validM Native.glZ = true ∧ Native.validM Native.glX25 = true ∧
    Native.validM (Native.subId Native.glZ) = true ∧ Native.glF0Valid Native.glX25 = true ∧
    Native.glFixZ Native.glX25 = false ∧ Native.d1QD.length = 128 ∧
    (∀ j < 3, (∀ k ∈ Native.d1EWords.getD j [], k ∈ Native.glCzLet) ∧
      Native.commRows (Native.d1ER j) Native.glX25 = true ∧
      mulRows 22 (Native.d1ER j) (Native.d1EIR j) = idRows 22) ∧
    ∀ g < 5, (∀ k ∈ Native.d1MarkWords.getD g [], k ∈ Native.glC0Let) ∧
      Native.commRows (Native.glR (Native.d1MarkWords.getD g [])) Native.glZ = true ∧
      Native.commRows (Native.glR (Native.d1MarkWords.getD g [])) Native.glX25 = true := by
  have h := d1_parts.1
  simp only [Native.d1EltOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.mem_range, List.contains_iff_mem, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun j hj => ⟨(h7 j hj).1.1, (h7 j hj).1.2, (h7 j hj).2⟩,
    fun g hg => ⟨(h8 g hg).1.1, (h8 g hg).1.2, (h8 g hg).2⟩⟩

theorem glCzLet_lt {k : ℕ} (h : k ∈ Native.glCzLet) : k < 22 := by
  simp only [Native.glCzLet, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem lt_of_mem_glC0Let {k : ℕ} (h : k ∈ Native.glC0Let) : k < 22 := by
  simp only [Native.glC0Let, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem mem_d1Inv {w : List ℕ} {k : ℕ} (h : k ∈ Native.d1Inv w) : k ∈ w := by
  simp only [Native.d1Inv, List.mem_flatMap, List.mem_reverse, List.mem_replicate] at h
  obtain ⟨a, ha, -, rfl⟩ := h
  exact ha

theorem d1EWords_getD_of_le {j : ℕ} (hj : 3 ≤ j) : Native.d1EWords.getD j [] = [] :=
  List.getD_eq_default _ _ (show Native.d1EWords.length ≤ j from le_of_eq_of_le rfl hj)

theorem d1E_letters (j : ℕ) :
    ∀ k ∈ Native.d1EWords.getD j [], k ∈ Native.glCzLet := by
  by_cases hj : j < 3
  · exact (d1Elt_spec.2.2.2.2.2.2.1 j hj).1
  · rw [d1EWords_getD_of_le (by omega)]
    intro k hk
    exact absurd hk List.not_mem_nil

@[expose] noncomputable def d1E (j : ℕ) : K :=
  glE (Native.d1EWords.getD j [])

@[expose] noncomputable def d1EI (j : ℕ) : K :=
  glE (Native.d1Inv (Native.d1EWords.getD j []))

@[expose] noncomputable def d1Gk (j : ℕ) : K :=
  if j < 3 then d1E j else d1EI (j - 3)

@[expose] noncomputable def d1GIk (j : ℕ) : K :=
  if j < 3 then d1EI j else d1E (j - 3)

theorem d1E_val (j : ℕ) :
    (d1E j).val.val = rowsMatrix 22 (Native.d1ER j) :=
  glE_val fun k hk => glCzLet_lt (d1E_letters j k hk)

theorem d1EI_val (j : ℕ) :
    (d1EI j).val.val = rowsMatrix 22 (Native.d1EIR j) :=
  glE_val fun k hk => glCzLet_lt (d1E_letters j k (mem_d1Inv hk))

theorem glE_nil : glE [] = 1 := rfl

theorem d1E_mul_d1EI (j : ℕ) :
    d1E j * d1EI j = 1 := by
  by_cases hj : j < 3
  · apply eq_of_val_eq
    rw [val_val_mul, d1E_val, d1EI_val, ← rowsMatrix_mulRows,
      (d1Elt_spec.2.2.2.2.2.2.1 j hj).2.2, rowsMatrix_idRows]
    rfl
  · rw [d1E, d1EI, d1EWords_getD_of_le (by omega), show Native.d1Inv [] = [] from rfl, glE_nil,
      mul_one]

theorem d1EI_eq_inv (j : ℕ) :
    d1EI j = (d1E j)⁻¹ :=
  eq_inv_of_mul_eq_one_right (d1E_mul_d1EI j)

theorem d1E_mem
    (j : ℕ) : d1E j ∈ Ax25 := by
  refine mem_Ax25.2 ⟨glE_mem_Cz (d1E_letters j), ?_⟩
  by_cases hj : j < 3
  · exact comm_of_commRows (d1E_val j) x25K_val (d1Elt_spec.2.2.2.2.2.2.1 j hj).2.1
  · rw [d1E, d1EWords_getD_of_le (by omega), glE_nil, one_mul, mul_one]

theorem d1EI_mem
    (j : ℕ) : d1EI j ∈ Ax25 := by
  rw [d1EI_eq_inv]
  exact Ax25.inv_mem (d1E_mem j)

theorem d1Gk_val (j : ℕ) :
    (d1Gk j).val.val = rowsMatrix 22 (Native.d1G j) := by
  unfold d1Gk Native.d1G
  split_ifs
  · exact d1E_val j
  · exact d1EI_val _

theorem d1GIk_val (j : ℕ) :
    (d1GIk j).val.val = rowsMatrix 22 (Native.d1GI j) := by
  unfold d1GIk Native.d1GI
  split_ifs
  · exact d1EI_val j
  · exact d1E_val _

theorem d1GIk_eq_inv (j : ℕ) :
    d1GIk j = (d1Gk j)⁻¹ := by
  unfold d1GIk d1Gk
  split_ifs
  · exact d1EI_eq_inv j
  · rw [d1EI_eq_inv, inv_inv]

theorem d1Gk_mem
    (j : ℕ) : d1Gk j ∈ Ax25 := by
  unfold d1Gk
  split_ifs
  · exact d1E_mem j
  · exact d1EI_mem _

theorem rows_getD_of {S : Subgroup K} {ent : Array (Array ℕ)}
    (h : ∀ R ∈ ent, ∃ x ∈ S, x.val.val = rowsMatrix 22 R) (i : ℕ) :
    ∃ x ∈ S, x.val.val = rowsMatrix 22 (ent.getD i (idRows 22)) := by
  rw [Array.getD_eq_getD_getElem?]
  cases h' : ent[i]? with
  | none => exact ⟨1, S.one_mem, by rw [Option.getD_none, rowsMatrix_idRows]; rfl⟩
  | some R =>
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 h'
    exact h _ (Array.getElem_mem hi)

theorem d1Run_sound
    (S : Subgroup K) (hS : ∀ x ∈ S, ∀ j, d1Gk j * x * (d1Gk j)⁻¹ ∈ S) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (start : Array (Array ℕ)),
      (∀ R ∈ start, ∃ x ∈ S, x.val.val = rowsMatrix 22 R) →
        ∀ R ∈ Native.d1Run start l, ∃ x ∈ S, x.val.val = rowsMatrix 22 R := by
  intro l
  induction l with
  | nil => exact fun start h => h
  | cons s l ih =>
    intro start h
    refine ih (Native.d1Step start s) fun R hR => ?_
    unfold Native.d1Step at hR
    split_ifs at hR
    · rcases Array.mem_push.1 hR with hR | rfl
      · exact h R hR
      · obtain ⟨x, hx, hxv⟩ := rows_getD_of h s.2.1
        refine ⟨d1Gk s.2.2 * x * d1GIk s.2.2, ?_, val_mul3 (d1Gk_val _) hxv (d1GIk_val _)⟩
        rw [d1GIk_eq_inv]
        exact hS x hx _
    · rcases Array.mem_push.1 hR with hR | rfl
      · exact h R hR
      · obtain ⟨x, hx, hxv⟩ := rows_getD_of h s.2.1
        obtain ⟨y, hy, hyv⟩ := rows_getD_of h s.2.2
        exact ⟨x * y, S.mul_mem hx hy, by rw [val_val_mul, hxv, hyv, rowsMatrix_mulRows]⟩

theorem mem_of_contains {l : Array (Array ℕ)} {R : Array ℕ} (h : l.contains R = true) : R ∈ l :=
  Array.contains_iff_mem.1 h

@[expose] noncomputable def Qx25 : Subgroup K :=
  Qsub ⊓ centralizer ({x25K} : Set K)

theorem mem_Qx25 {y : K} :
    y ∈ Qx25 ↔ y ∈ Qsub ∧ y * x25K = x25K * y := by
  rw [Qx25, Subgroup.mem_inf]
  exact and_congr Iff.rfl mem_centralizer_singleton_iff

theorem Qx25_le_Ax25 :
    Qx25 ≤ Ax25 := fun _ hy =>
  mem_Ax25.2 ⟨Qsub_le_Cz (mem_Qx25.1 hy).1, (mem_Qx25.1 hy).2⟩

theorem glQRows_val {e : ℕ} (he : e < 512) :
    (qElt e).val.val = rowsMatrix 22 (Native.glQRows e) :=
  qElt_val he

theorem qElt_mem_Qx25_iff
    {e : ℕ} (he : e < 512) :
    qElt e ∈ Qx25 ↔ e ∈ Native.d1QD := by
  rw [mem_Qx25, Native.d1QD, List.mem_filter, List.mem_range,
    commute_iff_commRows (glQRows_val he) x25K_val (validM_nfRows _ _) d1Elt_spec.2.1]
  exact ⟨fun h => ⟨he, h.2⟩, fun h => ⟨qElt_mem e, h.2⟩⟩

theorem lt_of_mem_d1QD {e : ℕ} (he : e ∈ Native.d1QD) : e < 512 := by
  rw [Native.d1QD, List.mem_filter, List.mem_range] at he
  exact he.1

theorem natCard_Qx25 :
    Nat.card Qx25 = 128 := by
  have hset : (Qx25 : Set K) = qElt '' (Native.d1QD.toFinset : Set ℕ) := by
    ext g
    rw [Set.mem_image]
    constructor
    · intro hg
      obtain ⟨e, he, rfl⟩ := exists_qElt (mem_Qx25.1 hg).1
      exact ⟨e, by rw [Finset.mem_coe, List.mem_toFinset]; exact (qElt_mem_Qx25_iff he).1 hg,
        rfl⟩
    · rintro ⟨e, he, rfl⟩
      rw [Finset.mem_coe, List.mem_toFinset] at he
      exact (qElt_mem_Qx25_iff (lt_of_mem_d1QD he)).2 he
  have hinj : Set.InjOn qElt (Native.d1QD.toFinset : Set ℕ) := by
    intro e he e' he' h
    rw [Finset.mem_coe, List.mem_toFinset] at he he'
    exact qElt_injOn (lt_of_mem_d1QD he) (lt_of_mem_d1QD he') h
  have hnd : Native.d1QD.Nodup := by
    unfold Native.d1QD
    exact List.nodup_range.filter _
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, hinj.ncard_image,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, d1Elt_spec.2.2.2.2.2.1]

theorem hK_one : hK 1 = δ1hK := rfl

theorem δ1hK_inv_eq_self :
    δ1hK⁻¹ = δ1hK :=
  inv_eq_of_mul_eq_one_right δ1hK_mul_self

theorem mem_F0c_one_iff
    {f : K} :
    f ∈ F0c 1 ↔ ∃ e ∈ Native.d1QD, f = δ1hK * qElt e * δ1hK := by
  constructor
  · rintro ⟨hfC, hfR⟩
    obtain ⟨e, he, rfl⟩ := mem_RK_iff.1 hfR
    rw [hK_one, δ1hK_inv_eq_self] at hfC ⊢
    exact ⟨e, (qElt_mem_Qx25_iff he).1 (mem_Qx25.2 ⟨qElt_mem e,
      conj_δ1hK_comm_z0_iff.1 (comm_of_mem_Cz hfC)⟩), rfl⟩
  · rintro ⟨e, he, rfl⟩
    have hq := (qElt_mem_Qx25_iff (lt_of_mem_d1QD he)).2 he
    refine ⟨conj_δ1hK_mem_Cz_of_Ax25 (Qx25_le_Ax25 hq), mem_RK_iff.2 ⟨e, lt_of_mem_d1QD he, ?_⟩⟩
    rw [hK_one, δ1hK_inv_eq_self]

theorem conj_x25K_δ1hK :
    δ1hK * x25K * δ1hK = z0 := by
  rw [x25K, show δ1hK * (δ1hK * x16K * δ1hK) * δ1hK = (δ1hK * δ1hK) * x16K * (δ1hK * δ1hK) by
    group, δ1hK_mul_self, one_mul, mul_one, x16K_eq]

theorem F0c_one_le_Ax25 :
    F0c 1 ≤ Ax25 := by
  intro f hf
  obtain ⟨e, he, rfl⟩ := mem_F0c_one_iff.1 hf
  have hq := mem_Ax25.1 (Qx25_le_Ax25 ((qElt_mem_Qx25_iff (lt_of_mem_d1QD he)).2 he))
  refine mem_Ax25.2 ⟨hf.1, (comm_conj_iff δ1hK_mul_self).2 ?_⟩
  rw [conj_x25K_δ1hK]
  exact comm_of_mem_Cz hq.1

@[expose] noncomputable def X0g : Subgroup K := Qsub ⊓ RK 1

theorem mem_X0g
    {g : K} : g ∈ X0g ↔ ∃ t < 4, xRootK 0 t = g :=
  mem_Qsub_inf_RK_iff (k := 1) (by decide)

theorem mem_d1X0R {R : Array ℕ} (h : Native.d1X0R.contains R = true) :
    ∃ t < 4, R = Native.glRootRows 0 t := by
  simp only [Native.d1X0R, List.contains_iff_mem, List.mem_map, List.mem_range] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, ht, rfl⟩

theorem d1QD_getD_mem {e : ℕ} (he : e ∈ Native.d1QD) :
    ∃ i < Native.d1QD.length, Native.d1QD.getD i 0 = e := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
  exact ⟨i, hi, by rw [List.getD_eq_getElem]⟩

theorem d1Lam1_spec : ∀ i < Native.d1QD.length,
    Native.d1X0R.contains (Native.glQRows (Native.d1QD.getD i 0)) = true ∨
      (Native.d1Run #[Native.glQRows (Native.d1QD.getD i 0)]
        (Native.d1Lam1.getD i [])).contains Native.glZ = true := by
  have h := d1_parts.2.1
  simp only [Native.d1Lam1OK, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  exact h

theorem d1_lam1
    (S : Subgroup K) (hS : S ≤ Qx25)
    (hinv : ∀ x ∈ S, ∀ j, d1Gk j * x * (d1Gk j)⁻¹ ∈ S) (hz : z0 ∉ S) : S ≤ X0g := by
  intro q hq
  obtain ⟨e, he, rfl⟩ := exists_qElt (mem_Qx25.1 (hS hq)).1
  have heD := (qElt_mem_Qx25_iff he).1 (hS hq)
  obtain ⟨i, hi, hie⟩ := d1QD_getD_mem heD
  rcases d1Lam1_spec i hi with h | h
  · rw [hie] at h
    obtain ⟨t, ht, hR⟩ := mem_d1X0R h
    exact mem_X0g.2 ⟨t, ht, eq_of_val_rows (xRootK_val 0 t) (glQRows_val he) hR.symm⟩
  · exfalso
    rw [hie] at h
    obtain ⟨x, hx, hxv⟩ := d1Run_sound S hinv _ _ (fun R hR => by
      rw [Array.mem_singleton] at hR
      exact ⟨qElt e, hq, hR ▸ glQRows_val he⟩) _ (mem_of_contains h)
    exact hz (eq_of_val_rows hxv z0_val' rfl ▸ hx)

@[expose] noncomputable def B8 : Set K :=
  {g | ∃ t < 4, g = xRootK 0 t ∨ g = x25K * xRootK 0 t}

theorem d1Lam2_spec : ∀ i < Native.d1QD.length,
    Native.d1B8R.contains (Native.d1FR (Native.d1QD.getD i 0)) = true ∨
      ∀ R ∈ Native.d1Tgt, (Native.d1Run #[Native.d1FR (Native.d1QD.getD i 0), Native.glX25]
        (Native.d1Lam2.getD i [])).contains R = true := by
  have h := d1_parts.2.2.1
  simp only [Native.d1Lam2OK, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  exact h

theorem d1Dec_spec : ∀ i < Native.d1QD.length,
    Native.d1DecR (Native.d1Dec.getD i 0) = Native.d1FR (Native.d1QD.getD i 0) := by
  have h := d1_parts.2.2.2.1
  simp only [Native.d1DecOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem d1FR_val {e : ℕ} (he : e < 512) :
    (δ1hK * qElt e * δ1hK).val.val = rowsMatrix 22 (Native.d1FR e) :=
  val_mul3 δ1hK_val (glQRows_val he) δ1hK_val

@[expose] noncomputable def d1DecK (c : ℕ) : K :=
  (if c / 64 == 1 then x25K else 1) * xRootK 0 (c / 16 % 4) * xRootK 4 (c / 4 % 4) *
    xRootK 5 (c % 4)

theorem d1DecK_val (c : ℕ) :
    (d1DecK c).val.val = rowsMatrix 22 (Native.d1DecR c) := by
  have h0 : (if c / 64 == 1 then x25K else 1).val.val =
      rowsMatrix 22 (if c / 64 == 1 then Native.glX25 else idRows 22) := by
    split_ifs
    · exact x25K_val
    · rw [rowsMatrix_idRows]
      rfl
  unfold d1DecK Native.d1DecR
  rw [val_val_mul, val_val_mul, val_val_mul, h0, xRootK_val, xRootK_val, xRootK_val,
    ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows]

theorem xRootK_mem_of_gens
    {S : Subgroup K} {r : ℕ} (hr : r < 12) (h1 : xRootK r 1 ∈ S) (h2 : xRootK r 2 ∈ S) {t : ℕ}
    (ht : t < 4) : xRootK r t ∈ S := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  · simp only [xRootK, beq_self_eq_true, ite_true]
    exact S.one_mem
  · exact h1
  · exact h2
  · have := xRootK_mul (r := r) (s := 1) (t := 2) hr (by decide) (by decide)
    rw [show (1 ^^^ 2 : ℕ) = 3 from rfl] at this
    rw [← this]
    exact S.mul_mem h1 h2

theorem d1_lam2
    (S : Subgroup K) (hS : S ≤ F0c 1)
    (hinv : ∀ x ∈ S, ∀ j, d1Gk j * x * (d1Gk j)⁻¹ ∈ S) (hx : x25K ∈ S) :
    (∀ s ∈ S, s ∈ B8) ∨ F0c 1 ≤ S := by
  by_cases hall : ∀ s ∈ S, s ∈ B8
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨f, hfS, hfB⟩ := hall
  obtain ⟨e, he, rfl⟩ := mem_F0c_one_iff.1 (hS hfS)
  obtain ⟨i, hi, hie⟩ := d1QD_getD_mem he
  have he512 := lt_of_mem_d1QD he
  rcases d1Lam2_spec i hi with h | h
  · exfalso
    apply hfB
    rw [hie] at h
    simp only [Native.d1B8R, List.contains_iff_mem, List.mem_append, Native.d1X0R, List.mem_map,
      List.mem_range] at h
    rcases h with ⟨t, ht, hR⟩ | ⟨R, ⟨t, ht, rfl⟩, hR⟩
    · exact ⟨t, ht, Or.inl (eq_of_val_rows (d1FR_val he512) (xRootK_val 0 t) hR.symm)⟩
    · refine ⟨t, ht, Or.inr (eq_of_val_rows (d1FR_val he512) ?_ hR.symm)⟩
      rw [val_val_mul, x25K_val, xRootK_val, rowsMatrix_mulRows]
  · rw [hie] at h
    have hsound := d1Run_sound S hinv (Native.d1Lam2.getD i [])
      #[Native.d1FR e, Native.glX25] (fun R hR => by
        simp only [Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · exact ⟨_, hfS, d1FR_val he512⟩
        · exact ⟨x25K, hx, x25K_val⟩)
    have hgen : ∀ r t, Native.glRootRows r t ∈ Native.d1Tgt → xRootK r t ∈ S := by
      intro r t hrt
      obtain ⟨x, hxS, hxv⟩ := hsound _ (mem_of_contains (h _ hrt))
      exact eq_of_val_rows hxv (xRootK_val r t) rfl ▸ hxS
    have hX : ∀ r ∈ [0, 4, 5], ∀ t < 4, xRootK r t ∈ S := by
      intro r hr t ht
      have hr' : r = 0 ∨ r = 4 ∨ r = 5 := by simpa using hr
      refine xRootK_mem_of_gens (by omega) (hgen r 1 ?_) (hgen r 2 ?_) ht <;>
        rcases hr' with rfl | rfl | rfl <;> simp [Native.d1Tgt]
    intro f' hf'
    obtain ⟨e', he', rfl⟩ := mem_F0c_one_iff.1 hf'
    obtain ⟨i', hi', hie'⟩ := d1QD_getD_mem he'
    have hdec := d1Dec_spec i' hi'
    rw [hie'] at hdec
    have hfe : δ1hK * qElt e' * δ1hK = d1DecK (Native.d1Dec.getD i' 0) :=
      eq_of_val_rows (d1FR_val (lt_of_mem_d1QD he')) (d1DecK_val _) hdec.symm
    rw [hfe, d1DecK]
    have h0 : (if Native.d1Dec.getD i' 0 / 64 == 1 then x25K else 1) ∈ S := by
      split_ifs
      · exact hx
      · exact S.one_mem
    exact S.mul_mem (S.mul_mem (S.mul_mem h0 (hX 0 (by simp) _ (Nat.mod_lt _ (by norm_num))))
      (hX 4 (by simp) _ (Nat.mod_lt _ (by norm_num))))
      (hX 5 (by simp) _ (Nat.mod_lt _ (by norm_num)))

end CFSG.Sporadic.Co2Smith
