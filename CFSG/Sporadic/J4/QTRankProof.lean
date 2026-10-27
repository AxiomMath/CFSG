module

public import CFSG.Sporadic.J4.QTProof
public import CFSG.Sporadic.J4.QTRankCheck

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
open scoped Pointwise

theorem rowsXor_of_zero (r : ℕ → ℕ) (m : ℕ) : rowsXor r m 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [rowsXor_succ, ih]; simp

theorem rowsXor_xor (r : ℕ → ℕ) (m c d : ℕ) :
    rowsXor r m (c ^^^ d) = rowsXor r m c ^^^ rowsXor r m d := by
  induction m with
  | zero => simp [rowsXor_zero]
  | succ m ih =>
    rw [rowsXor_succ, rowsXor_succ, rowsXor_succ, ih, Nat.testBit_xor]
    cases hc : c.testBit m <;> cases hd : d.testBit m <;> simp
    · exact Nat.xor_assoc _ _ _
    · exact Nat.xor_right_comm _ _ _
    · rw [Nat.xor_assoc, ← Nat.xor_assoc (r m), Nat.xor_comm (r m), Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero]

theorem rowsXor_congr {r r' : ℕ → ℕ} {m : ℕ} (h : ∀ j < m, r j = r' j) (c : ℕ) :
    rowsXor r m c = rowsXor r' m c := by
  induction m with
  | zero => simp [rowsXor_zero]
  | succ m ih => rw [rowsXor_succ, rowsXor_succ, ih (fun j hj => h j (by omega)), h m (by omega)]

theorem rowsXor_two_pow (r : ℕ → ℕ) {j : ℕ} : ∀ m, rowsXor r m (2 ^ j) = if j < m then r j else 0
  | 0 => by simp [rowsXor_zero]
  | m + 1 => by
    rw [rowsXor_succ, rowsXor_two_pow r m, Nat.testBit_two_pow]
    by_cases h1 : j = m
    · subst h1; simp
    · by_cases h2 : j < m
      · simp [h1, h2, show j < m + 1 by omega]
      · simp [h1, h2, show ¬ j < m + 1 by omega]

theorem rowsXor_pow_two (c : ℕ) : ∀ m, rowsXor (fun j => 2 ^ j) m c = c % 2 ^ m := by
  intro m
  induction m with
  | zero => rw [rowsXor_zero, pow_zero, Nat.mod_one]
  | succ m ih =>
    rw [rowsXor_succ, ih]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
    by_cases hb : c.testBit m
    · rcases lt_trichotomy i m with h | h | h
      · simp [hb, h, show m ≠ i by omega, show i < m + 1 by omega]
      · subst h; simp [hb]
      · simp [hb, show ¬ i < m by omega, show m ≠ i by omega,
          show ¬ i < m + 1 by omega]
    · simp only [hb]
      rcases lt_trichotomy i m with h | h | h
      · simp [h, show i < m + 1 by omega]
      · subst h; simp [hb]
      · simp [show ¬ i < m by omega, show ¬ i < m + 1 by omega]

theorem actT_zero (t : List ℕ) : actT t 0 = 0 := rowsXor_of_zero _ _

theorem actT_xor (t : List ℕ) (c d : ℕ) : actT t (c ^^^ d) = actT t c ^^^ actT t d :=
  rowsXor_xor _ _ _ _

theorem actT_rowsXor (t : List ℕ) (r : ℕ → ℕ) (m c : ℕ) :
    actT t (rowsXor r m c) = rowsXor (fun j => actT t (r j)) m c := by
  induction m with
  | zero => simp [rowsXor_zero, actT_zero]
  | succ m ih =>
    rw [rowsXor_succ, rowsXor_succ, actT_xor, ih]
    congr 1
    split_ifs <;> simp [actT_zero]

theorem getD_compT (t t' : List ℕ) (j : ℕ) : (compT t t').getD j 0 = actT t (t'.getD j 0) := by
  have := List.getD_map t' 0 (n := j) (actT t)
  rw [actT_zero] at this
  exact this

theorem actT_comp (t t' : List ℕ) (c : ℕ) : actT (compT t t') c = actT t (actT t' c) := by
  have h : (fun j => (compT t t').getD j 0) = fun j => actT t (t'.getD j 0) :=
    funext (getD_compT t t')
  show rowsXor (fun j => (compT t t').getD j 0) 11 c = actT t (rowsXor (fun j => t'.getD j 0) 11 c)
  rw [actT_rowsXor, h]

theorem rowsXor_lt {r : ℕ → ℕ} {m : ℕ} (h : ∀ j < m, r j < 2 ^ 11) (hm : m ≤ 11) (c : ℕ) :
    rowsXor r m c < 2 ^ 11 := by
  induction m with
  | zero => simp [rowsXor_zero]
  | succ m ih =>
    rw [rowsXor_succ]
    refine Nat.xor_lt_two_pow (ih (fun j hj => h j (by omega)) (by omega)) ?_
    split_ifs
    · exact h m (by omega)
    · exact Nat.two_pow_pos 11

theorem lenOK_iff {t : List ℕ} (h : lenOK t = true) : t.length = 11 ∧ ∀ x ∈ t, x < 2 ^ 11 := by
  unfold lenOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun x hx => by simpa using h.2 x hx⟩

theorem lenOK_of {t : List ℕ} (h1 : t.length = 11) (h2 : ∀ x ∈ t, x < 2 ^ 11) : lenOK t = true := by
  unfold lenOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  exact ⟨h1, fun x hx => by simpa using h2 x hx⟩

theorem actT_lt {t : List ℕ} (ht : lenOK t = true) (c : ℕ) : actT t c < 2 ^ 11 := by
  obtain ⟨hl, hx⟩ := lenOK_iff ht
  refine rowsXor_lt (fun j hj => ?_) le_rfl c
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hx _ (List.getElem_mem _)

theorem lenOK_compT {t t' : List ℕ} (ht : lenOK t = true) (ht' : lenOK t' = true) :
    lenOK (compT t t') = true := by
  obtain ⟨hl, hx⟩ := lenOK_iff ht'
  exact lenOK_of (by simp [compT, hl]) (fun x hx' => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx'
    exact actT_lt ht y)

theorem actT_two_pow (t : List ℕ) {j : ℕ} (hj : j < 11) : actT t (2 ^ j) = t.getD j 0 := by
  unfold actT
  rw [rowsXor_two_pow]
  simp [hj]

theorem idT_getD {j : ℕ} (hj : j < 11) : idT.getD j 0 = 2 ^ j := by
  unfold idT
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem actT_idT {c : ℕ} (hc : c < 2 ^ 11) : actT idT c = c := by
  have : actT idT c = rowsXor (fun j => 2 ^ j) 11 c := by
    unfold actT
    apply rowsXor_congr
    intro j hj
    exact idT_getD hj
  rw [this, rowsXor_pow_two, Nat.mod_eq_of_lt hc]


@[expose] def Acts (g : J) (t : List ℕ) : Prop :=
  lenOK t = true ∧ ∀ c < 2 ^ 11, g * eta uJ 11 c * g⁻¹ = eta uJ 11 (actT t c)

theorem lenOK_idT : lenOK idT = true := by decide

theorem Acts.mul {g g' : J} {t t' : List ℕ} (h : Acts g t) (h' : Acts g' t') :
    Acts (g * g') (compT t t') := by
  refine ⟨lenOK_compT h.1 h'.1, fun c hc => ?_⟩
  have e : g * g' * eta uJ 11 c * (g * g')⁻¹ = g * (g' * eta uJ 11 c * g'⁻¹) * g⁻¹ := by group
  rw [e, h'.2 c hc, h.2 _ (actT_lt h'.1 c), actT_comp]

theorem Acts.one : Acts 1 idT := by
  refine ⟨lenOK_idT, fun c hc => ?_⟩
  rw [actT_idT hc]
  group

section WithFacts

variable (hM : MatFacts)
include hM

theorem Acts.of_mem_Eg {g : J} (hg : g ∈ Eg uJ 11) : Acts g idT := by
  refine ⟨lenOK_idT, fun c hc => ?_⟩
  rw [actT_idT hc]
  have h1 : g * eta uJ 11 c = eta uJ 11 c * g := Eg_comm (elem_uJ hM) hg (eta_mem_Eg 11 le_rfl c)
  rw [h1]
  group

theorem Acts.mul_of_mem_Eg {g n : J} {t : List ℕ} (h : Acts g t) (hn : n ∈ Eg uJ 11) :
    Acts (g * n) t := by
  refine ⟨h.1, fun c hc => ?_⟩
  have h1 : n * eta uJ 11 c = eta uJ 11 c * n := Eg_comm (elem_uJ hM) hn (eta_mem_Eg 11 le_rfl c)
  have e : g * n * eta uJ 11 c * (g * n)⁻¹ = g * (n * eta uJ 11 c * n⁻¹) * g⁻¹ := by group
  have e2 : n * eta uJ 11 c * n⁻¹ = eta uJ 11 c := by rw [h1]; group
  rw [e, e2, h.2 c hc]

theorem Acts.unique {g : J} {t t' : List ℕ} (h : Acts g t) (h' : Acts g t') : t = t' := by
  obtain ⟨hl, hx⟩ := lenOK_iff h.1
  obtain ⟨hl', hx'⟩ := lenOK_iff h'.1
  apply List.ext_getElem (by omega)
  intro j hj hj'
  have hj11 : j < 11 := by omega
  have e1 := h.2 (2 ^ j) (Nat.pow_lt_pow_right (by norm_num) hj11)
  have e2 := h'.2 (2 ^ j) (Nat.pow_lt_pow_right (by norm_num) hj11)
  rw [e1, actT_two_pow t hj11] at e2
  rw [actT_two_pow t' hj11] at e2
  have hlt : t.getD j 0 < 2 ^ 11 := by
    rw [List.getD_eq_getElem _ _ hj]; exact hx _ (List.getElem_mem _)
  have hlt' : t'.getD j 0 < 2 ^ 11 := by
    rw [List.getD_eq_getElem _ _ hj']; exact hx' _ (List.getElem_mem _)
  have := eta_inj hM _ hlt _ hlt' e2
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at this
  exact this

end WithFacts

@[expose] noncomputable def kJ (i : ℕ) : J := wordProd xJ (kWords.getD i [])

theorem actT_letterTab (ℓ : ℤ) (c : ℕ) : actT (letterTab ℓ) c = act ℓ c := by
  unfold actT act
  apply rowsXor_congr
  intro j hj
  unfold letterTab
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem XJ_neg_of_mem {ℓ : ℤ} (hℓ : ℓ ∈ letters) : XJ (-ℓ) = (XJ ℓ)⁻¹ := (XJ_inv hℓ).2

theorem wordProd_invWord : ∀ w : List ℤ, (∀ ℓ ∈ w, ℓ ∈ letters) →
    wordProd xJ (invWord w) = (wordProd xJ w)⁻¹
  | [], _ => by simp [wordProd, invWord]
  | ℓ :: w, h => by
    have h1 := wordProd_invWord w (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 : invWord (ℓ :: w) = invWord w ++ [-ℓ] := by simp [invWord]
    rw [h2, wordProd_xJ, List.map_append, List.prod_append, ← wordProd_xJ, h1]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, wordProd_xJ]
    rw [XJ_neg_of_mem (h ℓ (List.mem_cons_self ..)), mul_inv_rev]

theorem kJ_letters {i : ℕ} (hi : i < 4) : ∀ ℓ ∈ kWords.getD i [], ℓ ∈ letters :=
  kWords_letters i hi

theorem kJ_mem {i : ℕ} (hi : i < 4) : kJ i ∈ Hj := wordProd_mem_Hj (kJ_letters hi)

section WithFacts2

variable (hM : MatFacts)
include hM

theorem Acts_XJ {ℓ : ℤ} (hℓ : ℓ ∈ letters) : Acts (XJ ℓ) (letterTab ℓ) := by
  refine ⟨letterTab_ok ℓ hℓ, fun c _ => ?_⟩
  rw [actT_letterTab]
  exact hX_all hM hℓ c

theorem Acts_wordProd : ∀ w : List ℤ, (∀ ℓ ∈ w, ℓ ∈ letters) →
    Acts (wordProd xJ w) (wordT w)
  | [], _ => by simpa [wordProd, wordT] using Acts.one
  | ℓ :: w, h => by
    have := (Acts_XJ hM (h ℓ (List.mem_cons_self ..))).mul
      (Acts_wordProd w (fun x hx => h x (List.mem_cons_of_mem _ hx)))
    simpa [wordProd_xJ, wordT] using this

theorem Acts_kJ {i : ℕ} (hi : i < 4) : Acts (kJ i) (kTab i) :=
  Acts_wordProd hM _ (kJ_letters hi)

theorem Acts_kJ_inv {i : ℕ} (hi : i < 4) : Acts (kJ i)⁻¹ (kInvTab i) := by
  have := Acts_wordProd hM (invWord (kWords.getD i [])) (fun ℓ hℓ => by
    simp only [invWord, List.mem_map, List.mem_reverse] at hℓ
    obtain ⟨x, hx, rfl⟩ := hℓ
    exact letters_neg x (kJ_letters hi x hx))
  rwa [wordProd_invWord _ (kJ_letters hi), ← kJ] at this

end WithFacts2

@[expose] noncomputable def Kel (e : ℕ) : J := ((pcSeq e).map kJ).prod

@[expose] def S0 : Set J := {g | (∃ j < 11, g = uJ j) ∨ ∃ i < 4, g = kJ i}

noncomputable abbrev P0 : Subgroup J := Subgroup.closure S0

theorem kJ_mem_P0 {i : ℕ} (hi : i < 4) : kJ i ∈ P0 := Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)

theorem Kel_mem_P0 {e : ℕ} (he : e < 1024) : Kel e ∈ P0 := by
  unfold Kel
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact kJ_mem_P0 (pcSeq_lt e he i hi)

theorem Eg_le_P0 : Eg uJ 11 ≤ P0 := by
  rw [Eg, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact Subgroup.subset_closure (Or.inl ⟨j, hj, rfl⟩)

theorem P0_le_Hj : P0 ≤ Hj := by
  rw [Subgroup.closure_le]
  rintro _ (⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩)
  · exact uJ_mem hj
  · exact kJ_mem hi

theorem Kel_mem_Hj {e : ℕ} (he : e < 1024) : Kel e ∈ Hj := P0_le_Hj (Kel_mem_P0 he)

theorem eta_mul_Kel_mem {c e : ℕ} (he : e < 1024) : eta uJ 11 c * Kel e ∈ P0 :=
  P0.mul_mem (Eg_le_P0 (eta_mem_Eg 11 le_rfl c)) (Kel_mem_P0 he)

section WithFacts3

variable (hM : MatFacts)
include hM

theorem Acts_prod_seq : ∀ s : List ℕ, (∀ i ∈ s, i < 4) → Acts ((s.map kJ).prod) (seqT s)
  | [], _ => by simpa [seqT] using Acts.one
  | i :: s, h => by
    have := (Acts_kJ hM (h i (List.mem_cons_self ..))).mul
      (Acts_prod_seq s (fun x hx => h x (List.mem_cons_of_mem _ hx)))
    simpa [seqT] using this

theorem Acts_Kel {e : ℕ} (he : e < 1024) : Acts (Kel e) (seqT (pcSeq e)) :=
  Acts_prod_seq hM _ (pcSeq_lt e he)

theorem table_of_mem : ∀ g ∈ P0, ∃ t ∈ tabL, Acts g t := by
  intro g hg
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨idT, idT_mem, Acts.one⟩
  | mul_right x hx y hy ih =>
    obtain ⟨t, ht, hxt⟩ := ih
    rcases hy with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · exact ⟨t, ht, hxt.mul_of_mem_Eg hM (u_mem_Eg hj)⟩
    · exact ⟨_, (tabL_closed t ht i hi).1, hxt.mul (Acts_kJ hM hi)⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨t, ht, hxt⟩ := ih
    rcases hy with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · exact ⟨t, ht, hxt.mul_of_mem_Eg hM ((Eg uJ 11).inv_mem (u_mem_Eg hj))⟩
    · exact ⟨_, (tabL_closed t ht i hi).2, hxt.mul (Acts_kJ_inv hM hi)⟩

theorem Acts.eta_mul {g : J} {t : List ℕ} (h : Acts g t) {n : J} (hn : n ∈ Eg uJ 11) :
    Acts (n * g) t := by
  refine ⟨h.1, fun c hc => ?_⟩
  have h1 : n * eta uJ 11 (actT t c) = eta uJ 11 (actT t c) * n :=
    Eg_comm (elem_uJ hM) hn (eta_mem_Eg 11 le_rfl _)
  have e : n * g * eta uJ 11 c * (n * g)⁻¹ = n * (g * eta uJ 11 c * g⁻¹) * n⁻¹ := by group
  rw [e, h.2 c hc, h1]
  group

theorem exists_eta_mul_Kel (hF : J4Facts) {g : J} (hg : g ∈ P0) :
    ∃ c < 2 ^ 11, ∃ e < 1024, g = eta uJ 11 c * Kel e := by
  obtain ⟨t, ht, hgt⟩ := table_of_mem hM g hg
  obtain ⟨e, he, rfl⟩ : ∃ e < 1024, seqT (pcSeq e) = t := by
    unfold tabL at ht
    simpa [List.mem_map, List.mem_range] using ht
  have hK := Acts_Kel hM he
  have hmem : (Kel e)⁻¹ * g ∈ Hj := Hj.mul_mem (Hj.inv_mem (Kel_mem_Hj he)) (P0_le_Hj hg)
  have hcomm : ∀ y ∈ Eg uJ 11, (Kel e)⁻¹ * g * y = y * ((Kel e)⁻¹ * g) := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    have hg1 := hgt.2 d hd
    have hK1 := hK.2 d hd
    calc (Kel e)⁻¹ * g * eta uJ 11 d
        = (Kel e)⁻¹ * (g * eta uJ 11 d * g⁻¹) * g := by group
      _ = (Kel e)⁻¹ * (Kel e * eta uJ 11 d * (Kel e)⁻¹) * g := by rw [hg1, hK1]
      _ = eta uJ 11 d * ((Kel e)⁻¹ * g) := by group
  obtain ⟨c0, hc0, hc0e⟩ := (mem_Eg_iff (elem_uJ hM)).1 (centralizer_Hj hM hF _ hmem hcomm)
  refine ⟨actT (seqT (pcSeq e)) c0, actT_lt hK.1 c0, e, he, ?_⟩
  have hg' : g = Kel e * eta uJ 11 c0 := by
    rw [← hc0e]; group
  rw [hg']
  calc Kel e * eta uJ 11 c0 = (Kel e * eta uJ 11 c0 * (Kel e)⁻¹) * Kel e := by group
    _ = eta uJ 11 (actT (seqT (pcSeq e)) c0) * Kel e := by rw [hK.2 c0 hc0]

theorem Acts_eta_mul_Kel {c e : ℕ} (he : e < 1024) :
    Acts (eta uJ 11 c * Kel e) (seqT (pcSeq e)) :=
  (Acts_Kel hM he).eta_mul hM (eta_mem_Eg 11 le_rfl c)

theorem Kel_inj {e e' : ℕ} (he : e < 1024) (he' : e' < 1024) {c c' : ℕ}
    (h : eta uJ 11 c * Kel e = eta uJ 11 c' * Kel e') (hc : c < 2 ^ 11) (hc' : c' < 2 ^ 11) :
    c = c' ∧ e = e' := by
  have h1 := Acts_eta_mul_Kel hM (c := c) he
  have h2 := Acts_eta_mul_Kel hM (c := c') he'
  rw [h] at h1
  have hT := h1.unique hM h2
  have hnd := tabL_nodup
  unfold tabL at hnd
  have hee := List.inj_on_of_nodup_map hnd (List.mem_range.2 he) (List.mem_range.2 he') hT
  subst hee
  refine ⟨?_, rfl⟩
  have : eta uJ 11 c = eta uJ 11 c' := mul_right_cancel h
  exact eta_inj hM c hc c' hc' this

@[expose] noncomputable def sylowFun (p : Fin (2 ^ 11) × Fin 1024) : P0 :=
  ⟨eta uJ 11 p.1 * Kel p.2, eta_mul_Kel_mem p.2.2⟩

theorem sylowFun_bijective (hF : J4Facts) : Function.Bijective sylowFun := by
  constructor
  · intro p q h
    have h' := congrArg Subtype.val h
    simp only [sylowFun] at h'
    have := Kel_inj hM p.2.2 q.2.2 h' p.1.2 q.1.2
    exact Prod.ext (Fin.ext this.1) (Fin.ext this.2)
  · rintro ⟨g, hg⟩
    obtain ⟨c, hc, e, he, rfl⟩ := exists_eta_mul_Kel hM hF hg
    exact ⟨(⟨c, hc⟩, ⟨e, he⟩), rfl⟩

theorem card_P0 (hF : J4Facts) : Nat.card P0 = 2 ^ 21 := by
  rw [← Nat.card_congr (Equiv.ofBijective sylowFun (sylowFun_bijective hM hF)), Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

end WithFacts3

theorem natCard_mem_le (L : List ℕ) : Nat.card {c : ℕ // c ∈ L} ≤ L.length := by
  classical
  have h1 : Nat.card {c : ℕ // c ∈ L} = Nat.card ↥L.toFinset :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => (List.mem_toFinset).symm)
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact List.toFinset_card_le L

section Rank

variable (hM : MatFacts)
include hM

theorem card_inf_le {A : Subgroup J} {x : J}
    (hcomm : ∀ y ∈ A, x * y = y * x) {t : List ℕ} (hxt : Acts x t) (hfix : fixCount t ≤ 128) :
    Nat.card ↥(Eg uJ 11 ⊓ A) ≤ 128 := by
  classical
  let L : List ℕ := (List.range 2048).filter fun c => actT t c == c
  have hL : L.length = fixCount t := rfl
  have key : ∀ y : ↥(Eg uJ 11 ⊓ A), ∃ c, c < 2 ^ 11 ∧ (y : J) = eta uJ 11 c ∧ actT t c = c := by
    intro y
    obtain ⟨c, hc, hyc⟩ := (mem_Eg_iff (elem_uJ hM)).1 y.2.1
    refine ⟨c, hc, hyc, ?_⟩
    have h1 := hcomm y y.2.2
    have h2 := hxt.2 c hc
    rw [← hyc] at h2
    have h3 : x * (y : J) * x⁻¹ = y := by rw [h1]; group
    rw [h3, hyc] at h2
    exact (eta_inj hM _ (actT_lt hxt.1 c) _ hc h2.symm)
  choose f hf1 hf2 hf3 using key
  let g : ↥(Eg uJ 11 ⊓ A) → {c : ℕ // c ∈ L} := fun y =>
    ⟨f y, by
      simp only [L, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨by have := hf1 y; omega, hf3 y⟩⟩
  have hg : Function.Injective g := by
    intro y z h
    have h' : f y = f z := congrArg Subtype.val h
    apply Subtype.ext
    rw [hf2 y, hf2 z, h']
  calc Nat.card ↥(Eg uJ 11 ⊓ A) ≤ Nat.card {c : ℕ // c ∈ L} := Nat.card_le_card_of_injective g hg
    _ ≤ L.length := natCard_mem_le L
    _ ≤ 128 := by rw [hL]; exact hfix

theorem relIndex_Eg_P0 (hF : J4Facts) : (Eg uJ 11).relIndex P0 = 2 ^ 10 := by
  have h1 := Subgroup.relIndex_mul_card (H := Eg uJ 11) (K := P0)
  rw [inf_eq_left.2 (Eg_le_P0), card_Eg_uJ hM] at h1
  rw [card_P0 hM hF] at h1
  have : (2 : ℕ) ^ 21 = 2 ^ 10 * 2 ^ 11 := by norm_num
  rw [this] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 11) h1

theorem card_le_of_le_P0 (hF : J4Facts) {A : Subgroup J} (hA : A ≤ P0)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 2 ^ 17 := by
  by_cases hAN : A ≤ Eg uJ 11
  · calc Nat.card A ≤ Nat.card (Eg uJ 11) := Subgroup.card_le_of_le hAN
      _ = 2 ^ 11 := card_Eg_uJ hM
      _ ≤ 2 ^ 17 := by norm_num
  · obtain ⟨x, hxA, hxN⟩ : ∃ x ∈ A, x ∉ Eg uJ 11 := by
      by_contra hcon
      apply hAN
      intro x hx
      by_contra hxN
      exact hcon ⟨x, hx, hxN⟩
    obtain ⟨t, htL, hxt⟩ := table_of_mem hM x (hA hxA)
    have h1 : compT t t = idT := by
      have h := hxt.mul hxt
      rw [hsq x hxA] at h
      exact h.unique hM Acts.one
    have h2 : t ≠ idT := by
      intro ht
      subst ht
      apply hxN
      refine centralizer_Hj hM hF x (P0_le_Hj (hA hxA)) (fun y hy => ?_)
      obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
      have := hxt.2 c hc
      rw [actT_idT hc] at this
      calc x * eta uJ 11 c = (x * eta uJ 11 c * x⁻¹) * x := by group
        _ = eta uJ 11 c * x := by rw [this]
    have hfix := fixCount_le t htL h1 h2
    have hAE := card_inf_le hM (fun y hy => hcomm x hxA y hy) hxt hfix
    have hrel : (Eg uJ 11).relIndex A ≤ 2 ^ 10 := by
      rw [← relIndex_Eg_P0 hM hF]
      exact Subgroup.relIndex_le_of_le_right hA (by rw [relIndex_Eg_P0 hM hF]; positivity)
    have hmul := Subgroup.relIndex_mul_card (H := Eg uJ 11) (K := A)
    calc Nat.card A = (Eg uJ 11).relIndex A * Nat.card ↥(Eg uJ 11 ⊓ A) := hmul.symm
      _ ≤ 2 ^ 10 * 128 := Nat.mul_le_mul hrel hAE
      _ = 2 ^ 17 := by norm_num

end Rank

theorem card_J_factorization (hF : J4Facts) : (Nat.card J).factorization 2 = 21 := by
  rw [card_J hF]
  have h : (86775571046077562880 : ℕ) = 2 ^ 21 * 41377816699065 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem exists_conj_le_P0 (hM : MatFacts) (hF : J4Facts) (A : Subgroup J) (hpA : IsPGroup 2 A) :
    ∃ g : J, ∀ x ∈ A, g⁻¹ * x * g ∈ P0 := by
  obtain ⟨Q, hAQ⟩ := hpA.exists_le_sylow
  let P : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P Q
  have hQ : (Q : Subgroup J) = MulAut.conj g • P0 := by
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ MulAut.conj g • P0 := by rw [← hQ]; exact hAQ hx
  obtain ⟨s, hs, hsx⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) P0).1 hxQ
  have : g⁻¹ * x * g = s := by
    rw [← hsx]
    simp only [MulAut.smul_def, MulAut.conj_apply]
    group
  rw [this]
  exact hs

theorem card_le_two_pow_seventeen (hM : MatFacts) (hF : J4Facts) (A : Subgroup J)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 2 ^ 17 := by
  have hpA : IsPGroup 2 A := fun x => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (hsq x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_P0 hM hF A hpA
  let φ : J →* J := (MulAut.conj g⁻¹).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.conj g⁻¹).injective
  have hle : A.map φ ≤ P0 := by
    rintro _ ⟨x, hx, rfl⟩
    have : φ x = g⁻¹ * x * g := by
      simp only [φ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [this]
    exact hg x hx
  have hc' : ∀ x ∈ A.map φ, ∀ y ∈ A.map φ, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hs' : ∀ x ∈ A.map φ, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]
  have := card_le_of_le_P0 hM hF hle hc' hs'
  rwa [Subgroup.card_map_of_injective hφ] at this

end CFSG.Sporadic.J4.QT
