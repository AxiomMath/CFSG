module

public import CFSG.Monster.B.Classical.E6FoldedData

public noncomputable section

namespace CFSG.Monster.B.Classical.E6Folded

theorem getD_ofFn {n : ℕ} (f : Fin n → ℤ) (j : Fin n) : (List.ofFn f).getD j 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem ofFn_pv {a : ℕ} (ha : a < 24) : List.ofFn (pv a) = ptList.getD a [] := by
  have hmem : ptList.getD a [] ∈ ptList := by
    rw [List.getD_eq_getElem _ _ (by rw [ptList_length]; exact ha)]
    exact List.getElem_mem _
  have hlen := ptList_lengths _ hmem
  refine List.ext_getElem (by rw [List.length_ofFn, hlen]) fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, pv]
  exact List.getD_eq_getElem _ _ h₂

theorem pv_of_ofFn {v : Fin 6 → ℤ} {b : ℕ} (h : List.ofFn v = ptList.getD b []) : pv b = v := by
  funext j
  rw [pv, ← h, getD_ofFn]

theorem pv_23 : pv 23 = θ := pv_of_ofFn theta_eq

theorem r_pv_eq (k : Fin 4) {a : ℕ} (ha : a < 24) : r k (pv a) = pv (gidx k a) :=
  (pv_of_ofFn (r_pv k a ha).2).symm

theorem gidx_lt (k : Fin 4) {a : ℕ} (ha : a < 24) : gidx k a < 24 := (r_pv k a ha).1

theorem wordIdx_lt_and_mem (l : List (Fin 4)) {x : ℕ} (hx : x < 24) (h : InOrbit (pv x)) :
    wordIdx l x < 24 ∧ InOrbit (pv (wordIdx l x)) := by
  induction l with
  | nil => exact ⟨hx, h⟩
  | cons k l ih =>
    obtain ⟨hy, hmem⟩ := ih
    refine ⟨gidx_lt k hy, ?_⟩
    change InOrbit (pv (gidx k (wordIdx l x)))
    rw [← r_pv_eq k hy]
    exact .step k hmem

theorem inOrbit_pv {a : ℕ} (ha : a < 24) : InOrbit (pv a) := by
  have h := (wordIdx_lt_and_mem (tWords.getD a []) (x := 23) (by norm_num)
    (by rw [pv_23]; exact .base)).2
  rwa [wordIdx_tWords a ha] at h

theorem exists_pv_eq {v : Fin 6 → ℤ} (hv : InOrbit v) : ∃ a < 24, pv a = v := by
  induction hv with
  | base => exact ⟨23, by norm_num, pv_23⟩
  | step k _ ih =>
    obtain ⟨a, ha, rfl⟩ := ih
    exact ⟨gidx k a, gidx_lt k ha, (r_pv_eq k ha).symm⟩

theorem pv_inj {a b : ℕ} (ha : a < 24) (hb : b < 24) (h : pv a = pv b) : a = b := by
  have h' : ptList.getD a [] = ptList.getD b [] := by
    rw [← ofFn_pv ha, ← ofFn_pv hb, h]
  rw [List.getD_eq_getElem _ _ (by rw [ptList_length]; exact ha),
    List.getD_eq_getElem _ _ (by rw [ptList_length]; exact hb)] at h'
  exact (ptList_nodup.getElem_inj_iff).1 h'

@[expose] def ι : Fin 24 ≃ Λ :=
  Equiv.ofBijective (fun a => ⟨pv a, inOrbit_pv a.2⟩)
    ⟨fun a b h => Fin.ext (pv_inj a.2 b.2 (congrArg Subtype.val h)), fun v => by
      obtain ⟨a, ha, hv⟩ := exists_pv_eq v.2
      exact ⟨⟨a, ha⟩, Subtype.ext hv⟩⟩

theorem ι_apply (a : Fin 24) : (ι a).1 = pv a := rfl

theorem ι_23 : ι 23 = θΛ := Subtype.ext pv_23

theorem gen_ι (k : Fin 4) (a : Fin 24) : gen k (ι a) = ι ⟨gidx k a, gidx_lt k a.2⟩ :=
  Subtype.ext (r_pv_eq k a.2)

theorem card_Λ : Nat.card Λ = 24 := by
  rw [← Nat.card_congr ι, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def code (w : Equiv.Perm Λ) : List ℕ :=
  List.ofFn fun a : Fin 24 => (ι.symm (w (ι a)) : ℕ)

theorem code_length (w : Equiv.Perm Λ) : (code w).length = 24 := by simp [code]

theorem code_getD (w : Equiv.Perm Λ) (a : Fin 24) : (code w).getD a 0 = ι.symm (w (ι a)) := by
  rw [code, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem code_getD_lt (w : Equiv.Perm Λ) {a : ℕ} (ha : a < 24) : (code w).getD a 0 < 24 := by
  rw [code_getD w ⟨a, ha⟩]
  exact (ι.symm _).2

theorem apply_ι (w : Equiv.Perm Λ) (a : Fin 24) :
    w (ι a) = ι ⟨(code w).getD a 0, code_getD_lt w a.2⟩ := by
  rw [← ι.apply_symm_apply (w (ι a))]
  congr 1
  exact Fin.ext (code_getD w a).symm

theorem apply_ι_eq_iff (w : Equiv.Perm Λ) (a b : Fin 24) :
    w (ι a) = ι b ↔ (code w).getD a 0 = b := by
  rw [apply_ι, ι.apply_eq_iff_eq, Fin.ext_iff]

theorem code_injective : Function.Injective code := by
  intro w w' h
  refine Equiv.ext fun x => ?_
  obtain ⟨a, rfl⟩ := ι.surjective x
  rw [apply_ι, apply_ι]
  congr 2
  rw [h]

theorem code_mul (x y : Equiv.Perm Λ) : code (x * y) = compose (code x) (code y) := by
  refine List.ext_getElem (by simp [compose, code_length]) fun n h₁ h₂ => ?_
  have hn : n < 24 := by simpa [code_length] using h₁
  simp only [compose, List.getElem_map]
  rw [← List.getD_eq_getElem _ 0 h₁,
    ← List.getD_eq_getElem (code y) 0 (by rw [code_length]; exact hn)]
  rw [code_getD (x * y) ⟨n, hn⟩, code_getD y ⟨n, hn⟩, code_getD x (ι.symm (y (ι ⟨n, hn⟩))),
    ι.apply_symm_apply, Equiv.Perm.mul_apply]

theorem code_one : code 1 = idCode := by
  refine List.ext_getElem (by simp [code_length, idCode]) fun n h₁ h₂ => ?_
  have hn : n < 24 := by simpa [code_length] using h₁
  rw [← List.getD_eq_getElem _ 0 h₁, code_getD 1 ⟨n, hn⟩]
  simp [idCode]

theorem code_gen (k : Fin 4) : code (gen k) = gc k := by
  refine List.ext_getElem (by simp [code_length, gc_length]) fun n h₁ h₂ => ?_
  have hn : n < 24 := by simpa [code_length] using h₁
  rw [← List.getD_eq_getElem _ 0 h₁, ← List.getD_eq_getElem _ 0 h₂, code_getD _ ⟨n, hn⟩,
    gen_ι, ι.symm_apply_apply]
  rfl

theorem code_wordProd (l : List (Fin 4)) : code (wordProd l) = codeWord l := by
  induction l with
  | nil => exact code_one
  | cons k l ih => rw [wordProd_cons, code_mul, ih, code_gen]; rfl

theorem mem_closure_iff_of_list {S : Set (Fin 4)} {ws : List (List (Fin 4))} {cs : List (List ℕ)}
    (hlen : ws.length = cs.length)
    (hcode : ∀ i < cs.length, codeWord (ws.getD i []) = cs.getD i [])
    (hletters : ∀ l ∈ ws, ∀ k ∈ l, k ∈ S) (hone : idCode ∈ cs)
    (hclosed : ∀ i < cs.length, ∀ k ∈ S, compose (gc k) (cs.getD i []) ∈ cs)
    (w : Equiv.Perm Λ) : w ∈ Subgroup.closure (gen '' S) ↔ code w ∈ cs := by
  have hstep : ∀ k ∈ S, ∀ y : Equiv.Perm Λ, code y ∈ cs → code (gen k * y) ∈ cs := by
    intro k hk y hy
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy
    rw [code_mul, code_gen, ← hiy, ← List.getD_eq_getElem _ [] hi]
    exact hclosed i hi k hk
  constructor
  · intro hw
    induction hw using Subgroup.closure_induction_left with
    | one => rw [code_one]; exact hone
    | mul_left x hx y _ ih =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hstep k hk y ih
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [gen_inv]
      exact hstep k hk y ih
  · intro hw
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hw
    have hwi : ws.getD i [] ∈ ws := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have : wordProd (ws.getD i []) = w := by
      apply code_injective
      rw [code_wordProd, hcode i hi, List.getD_eq_getElem _ _ hi, hiw]
    rw [← this]
    exact wordProd_mem_closure (hletters _ hwi)

theorem card_closure_of_list {S : Set (Fin 4)} {ws : List (List (Fin 4))} {cs : List (List ℕ)}
    (hlen : ws.length = cs.length)
    (hcode : ∀ i < cs.length, codeWord (ws.getD i []) = cs.getD i [])
    (hletters : ∀ l ∈ ws, ∀ k ∈ l, k ∈ S) (hone : idCode ∈ cs)
    (hclosed : ∀ i < cs.length, ∀ k ∈ S, compose (gc k) (cs.getD i []) ∈ cs) (hnd : cs.Nodup) :
    Nat.card (Subgroup.closure (gen '' S)) = cs.length := by
  have hmem := mem_closure_iff_of_list hlen hcode hletters hone hclosed
  let f : Subgroup.closure (gen '' S) → cs.toFinset := fun w =>
    ⟨code w, List.mem_toFinset.2 ((hmem w).1 w.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (code_injective (congrArg Subtype.val h)), fun c => ?_⟩
    obtain ⟨i, hi, hic⟩ := List.getElem_of_mem (List.mem_toFinset.1 c.2)
    refine ⟨⟨wordProd (ws.getD i []), (hmem _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [code_wordProd, hcode i hi, List.getD_eq_getElem _ _ hi, hic]
      exact List.mem_toFinset.1 c.2
    · change code (wordProd (ws.getD i [])) = c.1
      rw [code_wordProd, hcode i hi, List.getD_eq_getElem _ _ hi, hic]
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_finsetCard,
    List.toFinset_card_of_nodup hnd]

@[expose] def tElt (a : ℕ) : Equiv.Perm Λ := wordProd (tWords.getD a [])

@[expose] def jElt (i : ℕ) : Equiv.Perm Λ := wordProd (jWords.getD i [])

@[expose] def kElt (i : ℕ) : Equiv.Perm Λ := wordProd (kWords.getD i [])

theorem code_tElt {a : ℕ} (ha : a < 24) : code (tElt a) = tCodes.getD a [] := by
  rw [tElt, code_wordProd, codeWord_tWords a ha]

theorem code_jElt {i : ℕ} (hi : i < 48) : code (jElt i) = jCodes.getD i [] := by
  rw [jElt, code_wordProd, codeWord_jWords i hi]

theorem code_kElt {i : ℕ} (hi : i < 48) : code (kElt i) = kCodes.getD i [] := by
  rw [kElt, code_wordProd, codeWord_kWords i hi]

theorem tElt_23 : tElt 23 = 1 := by rw [tElt, tWords_theta]; rfl

theorem jElt_zero : jElt 0 = 1 := by rw [jElt, jWords_zero]; rfl

theorem mem_J_iff (k : Fin 4) : k ∈ J ↔ k ≠ 0 := by
  simp only [J, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert k
  decide

theorem mem_K_iff (k : Fin 4) : k ∈ K ↔ k ≠ 3 := by
  simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert k
  decide

theorem idCode_mem_jCodes : idCode ∈ jCodes := by
  have h := codeWord_jWords 0 (by norm_num)
  rw [jWords_zero] at h
  have h0 : 0 < jCodes.length := by rw [jCodes_length]; norm_num
  rw [show idCode = codeWord [] from rfl, h, List.getD_eq_getElem _ _ h0]
  exact List.getElem_mem _

theorem idCode_mem_kCodes : idCode ∈ kCodes := by
  have h := codeWord_kWords 0 (by norm_num)
  rw [kWords_zero] at h
  have h0 : 0 < kCodes.length := by rw [kCodes_length]; norm_num
  rw [show idCode = codeWord [] from rfl, h, List.getD_eq_getElem _ _ h0]
  exact List.getElem_mem _

theorem jCodes_closed :
    ∀ i < jCodes.length, ∀ k ∈ J, compose (gc k) (jCodes.getD i []) ∈ jCodes := by
  intro i hi k hk
  rw [jCodes_length] at hi
  obtain ⟨m, hm, heq, -⟩ := jCodes_edge i hi k ((mem_J_iff k).1 hk)
  rw [heq, List.getD_eq_getElem _ _ (by rw [jCodes_length]; exact hm)]
  exact List.getElem_mem _

theorem mem_WJ_iff_code (w : Equiv.Perm Λ) : w ∈ WJ ↔ code w ∈ jCodes :=
  mem_closure_iff_of_list (by rw [jWords_length, jCodes_length])
    (fun i hi => codeWord_jWords i (by rwa [jCodes_length] at hi))
    (fun l hl k hk => (mem_J_iff k).2 (jWords_letters l hl k hk)) idCode_mem_jCodes
    jCodes_closed w

theorem mem_WK_iff_code (w : Equiv.Perm Λ) : w ∈ WK ↔ code w ∈ kCodes :=
  mem_closure_iff_of_list (by rw [kWords_length, kCodes_length])
    (fun i hi => codeWord_kWords i (by rwa [kCodes_length] at hi))
    (fun l hl k hk => (mem_K_iff k).2 (kWords_letters l hl k hk)) idCode_mem_kCodes
    (fun i hi k hk => kCodes_closed i (by rwa [kCodes_length] at hi) k ((mem_K_iff k).1 hk)) w

theorem card_WJ : Nat.card WJ = 48 := by
  rw [WJ, card_closure_of_list (by rw [jWords_length, jCodes_length])
    (fun i hi => codeWord_jWords i (by rwa [jCodes_length] at hi))
    (fun l hl k hk => (mem_J_iff k).2 (jWords_letters l hl k hk)) idCode_mem_jCodes jCodes_closed
    jCodes_nodup, jCodes_length]

theorem card_WK : Nat.card WK = 48 := by
  rw [WK, card_closure_of_list (by rw [kWords_length, kCodes_length])
    (fun i hi => codeWord_kWords i (by rwa [kCodes_length] at hi))
    (fun l hl k hk => (mem_K_iff k).2 (kWords_letters l hl k hk)) idCode_mem_kCodes
    (fun i hi k hk => kCodes_closed i (by rwa [kCodes_length] at hi) k ((mem_K_iff k).1 hk))
    kCodes_nodup, kCodes_length]

theorem mem_WJ_iff (w : Equiv.Perm Λ) : w ∈ WJ ↔ ∃ i < 48, w = jElt i := by
  rw [mem_WJ_iff_code]
  constructor
  · intro h
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem h
    rw [jCodes_length] at hi
    refine ⟨i, hi, code_injective ?_⟩
    rw [code_jElt hi, List.getD_eq_getElem _ _ (by rw [jCodes_length]; exact hi), hiw]
  · rintro ⟨i, hi, rfl⟩
    rw [code_jElt hi, List.getD_eq_getElem _ _ (by rw [jCodes_length]; exact hi)]
    exact List.getElem_mem _

theorem mem_WK_iff (w : Equiv.Perm Λ) : w ∈ WK ↔ ∃ i < 48, w = kElt i := by
  rw [mem_WK_iff_code]
  constructor
  · intro h
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem h
    rw [kCodes_length] at hi
    refine ⟨i, hi, code_injective ?_⟩
    rw [code_kElt hi, List.getD_eq_getElem _ _ (by rw [kCodes_length]; exact hi), hiw]
  · rintro ⟨i, hi, rfl⟩
    rw [code_kElt hi, List.getD_eq_getElem _ _ (by rw [kCodes_length]; exact hi)]
    exact List.getElem_mem _

theorem jElt_mem {i : ℕ} (hi : i < 48) : jElt i ∈ WJ := (mem_WJ_iff _).2 ⟨i, hi, rfl⟩

theorem tElt_mem_W (a : ℕ) : tElt a ∈ W := wordProd_mem_W _

theorem gen_θΛ {j : Fin 4} (hj : j ∈ J) : gen j θΛ = θΛ := by
  rw [← ι_23, apply_ι_eq_iff, code_gen]
  exact gc_theta j ((mem_J_iff j).1 hj)

theorem WJ_le_stabilizer : WJ ≤ MulAction.stabilizer (Equiv.Perm Λ) θΛ := by
  rw [WJ, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact gen_θΛ hj

theorem apply_θΛ_of_mem_WJ {v : Equiv.Perm Λ} (hv : v ∈ WJ) : v θΛ = θΛ :=
  WJ_le_stabilizer hv

theorem tElt_θΛ {a : ℕ} (ha : a < 24) : tElt a θΛ = ι ⟨a, ha⟩ := by
  rw [← ι_23, apply_ι_eq_iff, code_tElt ha]
  exact tCodes_theta a ha

theorem gen_mul_tElt (k : Fin 4) {a : ℕ} (ha : a < 24) :
    (gen k * tElt a = tElt (gidx k a) ∧
      (tWords.getD (gidx k a) []).length ≤ (tWords.getD a []).length + 1 ∧
      ((tWords.getD (gidx k a) []).length = (tWords.getD a []).length + 1 →
        wordWeight (tWords.getD (gidx k a) []) =
          letterWeight k * wordWeight (tWords.getD a []))) ∨
    (gidx k a = a ∧
      ∃ j ∈ J, gen k * tElt a = tElt a * gen j ∧ letterWeight j = letterWeight k) := by
  rcases tCodes_edge a ha k with ⟨h, hl, hw⟩ | ⟨hb, j, hj, h, hw⟩
  · refine Or.inl ⟨code_injective ?_, hl, hw⟩
    rw [code_mul, code_gen, code_tElt ha, code_tElt (gidx_lt k ha), h]
  · refine Or.inr ⟨hb, j, (mem_J_iff j).2 hj, code_injective ?_, hw⟩
    rw [code_mul, code_mul, code_gen, code_gen, code_tElt ha, h]

theorem mem_W_iff (w : Equiv.Perm Λ) : w ∈ W ↔ ∃ a < 24, ∃ v ∈ WJ, w = tElt a * v := by
  constructor
  · intro hw
    have hstep : ∀ (k : Fin 4) (y : Equiv.Perm Λ), (∃ a < 24, ∃ v ∈ WJ, y = tElt a * v) →
        ∃ a < 24, ∃ v ∈ WJ, gen k * y = tElt a * v := by
      rintro k y ⟨a, ha, v, hv, rfl⟩
      rcases gen_mul_tElt k ha with ⟨h, -⟩ | ⟨-, j, hj, h, -⟩
      · exact ⟨gidx k a, gidx_lt k ha, v, hv, by rw [← mul_assoc, h]⟩
      · refine ⟨a, ha, gen j * v, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨j, hj, rfl⟩) hv,
          by rw [← mul_assoc, h, mul_assoc]⟩
    induction hw using Subgroup.closure_induction_left with
    | one => exact ⟨23, by norm_num, 1, Subgroup.one_mem _, by rw [tElt_23, mul_one]⟩
    | mul_left x hx y _ ih =>
      obtain ⟨k, rfl⟩ := hx
      exact hstep k y ih
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨k, rfl⟩ := hx
      rw [gen_inv]
      exact hstep k y ih
  · rintro ⟨a, -, v, hv, rfl⟩
    exact Subgroup.mul_mem _ (tElt_mem_W a) (WJ_le_W hv)

theorem tElt_mul_apply_θΛ {a : ℕ} (ha : a < 24) {v : Equiv.Perm Λ} (hv : v ∈ WJ) :
    (tElt a * v) θΛ = ι ⟨a, ha⟩ := by
  rw [Equiv.Perm.mul_apply, apply_θΛ_of_mem_WJ hv, tElt_θΛ ha]

theorem tElt_mul_inj {a b : ℕ} (ha : a < 24) (hb : b < 24) {v v' : Equiv.Perm Λ} (hv : v ∈ WJ)
    (hv' : v' ∈ WJ) (h : tElt a * v = tElt b * v') : a = b ∧ v = v' := by
  have hab : a = b := by
    have := congrArg (fun w : Equiv.Perm Λ => w θΛ) h
    simp only [tElt_mul_apply_θΛ ha hv, tElt_mul_apply_θΛ hb hv'] at this
    exact congrArg Fin.val (ι.injective this)
  subst hab
  exact ⟨rfl, mul_left_cancel h⟩

theorem card_W : Nat.card W = 1152 := by
  let f : Fin 24 × WJ → W := fun p =>
    ⟨tElt p.1 * p.2, (mem_W_iff _).2 ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q h => ?_, fun w => ?_⟩
    · obtain ⟨h₁, h₂⟩ := tElt_mul_inj p.1.2 q.1.2 p.2.2 q.2.2 (congrArg Subtype.val h)
      exact Prod.ext (Fin.ext h₁) (Subtype.ext h₂)
    · obtain ⟨a, ha, v, hv, hw⟩ := (mem_W_iff w.1).1 w.2
      exact ⟨(⟨a, ha⟩, ⟨v, hv⟩), Subtype.ext hw.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_WJ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem mem_WJ_iff_stabilizer (w : Equiv.Perm Λ) : w ∈ WJ ↔ w ∈ W ∧ w θΛ = θΛ := by
  refine ⟨fun hw => ⟨WJ_le_W hw, apply_θΛ_of_mem_WJ hw⟩, fun ⟨hw, hθ⟩ => ?_⟩
  obtain ⟨a, ha, v, hv, rfl⟩ := (mem_W_iff w).1 hw
  rw [tElt_mul_apply_θΛ ha hv, ← ι_23] at hθ
  have : a = 23 := congrArg Fin.val (ι.injective hθ)
  subst this
  rwa [tElt_23, one_mul]

end CFSG.Monster.B.Classical.E6Folded
