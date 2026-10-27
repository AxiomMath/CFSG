module

public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4.QTAbstract
public import CFSG.Sporadic.J4.QTCheck

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native Matrix

@[expose] noncomputable def Mx : J →* Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  (Units.coeHom _).comp J.subtype

theorem Mx_injective : Function.Injective Mx := fun _ _ h => Subtype.ext (Units.ext h)

theorem Mx_apply (g : J) :
    Mx g = ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := rfl

@[expose] noncomputable def XJ (ℓ : ℤ) : J :=
  if 0 < ℓ then xJ (ℓ.toNat - 1) else (xJ ((-ℓ).toNat - 1))⁻¹

theorem wordProd_xJ (w : List ℤ) : wordProd xJ w = (w.map XJ).prod := rfl

theorem coe_wordProd (w : List ℤ) :
    ((wordProd xJ w : J) : GL (Fin 112) (ZMod 2)) = wordProd locGL w := by
  unfold wordProd
  induction w with
  | nil => simp
  | cons l w ih =>
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih]
    congr 1
    split_ifs <;> simp [xJ]

section Mat

variable (hM : MatFacts)
include hM

theorem Mx_XJ (ℓ : ℤ) : Mx (XJ ℓ) = rowsMatrix (xRows (locMats ()) (locInvs ()) ℓ) := by
  unfold XJ xRows
  split_ifs with h
  · rw [Mx_apply, show ((xJ (ℓ.toNat - 1) : J) : GL (Fin 112) (ZMod 2)) = locGL (ℓ.toNat - 1) from
      rfl, ← locMats_spec hM]
  · rw [Mx_apply, show (((xJ ((-ℓ).toNat - 1))⁻¹ : J) : GL (Fin 112) (ZMod 2)) =
      (locGL ((-ℓ).toNat - 1))⁻¹ from rfl, ← locInvs_spec hM]

theorem Mx_XJ_inv (ℓ : ℤ) :
    Mx ((XJ ℓ)⁻¹) = rowsMatrix (xiRows (locMats ()) (locInvs ()) ℓ) := by
  unfold XJ xiRows
  split_ifs with h
  · rw [Mx_apply, show (((xJ (ℓ.toNat - 1))⁻¹ : J) : GL (Fin 112) (ZMod 2)) =
      (locGL (ℓ.toNat - 1))⁻¹ from rfl, ← locInvs_spec hM]
  · rw [inv_inv, Mx_apply, show ((xJ ((-ℓ).toNat - 1) : J) : GL (Fin 112) (ZMod 2)) =
      locGL ((-ℓ).toNat - 1) from rfl, ← locMats_spec hM]

theorem Mx_wordProd (w : List ℤ) :
    Mx (wordProd xJ w) = rowsMatrix (wordRows (locMats ()) (locInvs ()) w) := by
  rw [Mx_apply, coe_wordProd, rowsMatrix_wordRows (locMats_spec hM) (locInvs_spec hM) w]

end Mat

@[expose] noncomputable def uJ (j : ℕ) : J := wordProd xJ (uWord j)

theorem uTab_size (loc inv : Array (Array V2)) : (uTab loc inv).size = 11 := by
  simp [uTab]

theorem uTab_get {j : ℕ} (hj : j < 11) (loc inv : Array (Array V2)) :
    (uTab loc inv)[j]?.getD idRows = wordRows loc inv (uWord j) := by
  simp [uTab, hj]

theorem etaRows_succ (T : Array (Array V2)) (n c : ℕ) :
    etaRows T (n + 1) c =
      if c.testBit n then mulRows (etaRows T n c) (T[n]?.getD idRows) else etaRows T n c := by
  unfold etaRows
  rw [List.range_succ, List.foldl_append]
  by_cases h : c.testBit n <;> simp [h]

section Mat2

variable (hM : MatFacts)
include hM

theorem Mx_uJ {j : ℕ} (hj : j < 11) :
    Mx (uJ j) = rowsMatrix ((uTab (locMats ()) (locInvs ()))[j]?.getD idRows) := by
  rw [uTab_get hj, uJ, Mx_wordProd hM]

theorem Mx_eta : ∀ n ≤ 11, ∀ c, Mx (eta uJ n c) =
    rowsMatrix (etaRows (uTab (locMats ()) (locInvs ())) n c)
  | 0, _, c => by simp [eta, etaRows, rowsMatrix_idRows]
  | n + 1, hn, c => by
    rw [eta_succ, etaRows_succ, map_mul]
    split_ifs with h
    · rw [Mx_eta n (by omega) c, Mx_uJ hM (by omega), rowsMatrix_mulRows]
    · rw [map_one, Mx_eta n (by omega) c, mul_one]

theorem elem_uJ : Elem uJ 11 := by
  have h := chkU_true
  unfold chkU at h
  simp only [List.all_eq_true, Bool.and_eq_true, List.mem_range] at h
  refine ⟨fun j hj => ?_, fun i hi j hj => ?_⟩
  · apply Mx_injective
    have := congrArg rowsMatrix (eqRows_iff.1 (h j hj).1)
    rw [rowsMatrix_mulRows, rowsMatrix_idRows, ← Mx_uJ hM hj] at this
    rw [map_mul, map_one]
    exact this
  · apply Mx_injective
    have := congrArg rowsMatrix (eqRows_iff.1 ((h i hi).2 j hj))
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← Mx_uJ hM hi, ← Mx_uJ hM hj] at this
    rw [map_mul, map_mul]
    exact this

theorem conj_uJ {ℓ : ℤ} (hℓ : ℓ ∈ letters) {j : ℕ} (hj : j < 11) :
    XJ ℓ * uJ j * (XJ ℓ)⁻¹ = eta uJ 11 (letterRow ℓ j) := by
  have h := chkConj_true
  unfold chkConj at h
  simp only [List.all_eq_true, List.mem_range] at h
  have := congrArg rowsMatrix (eqRows_iff.1 (h ℓ hℓ j hj))
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← Mx_XJ hM, ← Mx_XJ_inv hM, ← Mx_uJ hM hj,
    ← Mx_eta hM 11 le_rfl] at this
  apply Mx_injective
  rw [map_mul, map_mul]
  exact this

end Mat2

theorem etaVec_succ (F : Array (Array V2)) (n c : ℕ) :
    etaVec F (n + 1) c =
      if c.testBit n then frApply (F[n]?.getD #[]) (etaVec F n c) else etaVec F n c := by
  unfold etaVec
  rw [List.range_succ, List.foldl_append]
  by_cases h : c.testBit n <;> simp [h]

theorem F_get {n : ℕ} (hn : n < 11) (loc inv : Array (Array V2)) :
    ((uTab loc inv).map frTable)[n]?.getD #[] = frTable ((uTab loc inv)[n]?.getD idRows) := by
  have : n < (uTab loc inv).size := by rw [uTab_size]; exact hn
  rw [Array.getElem?_map, Array.getElem?_eq_getElem this]
  simp only [Option.map_some, Option.getD_some]

theorem differs_toVec {a b : V2} (h : differs a b = true) : a.toVec ≠ b.toVec := by
  intro e
  unfold differs at h
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨j, hj, hne⟩ := h
  exact hne (V2.testBit_eq_of_toVec_eq e (by omega))

section Vec

variable (hM : MatFacts)
include hM

theorem etaVec_toVec : ∀ n ≤ 11, ∀ c,
    (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) n c).toVec =
      w0.toVec ᵥ* Mx (eta uJ n c)
  | 0, _, c => by simp [etaVec, eta]
  | n + 1, hn, c => by
    rw [etaVec_succ, eta_succ, map_mul]
    split_ifs with h
    · rw [F_get (by omega), frApply_toVec_eq_vecMul, etaVec_toVec n (by omega) c,
        Matrix.vecMul_vecMul, Mx_uJ hM (by omega)]
    · rw [map_one, Matrix.mul_one, etaVec_toVec n (by omega) c]

theorem eta_ne_one {c : ℕ} (hc0 : c ≠ 0) (hc : c < 2 ^ 11) : eta uJ 11 c ≠ 1 := by
  intro h1
  have h := chkFree_true
  unfold chkFree at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  rcases h c (by omega) with h0 | h0
  · exact hc0 h0
  · apply differs_toVec h0
    rw [etaVec_toVec hM 11 le_rfl, h1, map_one, Matrix.vecMul_one]

theorem eta_inj : ∀ c < 2 ^ 11, ∀ d < 2 ^ 11, eta uJ 11 c = eta uJ 11 d → c = d :=
  eta_injective (elem_uJ hM) fun _ hc hc0 => eta_ne_one hM hc0 hc

theorem card_Eg_uJ : Nat.card ↥(Eg uJ 11) = 2 ^ 11 := card_Eg (elem_uJ hM) (eta_inj hM)

end Vec

@[expose] noncomputable def xpJ : J := wordProd xJ xpWord

section Fus

variable (hM : MatFacts)
include hM

theorem Mx_a : Mx a = rowsMatrix rowsA := by
  rw [Mx_apply, a_coe, gA_val hM, rowsMatrix_rowsA]

theorem a_mul_a : a * a = 1 := by
  apply Mx_injective
  rw [map_mul, map_one, Mx_a hM, ← sq, rowsMatrix_rowsA, matA_sq hM]

theorem a_inv_eq : a⁻¹ = a := inv_eq_of_mul_eq_one_right (a_mul_a hM)

theorem Mx_xpJ : Mx xpJ = rowsMatrix (xpRows (locMats ()) (locInvs ())) :=
  Mx_wordProd hM xpWord

theorem xpJ_not_mem : xpJ ∉ Eg uJ 11 := by
  intro hx
  obtain ⟨c, hc, hxc⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
  have h := chkOut_true
  unfold chkOut at h
  simp only [List.all_eq_true, List.mem_range] at h
  apply differs_toVec (h c hc)
  rw [etaVec_toVec hM 11 le_rfl, ← hxc, frApply_toVec_eq_vecMul, Mx_xpJ hM]

theorem xpJ_sq : xpJ * xpJ = 1 := by
  have h := chkFus_true
  unfold chkFus at h
  simp only [Bool.and_eq_true] at h
  apply Mx_injective
  have := congrArg rowsMatrix (eqRows_iff.1 h.1)
  rw [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  rw [map_mul, map_one, Mx_xpJ hM]
  exact this

theorem sxp_pow : ((a * uJ 0 * a⁻¹) * xpJ) ^ 33 = 1 := by
  have h := chkFus_true
  unfold chkFus at h
  simp only [Bool.and_eq_true] at h
  apply Mx_injective
  have := congrArg rowsMatrix (eqRows_iff.1 h.2)
  rw [rowsMatrix_powRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows,
    rowsMatrix_idRows, ← Mx_a hM, ← Mx_uJ hM (j := 0) (by norm_num)] at this
  rw [map_pow, map_one, map_mul, map_mul, map_mul, a_inv_eq hM, Mx_xpJ hM]
  exact this

end Fus

theorem XJ_one : XJ 1 = xJ 0 := by simp [XJ]

theorem XJ_two : XJ 2 = xJ 1 := by simp [XJ]

theorem XJ_three : XJ 3 = xJ 2 := by simp [XJ]

theorem XJ_neg_one : XJ (-1) = (xJ 0)⁻¹ := by simp [XJ]

theorem XJ_neg_two : XJ (-2) = (xJ 1)⁻¹ := by simp [XJ]

theorem XJ_neg_three : XJ (-3) = (xJ 2)⁻¹ := by simp [XJ]

theorem letters_cases {ℓ : ℤ} (hℓ : ℓ ∈ letters) :
    ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 ∨ ℓ = -1 ∨ ℓ = -2 ∨ ℓ = -3 := by
  simpa [letters] using hℓ

theorem XJ_mem {ℓ : ℤ} (hℓ : ℓ ∈ letters) : XJ ℓ ∈ Hj := by
  rcases letters_cases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [XJ_one]; exact xJ_mem (by norm_num)
  · rw [XJ_two]; exact xJ_mem (by norm_num)
  · rw [XJ_three]; exact xJ_mem (by norm_num)
  · rw [XJ_neg_one]; exact Hj.inv_mem (xJ_mem (by norm_num))
  · rw [XJ_neg_two]; exact Hj.inv_mem (xJ_mem (by norm_num))
  · rw [XJ_neg_three]; exact Hj.inv_mem (xJ_mem (by norm_num))

theorem XJ_inv {ℓ : ℤ} (hℓ : ℓ ∈ letters) : -ℓ ∈ letters ∧ XJ (-ℓ) = (XJ ℓ)⁻¹ := by
  refine ⟨letters_neg ℓ hℓ, ?_⟩
  rcases letters_cases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [XJ_neg_one, XJ_one]
  · rw [XJ_neg_two, XJ_two]
  · rw [XJ_neg_three, XJ_three]
  · rw [neg_neg, XJ_neg_one, XJ_one, inv_inv]
  · rw [neg_neg, XJ_neg_two, XJ_two, inv_inv]
  · rw [neg_neg, XJ_neg_three, XJ_three, inv_inv]

theorem Hj_le_closure : Hj ≤ Subgroup.closure (XJ '' {ℓ | ℓ ∈ letters}) := by
  refine Subgroup.closure_mono ?_
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨1, by simp [letters], XJ_one⟩
  · exact ⟨2, by simp [letters], XJ_two⟩
  · exact ⟨3, by simp [letters], XJ_three⟩

theorem wordProd_mem_Hj {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) : wordProd xJ w ∈ Hj := by
  rw [wordProd_xJ]
  refine Subgroup.list_prod_mem Hj ?_
  intro x hx
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hx
  exact XJ_mem (hw ℓ hℓ)

theorem uJ_mem {j : ℕ} (hj : j < 11) : uJ j ∈ Hj := wordProd_mem_Hj (uWord_letters.1 j hj)

theorem Eg_le_Hj : Eg uJ 11 ≤ Hj := by
  rw [Eg, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact uJ_mem hj

@[expose] noncomputable def SJ (i : ℕ) : J := wordProd xJ (sgWords.getD i [])

theorem sg_letters_get (i : ℕ) : ∀ ℓ ∈ sgWords.getD i [], ℓ ∈ letters := by
  intro ℓ hℓ
  by_cases hi : i < sgWords.length
  · rw [List.getD_eq_getElem _ _ hi] at hℓ
    exact sg_letters _ (List.getElem_mem hi) ℓ hℓ
  · rw [List.getD_eq_default _ _ (by omega)] at hℓ
    simp at hℓ

theorem SJ_mem (i : ℕ) : SJ i ∈ Hj := wordProd_mem_Hj (sg_letters_get i)

section Act

variable (hM : MatFacts)
include hM

theorem hX_all {ℓ : ℤ} (hℓ : ℓ ∈ letters) (c : ℕ) :
    XJ ℓ * eta uJ 11 c * (XJ ℓ)⁻¹ = eta uJ 11 (act ℓ c) :=
  conj_eta (elem_uJ hM) (XJ ℓ) (letterRow ℓ) (fun _ hj => conj_uJ hM hℓ hj) le_rfl c

theorem SJ_conj {i : ℕ} (hi : i < 12) (c : ℕ) :
    SJ i * eta uJ 11 c * (SJ i)⁻¹ = eta uJ 11 (actS i c) := by
  have hx : ∀ j < 11, SJ i * uJ j * (SJ i)⁻¹ = eta uJ 11 (sgRow i j) := by
    intro j hj
    have := word_conj XJ act (sgWords.getD i [])
      (fun ℓ hℓ c => hX_all hM (sg_letters_get i ℓ hℓ) c) (2 ^ j)
    rw [eta_two_pow hj, ← sg_rows_spec i hi j hj] at this
    exact this
  exact conj_eta (elem_uJ hM) (SJ i) (sgRow i) hx le_rfl c

end Act

@[expose] noncomputable def bJ (i : ℕ) : J := eta uJ 11 (chainBase.getD i 0)

@[expose] noncomputable def tJ (j k : ℕ) : J :=
  (((chainLevels.getD j []).getD k []).map SJ).prod

@[expose] def cntJ (j : ℕ) : ℕ := (chainLevels.getD j []).length

theorem tw_mem {j k : ℕ} (hk : k < cntJ j) :
    (chainLevels.getD j []).getD k [] ∈ chainLevels.getD j [] := by
  unfold cntJ at hk
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

section Chain

variable (hM : MatFacts)
include hM

theorem tJ_conj {j k : ℕ} (hj : j < 5) (hk : k < cntJ j) (c : ℕ) :
    tJ j k * eta uJ 11 c * (tJ j k)⁻¹ =
      eta uJ 11 (((chainLevels.getD j []).getD k []).foldr actS c) :=
  word_conj SJ actS _ (fun _ hi c => SJ_conj hM ((chain_fix j hj _ (tw_mem hk)).1 _ hi) c) c

theorem tJ_mem_Kc {j k : ℕ} (hj : j < 5) (hk : k < cntJ j) : tJ j k ∈ Kc Hj bJ j := by
  rw [mem_Kc]
  refine ⟨?_, fun i hi => ?_⟩
  · refine Subgroup.list_prod_mem Hj ?_
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact SJ_mem i
  · have hfix := (chain_fix j hj _ (tw_mem hk)).2 i hi
    have h1 := tJ_conj hM hj hk (chainBase.getD i 0)
    rw [hfix] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem tJ_distinct {j : ℕ} (hj : j < 5) {k k' : ℕ} (hk : k < cntJ j) (hk' : k' < cntJ j)
    (h : tJ j k * bJ j * (tJ j k)⁻¹ = tJ j k' * bJ j * (tJ j k')⁻¹) : k = k' := by
  have e1 := tJ_conj hM hj hk (chainBase.getD j 0)
  have e2 := tJ_conj hM hj hk' (chainBase.getD j 0)
  obtain ⟨hnd, hlt⟩ := chain_distinct j hj
  have h' : eta uJ 11 (((chainLevels.getD j []).getD k []).foldr actS (chainBase.getD j 0)) =
      eta uJ 11 (((chainLevels.getD j []).getD k' []).foldr actS (chainBase.getD j 0)) := by
    rw [← e1, ← e2]
    exact h
  have hm := eta_inj hM _ (hlt _ (tw_mem hk)) _ (hlt _ (tw_mem hk')) h'
  have hk1 : k < ((chainLevels.getD j []).map fun tw =>
      tw.foldr actS (chainBase.getD j 0)).length := by
    rw [List.length_map]; exact hk
  have hk1' : k' < ((chainLevels.getD j []).map fun tw =>
      tw.foldr actS (chainBase.getD j 0)).length := by
    rw [List.length_map]; exact hk'
  refine (hnd.getElem_inj_iff (hi := hk1) (hj := hk1')).1 ?_
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] at hm
  simpa [List.getElem_map] using hm

theorem centralizer_Hj (hF : J4Facts) :
    ∀ x ∈ Hj, (∀ y ∈ Eg uJ 11, x * y = y * x) → x ∈ Eg uJ 11 := by
  refine centralizer_le_of_chain (elem_uJ hM) Hj Eg_le_Hj (card_Eg_uJ hM) bJ
    (fun i => eta_mem_Eg 11 le_rfl _) cntJ tJ 5 (fun j hj k hk => tJ_mem_Kc hM hj hk)
    (fun j hj k hk k' hk' h => tJ_distinct hM hj hk hk' h) ?_
  rw [card_Hj hF]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  unfold cntJ
  rw [chain_card]
  norm_num

end Chain

theorem index_Hj_odd (hF : J4Facts) : ¬ 2 ∣ Hj.index := by
  have h := Subgroup.card_mul_index Hj
  rw [card_Hj hF, card_J hF] at h
  have : Hj.index = 173067389 := by omega
  rw [this]
  decide

theorem selfCentralizingFusion_J (hF : J4Facts) :
    ∃ H E : Subgroup J, E ≤ H ∧ ¬ 2 ∣ H.index ∧ (∀ h ∈ H, ∀ x ∈ E, h * x * h⁻¹ ∈ E) ∧
      IsPGroup 2 E ∧
      (∀ D : Subgroup J, D ≤ E → (∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D) → D = ⊥ ∨ D = E) ∧
      (∀ h ∈ H, (∀ x ∈ E, h * x = x * h) → h ∈ E) ∧
      ∃ e ∈ E, ∃ g : J, e * e = 1 ∧ g * e * g⁻¹ ∈ H ∧ g * e * g⁻¹ ∉ E := by
  have hM := hF.mat
  refine ⟨Hj, Eg uJ 11, Eg_le_Hj, index_Hj_odd hF, ?_, isPGroup_Eg (elem_uJ hM), ?_,
    centralizer_Hj hM hF, ?_⟩
  · exact eg_normalizes (elem_uJ hM) Hj XJ act letters (fun ℓ hℓ c => hX_all hM hℓ c)
      (fun ℓ hℓ => XJ_inv hℓ) Hj_le_closure
  · intro D hDE hD
    exact minimal_of_orbits (elem_uJ hM) Hj XJ act letters (fun ℓ hℓ => XJ_mem hℓ)
      (fun ℓ hℓ c => hX_all hM hℓ c) orbits orbit_words orbit_cover orbit_span D hDE hD
  · have he2 : uJ 0 * uJ 0 = 1 := (elem_uJ hM).sq 0 (by norm_num)
    have hs : (a * uJ 0 * a⁻¹) * (a * uJ 0 * a⁻¹) = 1 := by
      calc (a * uJ 0 * a⁻¹) * (a * uJ 0 * a⁻¹) = a * (uJ 0 * uJ 0) * a⁻¹ := by group
        _ = 1 := by rw [he2]; group
    have hconj := dihedral_conj (a * uJ 0 * a⁻¹) xpJ hs (xpJ_sq hM) (sxp_pow hM)
    have key : ∀ P : J, P * a * uJ 0 * (P * a)⁻¹ = P * (a * uJ 0 * a⁻¹) * P⁻¹ := by
      intro P; group
    have hgx : ((a * uJ 0 * a⁻¹) * xpJ) ^ 16 * a * uJ 0 *
        (((a * uJ 0 * a⁻¹) * xpJ) ^ 16 * a)⁻¹ = xpJ := by
      rw [key]; exact hconj
    refine ⟨uJ 0, u_mem_Eg (by norm_num), ((a * uJ 0 * a⁻¹) * xpJ) ^ 16 * a, he2, ?_, ?_⟩
    · rw [hgx]
      exact wordProd_mem_Hj uWord_letters.2
    · rw [hgx]
      exact xpJ_not_mem hM

end CFSG.Sporadic.J4.QT
