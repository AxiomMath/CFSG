module

public import CFSG.Sporadic.Schreier.Co1OddBCheck
public import CFSG.Sporadic.Schreier.Co1OddRows
public import CFSG.Sporadic.Schreier.Co1OddGen
public import CFSG.Sporadic.Co1.Module.TwoBCert

public section

namespace CFSG.Sporadic.Co1Schreier.OddB

open CFSG.Blueprint
open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective rowsMatrix rowsMatrix_mulVec
  rowsMatrix_idRows rowsMatrix_powRows rowsMatrix_mulRows)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative Matrix
open CFSG.Sporadic.Co1.Module (matHom matHom_injective co1Act co1Act_mul co1Act_inv_apply
  co1Act_apply_inv co1Act_injective rowsSB code4)
open CFSG.Sporadic.Co1.Module.TwoB (sBc matHom_sBc KB mem_KB card_cent card_KB_ge
  exists_orbit_family fix_eq_orbit ncard_fix_sBc initRowsB_size initRowsB_two getD_two'
  matHom_eA matHom_eB fix_sBc_omega)
open CFSG.Sporadic.Co1Schreier.OddGen CFSG.Sporadic.Co1Schreier.OddRows

@[expose] noncomputable def bRegsG :
    List NativeSporadic.Co1 :=
  CFSG.Sporadic.Co1.Module.Odd.runEval
    [CFSG.Sporadic.Co1.Module.Odd.eA, CFSG.Sporadic.Co1.Module.Odd.eB, sBc] Data.oddBProg

@[expose] noncomputable def bElt
    (i : ℕ) : NativeSporadic.Co1 := bRegsG.getD i 1

attribute [local irreducible] rowsSB

theorem bRel :
    CFSG.Sporadic.Co1.Module.Odd.RegsRel matHom bRegsG Native.oddBRegs := by
  refine CFSG.Sporadic.Co1.Module.Odd.runRows_spec matHom Data.oddBProg ?_
  refine ⟨by rw [initRowsB_size]; rfl, fun i => ?_⟩
  match i with
  | 0 => exact matHom_eA
  | 1 => exact matHom_eB
  | 2 =>
    rw [initRowsB_two, getD_two']
    exact matHom_sBc
  | i + 3 => simp [rowsMatrix_idRows, CFSG.Sporadic.Co1.Module.TwoB.initRowsB]

attribute [local irreducible] Native.oddBRegs

section

attribute [local irreducible] bRegsG

theorem matHom_bElt (i : ℕ) :
    matHom (bElt i) = rowsMatrix 24 (Native.oddReg Native.oddBRegs i) := by
  have h : ∀ j : ℕ, matHom (bRegsG.getD j 1) =
      rowsMatrix 24 (Native.oddBRegs[j]?.getD (idRows 24)) :=
    And.right bRel
  simpa only [bElt, Native.oddReg] using h i

end

attribute [local irreducible] bElt bRegsG

theorem b_facts :
    validRows rowsSB = true ∧
    (∀ i ∈ [9, 14, 19, 24], validRows (Native.oddReg Native.oddBRegs i) = true ∧
      mulRows 24 (Native.oddReg Native.oddBRegs i) rowsSB =
        mulRows 24 rowsSB (Native.oddReg Native.oddBRegs i) ∧
      isFixedN (transposeRows 24 (Native.oddReg Native.oddBRegs i)) code4 = true) ∧
    powRows 24 (Native.oddReg Native.oddBRegs 9) 3 = idRows 24 ∧
    powRows 24 (Native.oddReg Native.oddBRegs 19) 3 = idRows 24 ∧
    powRows 24 (Native.oddReg Native.oddBRegs 14) 5 = idRows 24 ∧
    powRows 24 (Native.oddReg Native.oddBRegs 24) 5 = idRows 24 ∧
    powRows 24 (mulRows 24 (Native.oddReg Native.oddBRegs 9)
      (Native.oddReg Native.oddBRegs 19)) 15 ≠ idRows 24 ∧
    powRows 24 (mulRows 24 (Native.oddReg Native.oddBRegs 14)
      (Native.oddReg Native.oddBRegs 24)) 15 ≠ idRows 24 ∧
    Native.oddPerfOK #[Native.oddReg Native.oddBRegs 9, Native.oddReg Native.oddBRegs 14]
      Data.oddPerfX (Native.oddReg Native.oddBRegs 9) = true ∧
    Native.oddPerfOK #[Native.oddReg Native.oddBRegs 9, Native.oddReg Native.oddBRegs 14]
      Data.oddPerfY (Native.oddReg Native.oddBRegs 14) = true := by
  have h := odd_b_check
  simp only [Native.oddBCheckOf, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, fun i hi => ⟨(h2 i hi).1.1, (h2 i hi).1.2, (h2 i hi).2⟩, h3, h4, h5, h6, h7, h8,
    h9, h10⟩

theorem bElt_mem_cent
    {i : ℕ} (hi : i ∈ [9, 14, 19, 24]) :
    bElt i ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commute_of_rows matHom_injective (matHom_bElt i) matHom_sBc (b_facts.2.1 i hi).2.1

theorem bElt_fix
    {i : ℕ} (hi : i ∈ [9, 14, 19, 24]) :
    co1Act (bElt i) (toVecD 24 code4) = toVecD 24 code4 := by
  rw [CFSG.Sporadic.Co1.Module.co1Act_eq_mulVec, matHom_bElt]
  exact (CFSG.Sporadic.Co1.Module.Odd.isFixedN_iff _ (by norm_num [code4])).1
    (b_facts.2.1 i hi).2.2

theorem bElt_mem_KB
    {i : ℕ} (hi : i ∈ [9, 14, 19, 24]) : bElt i ∈ KB :=
  mem_KB (bElt_mem_cent hi) (bElt_fix hi)

theorem bElt_nine_pow :
    bElt 9 ^ 3 = 1 :=
  pow_eq_one_of_rows matHom_injective (matHom_bElt 9) b_facts.2.2.1

theorem bElt_nineteen_pow :
    bElt 19 ^ 3 = 1 :=
  pow_eq_one_of_rows matHom_injective (matHom_bElt 19) b_facts.2.2.2.1

theorem bElt_fourteen_pow :
    bElt 14 ^ 5 = 1 :=
  pow_eq_one_of_rows matHom_injective (matHom_bElt 14) b_facts.2.2.2.2.1

theorem bElt_twentyfour_pow :
    bElt 24 ^ 5 = 1 :=
  pow_eq_one_of_rows matHom_injective (matHom_bElt 24) b_facts.2.2.2.2.2.1

theorem prod_pow_ne
    {i j : ℕ} (hi : i ∈ [9, 14, 19, 24]) (hj : j ∈ [9, 14, 19, 24])
    (h : powRows 24 (mulRows 24 (Native.oddReg Native.oddBRegs i)
      (Native.oddReg Native.oddBRegs j)) 15 ≠ idRows 24) : (bElt i * bElt j) ^ 15 ≠ 1 := by
  refine ne_one_of_rows (φ := matHom) ?_ (validRows_powRows
    (CFSG.Sporadic.Co1.Module.Odd.validRows_mulRows (b_facts.2.1 i hi).1 (b_facts.2.1 j hj).1)
    15) h
  rw [map_pow, map_mul, matHom_bElt, matHom_bElt, ← rowsMatrix_mulRows, ← rowsMatrix_powRows]

section Order

attribute [local instance] CFSG.Sporadic.Co1.Module.Odd.vecAct
  CFSG.Sporadic.Co1.Module.Odd.vecSMul

theorem card_KB :
    Nat.card ↥KB = 491520 := by
  have := CFSG.Sporadic.Co1.Module.finite_co1
  obtain ⟨t, ht, hdist⟩ := exists_orbit_family
  have h1 := CFSG.Sporadic.Co1.Module.Odd.card_mul_card_stab_le (G := NativeSporadic.Co1)
    (Ω := Fin 24 → ZMod 2) (Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1))
    (toVecD 24 code4) 4095 t ht (fun i hi j hj e => hdist i hi j hj e)
  rw [card_cent] at h1
  have h2 := card_KB_ge
  have h3 : 4095 * Nat.card ↥KB ≤ 2012774400 := h1
  omega

end Order

theorem KB_noOddNormal
    (N : Subgroup KB) (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have := CFSG.Sporadic.Co1.Module.finite_co1
  have h9 : bElt 9 ∈ KB := bElt_mem_KB (by simp)
  have h19 : bElt 19 ∈ KB := bElt_mem_KB (by simp)
  have h14 : bElt 14 ∈ KB := bElt_mem_KB (by simp)
  have h24 : bElt 24 ∈ KB := bElt_mem_KB (by simp)
  refine eq_bot_of_two_elements (K := KB) (by rw [card_KB]; norm_num) (e3 := ⟨bElt 9, h9⟩)
    (e3' := ⟨bElt 19, h19⟩) (e5 := ⟨bElt 14, h14⟩) (e5' := ⟨bElt 24, h24⟩)
    (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact bElt_nine_pow))
    (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact bElt_nineteen_pow))
    (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact bElt_fourteen_pow))
    (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact bElt_twentyfour_pow))
    (fun h => ?_) (fun h => ?_) N hN hodd
  · have h' := congrArg Subtype.val h
    rw [SubgroupClass.coe_pow, Subgroup.coe_mul] at h'
    exact prod_pow_ne (by simp) (by simp) b_facts.2.2.2.2.2.2.1 h'
  · have h' := congrArg Subtype.val h
    rw [SubgroupClass.coe_pow, Subgroup.coe_mul] at h'
    exact prod_pow_ne (by simp) (by simp) b_facts.2.2.2.2.2.2.2.1 h'

theorem xyRel :
    CFSG.Sporadic.Co1.Module.Odd.RegsRel matHom [bElt 9, bElt 14]
    #[Native.oddReg Native.oddBRegs 9, Native.oddReg Native.oddBRegs 14] := by
  refine ⟨by simp, fun i => ?_⟩
  match i with
  | 0 =>
    have e1 : ([bElt 9, bElt 14] : List NativeSporadic.Co1).getD 0 1 = bElt 9 := rfl
    have e2 : (#[Native.oddReg Native.oddBRegs 9, Native.oddReg Native.oddBRegs 14] :
        Array (Array ℕ))[0]?.getD (idRows 24) = Native.oddReg Native.oddBRegs 9 := by simp
    rw [e1, e2]
    exact matHom_bElt 9
  | 1 =>
    have e1 : ([bElt 9, bElt 14] : List NativeSporadic.Co1).getD 1 1 = bElt 14 := rfl
    have e2 : (#[Native.oddReg Native.oddBRegs 9, Native.oddReg Native.oddBRegs 14] :
        Array (Array ℕ))[1]?.getD (idRows 24) = Native.oddReg Native.oddBRegs 14 := by simp
    rw [e1, e2]
    exact matHom_bElt 14
  | i + 2 =>
    have e1 : ([bElt 9, bElt 14] : List NativeSporadic.Co1).getD (i + 2) 1 = 1 := by simp
    have e2 : (#[Native.oddReg Native.oddBRegs 9, Native.oddReg Native.oddBRegs 14] :
        Array (Array ℕ))[i + 2]?.getD (idRows 24) = idRows 24 := by simp
    rw [e1, e2, map_one, rowsMatrix_idRows]

theorem matHom_word
    (w : List (ℕ × ℕ)) :
    matHom (CFSG.Sporadic.Co1.Module.Odd.lineEval [bElt 9, bElt 14] w) =
      rowsMatrix 24 (lineRows #[Native.oddReg Native.oddBRegs 9,
        Native.oddReg Native.oddBRegs 14] w) :=
  CFSG.Sporadic.Co1.Module.Odd.lineRows_spec matHom xyRel w

theorem rowsMatrix_oddProdRows (G : Array (Array ℕ)) (ws : List (List (ℕ × ℕ))) :
    rowsMatrix 24 (Native.oddProdRows G ws) =
      (ws.map fun w => rowsMatrix 24 (lineRows G w)).prod := by
  unfold Native.oddProdRows
  have key : ∀ (acc : Array ℕ), rowsMatrix 24 (ws.foldl (fun acc w =>
      mulRows 24 acc (lineRows G w)) acc) =
      rowsMatrix 24 acc * (ws.map fun w => rowsMatrix 24 (lineRows G w)).prod := by
    induction ws with
    | nil => intro acc; simp
    | cons w ws ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_mulRows, List.map_cons, List.prod_cons,
        Matrix.mul_assoc]
  rw [key, rowsMatrix_idRows, Matrix.one_mul]

theorem eq_commutators
    {w0 w1 w2 w3 w4 w5 w6 w7 : List (ℕ × ℕ)} {t : NativeSporadic.Co1}
    {T : Array ℕ} (hT : matHom t = rowsMatrix 24 T)
    (h : Native.oddPerfOK #[Native.oddReg Native.oddBRegs 9, Native.oddReg Native.oddBRegs 14]
      [w0, w1, w2, w3, w4, w5, w6, w7] T = true) :
    ∃ a b c d : NativeSporadic.Co1, (∀ g ∈ [a, b, c, d],
      g ∈ Subgroup.closure ({bElt 9, bElt 14} : Set NativeSporadic.Co1)) ∧
      t = a * b * a⁻¹ * b⁻¹ * (c * d * c⁻¹ * d⁻¹) := by
  simp only [Native.oddPerfOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨-, hprod⟩, hinv⟩ := h
  set f : List (ℕ × ℕ) → NativeSporadic.Co1 :=
    CFSG.Sporadic.Co1.Module.Odd.lineEval [bElt 9, bElt 14] with hf
  have hmemJ : ∀ w, f w ∈ Subgroup.closure ({bElt 9, bElt 14} : Set NativeSporadic.Co1) := by
    intro w
    refine lineEval_mem _ (fun g hg => ?_) w
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hinvs : ∀ p ∈ [(0, 2), (1, 3), (4, 6), (5, 7)],
      f ([w0, w1, w2, w3, w4, w5, w6, w7][p.1]!) *
        f ([w0, w1, w2, w3, w4, w5, w6, w7][p.2]!) = 1 :=
    fun p hp => mul_eq_one_of_rows matHom_injective (matHom_word _) (matHom_word _) (hinv p hp)
  have e02 : f w2 = (f w0)⁻¹ := (eq_inv_of_mul_eq_one_right (hinvs (0, 2) (by simp)))
  have e13 : f w3 = (f w1)⁻¹ := (eq_inv_of_mul_eq_one_right (hinvs (1, 3) (by simp)))
  have e46 : f w6 = (f w4)⁻¹ := (eq_inv_of_mul_eq_one_right (hinvs (4, 6) (by simp)))
  have e57 : f w7 = (f w5)⁻¹ := (eq_inv_of_mul_eq_one_right (hinvs (5, 7) (by simp)))
  have ht : t = ([w0, w1, w2, w3, w4, w5, w6, w7].map f).prod := by
    apply matHom_injective
    rw [hT, ← hprod, rowsMatrix_oddProdRows, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun w _ => ?_
    exact (matHom_word w).symm
  refine ⟨f w0, f w1, f w4, f w5, fun g hg => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> exact hmemJ _
  · rw [ht]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, e02, e13, e46, e57]
    group

theorem perfect_J :
    ⁅Subgroup.closure ({bElt 9, bElt 14} : Set NativeSporadic.Co1),
      Subgroup.closure ({bElt 9, bElt 14} : Set NativeSporadic.Co1)⁆ =
      Subgroup.closure ({bElt 9, bElt 14} : Set NativeSporadic.Co1) := by
  obtain ⟨-, -, -, -, -, -, -, -, hX, hY⟩ := b_facts
  obtain ⟨a, b, c, d, habcd, hx⟩ := eq_commutators (t := bElt 9) (matHom_bElt 9) hX
  obtain ⟨a', b', c', d', habcd', hy⟩ := eq_commutators (t := bElt 14) (matHom_bElt 14) hY
  have hall : ∀ g ∈ [a, b, c, d] ++ [a', b', c', d'],
      g ∈ Subgroup.closure ({bElt 9, bElt 14} : Set NativeSporadic.Co1) :=
    List.forall_mem_append.mpr ⟨habcd, habcd'⟩
  exact perfect_closure_pair hall (by rw [hx]; rfl) (by rw [hy]; rfl)

theorem getElem!_toArray_map {α β : Type*} [Inhabited α] [Inhabited β] (l : List α)
    (f : α → β) {i : ℕ} (hi : i < l.length) : (l.map f).toArray[i]! = f l[i]! := by
  rw [getElem!_pos (l.map f).toArray i (by simpa using hi), getElem!_pos l i hi]
  simp

theorem getElem!_ofFn (f : Fin 24 → ℕ) {i : ℕ} (hi : i < 24) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi)]
  simp

theorem getD_eq_getElem! {a : Array ℕ} {i : ℕ} (hi : i < a.size) : a[i]?.getD 0 = a[i]! := by
  rw [getElem!_pos a i hi, Array.getElem?_eq_getElem hi, Option.getD_some]

@[expose] noncomputable def hElt
    (i : ℕ) : NativeSporadic.Co1 :=
  CFSG.Sporadic.Co1.Module.Odd.lineEval [bElt 9, bElt 14] (Data.oddHWords[i]!)

theorem oddX_eq : Native.oddX = Native.oddReg Native.oddBRegs 9 := rfl

theorem oddY_eq : Native.oddY = Native.oddReg Native.oddBRegs 14 := rfl

attribute [local irreducible] Native.oddX Native.oddY

theorem oddHsB_get {i : ℕ} (hi : i < 24) :
    Native.oddHsB[i]! = lineRows #[Native.oddReg Native.oddBRegs 9,
      Native.oddReg Native.oddBRegs 14] (Data.oddHWords[i]!) := by
  have hlen : Data.oddHWords.length = 24 := rfl
  have h1 : Native.oddHsB = (Data.oddHWords.map (lineRows #[Native.oddX, Native.oddY])).toArray :=
    rfl
  rw [h1, getElem!_toArray_map _ _ (by rw [hlen]; exact hi), oddX_eq, oddY_eq]

theorem matHom_hElt
    {i : ℕ} (hi : i < 24) :
    matHom (hElt i) = rowsMatrix 24 (Native.oddHsB[i]!) := by
  rw [oddHsB_get hi]
  exact matHom_word _

theorem oddUs_get (Hs : Array (Array ℕ)) (u0 u1 : ℕ) {i : ℕ} (hi : i < 24) :
    (Native.oddUs Hs u0 u1)[i]! = vecMulN 24 (transposeRows 24 Hs[i]!)
      (if Data.oddSel.getD i 0 = 0 then u0 else u1) := by
  unfold Native.oddUs
  rw [getElem!_ofFn _ hi]

theorem oddUs_size (Hs : Array (Array ℕ)) (u0 u1 : ℕ) : (Native.oddUs Hs u0 u1).size = 24 := by
  unfold Native.oddUs
  simp

theorem basis_facts :
    rowsMatrix 24 Native.oddY *ᵥ toVecD 24 (Data.oddSeeds.getD 0 0) =
      toVecD 24 (Data.oddSeeds.getD 0 0) ∧
    rowsMatrix 24 Native.oddY *ᵥ toVecD 24 (Data.oddSeeds.getD 1 0) =
      toVecD 24 (Data.oddSeeds.getD 1 0) ∧
    rowsMatrix 24 (Native.inv Native.oddBT) * rowsMatrix 24 Native.oddBT = 1 := by
  have h := odd_b_basis
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨(CFSG.Sporadic.Co1.Module.Odd.isFixedN_iff _ (by norm_num [Data.oddSeeds])).1 h1,
    (CFSG.Sporadic.Co1.Module.Odd.isFixedN_iff _ (by norm_num [Data.oddSeeds])).1 h2, ?_⟩
  rw [← rowsMatrix_mulRows, h3, rowsMatrix_idRows]

theorem oddCandOK_spec {x y s : Array ℕ} {Hs : Array (Array ℕ)} {BT BTi : Array ℕ} {u0 u1 : ℕ}
    (h : Native.oddCandOK x y s Hs BT BTi u0 u1 = true) :
    (∀ i < 24, vecMulN 24 (transposeRows 24 (transposeRows 24
      (mulRows 24 BTi (Native.oddUs Hs u0 u1)))) BT[i]! = (Native.oddUs Hs u0 u1)[i]!) ∧
    (mulRows 24 (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) x =
        mulRows 24 x (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) →
      mulRows 24 (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) y =
        mulRows 24 y (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) →
      mulRows 24 (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) s =
        mulRows 24 s (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) →
      transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1)) ≠ idRows 24 →
      ∀ p ∈ [3, 5, 7, 13],
        powRows 24 (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) p ≠
          idRows 24) := by
  unfold Native.oddCandOK at h
  dsimp only at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hA, hBC⟩ := h
  refine ⟨fun i hi => beq_iff_eq.mp (hA i (List.mem_range.2 hi)), fun h1 h2 h3 h4 => ?_⟩
  have hB : (mulRows 24 (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) x ==
        mulRows 24 x (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) &&
      mulRows 24 (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) y ==
        mulRows 24 y (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) &&
      mulRows 24 (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) s ==
        mulRows 24 s (transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1))) &&
      transposeRows 24 (mulRows 24 BTi (Native.oddUs Hs u0 u1)) != idRows 24) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  rw [hB, Bool.not_true, Bool.false_or, List.all_eq_true] at hBC
  exact fun p hp => bne_iff_ne.mp (hBC p hp)

theorem cand_spec
    (m : NativeSporadic.Co1) (hx : m * bElt 9 = bElt 9 * m)
    (hy : m * bElt 14 = bElt 14 * m) (hs : m * sBc = sBc * m) (hm : m ≠ 1) {p : ℕ}
    (hp : p ∈ [3, 5, 7, 13]) : m ^ p ≠ 1 := by
  obtain ⟨hw0, hw1, hinv⟩ := basis_facts
  obtain ⟨hvs, hreg, -⟩ := b_facts
  have hv9 := (hreg 9 (by simp)).1
  have hv14 := (hreg 14 (by simp)).1
  have hY : matHom (bElt 14) = rowsMatrix 24 Native.oddY := by rw [oddY_eq]; exact matHom_bElt 14
  have hX : matHom (bElt 9) = rowsMatrix 24 Native.oddX := by rw [oddX_eq]; exact matHom_bElt 9
  have hcomm : ∀ i, m * hElt i = hElt i * m := fun i => commute_lineEval (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hx
    · exact hy) _
  have hfixY : ∀ v : Fin 24 → ZMod 2, rowsMatrix 24 Native.oddY *ᵥ v = v →
      rowsMatrix 24 Native.oddY *ᵥ (matHom m *ᵥ v) = matHom m *ᵥ v := by
    intro v hv
    rw [← hY, mulVec_mulVec, ← map_mul, ← hy, map_mul, ← mulVec_mulVec, hY, hv]
  obtain ⟨u0, hu0lt, hu0⟩ := CFSG.Sporadic.Co1.Module.Odd.exists_toVecD
    (matHom m *ᵥ toVecD 24 (Data.oddSeeds.getD 0 0))
  obtain ⟨u1, hu1lt, hu1⟩ := CFSG.Sporadic.Co1.Module.Odd.exists_toVecD
    (matHom m *ᵥ toVecD 24 (Data.oddSeeds.getD 1 0))
  have hmemL : ∀ u < 2 ^ 24, ∀ w, toVecD 24 u = matHom m *ᵥ toVecD 24 w →
      rowsMatrix 24 Native.oddY *ᵥ toVecD 24 w = toVecD 24 w →
      u ∈ fixList [transposeRows 24 Native.oddY] := by
    intro u hu w hw hfw
    refine (CFSG.Sporadic.Co1.Module.Odd.mem_fixList [Native.oddY] u).2 ⟨hu, fun M hM => ?_⟩
    rw [List.mem_singleton.1 hM, hw]
    exact hfixY _ hfw
  have hc := odd_b_cand
  simp only [Native.oddCandCheckOf, List.all_eq_true] at hc
  obtain ⟨hbasis, himp⟩ :=
    oddCandOK_spec (hc u0 (hmemL u0 hu0lt _ hu0 hw0) u1 (hmemL u1 hu1lt _ hu1 hw1))
  generalize hUs : Native.oddUs Native.oddHsB u0 u1 = Us at hbasis himp
  generalize hT : transposeRows 24 (mulRows 24 (Native.inv Native.oddBT) Us) = T at hbasis himp
  have hTm : rowsMatrix 24 T = matHom m := by
    refine eq_of_agree_rows hinv fun i hi => ?_
    have hbi := hbasis i hi
    have hsz : i < Native.oddBT.size := by
      rw [show Native.oddBT = Native.oddUs Native.oddHsB (Data.oddSeeds.getD 0 0)
        (Data.oddSeeds.getD 1 0) from rfl, oddUs_size]
      exact hi
    rw [getD_eq_getElem! hsz, rowsMatrix_mulVec, hbi, ← hUs, oddUs_get _ _ _ hi]
    rw [show Native.oddBT = Native.oddUs Native.oddHsB (Data.oddSeeds.getD 0 0)
      (Data.oddSeeds.getD 1 0) from rfl, oddUs_get _ _ _ hi, ← rowsMatrix_mulVec,
      ← rowsMatrix_mulVec, ← matHom_hElt hi, mulVec_mulVec, ← map_mul, hcomm i, map_mul,
      ← mulVec_mulVec]
    have hsel' : toVecD 24 (if Data.oddSel.getD i 0 = 0 then u0 else u1) =
        matHom m *ᵥ toVecD 24 (if Data.oddSel.getD i 0 = 0 then Data.oddSeeds.getD 0 0 else
          Data.oddSeeds.getD 1 0) := by
      by_cases hsel : Data.oddSel.getD i 0 = 0
      · simp only [hsel, ↓reduceIte]
        exact hu0
      · simp only [hsel, ↓reduceIte]
        exact hu1
    rw [hsel']
  have hvT : validRows T = true := by rw [← hT]; exact validRows_transposeRows _
  have hcommT : ∀ (X : Array ℕ) (g : NativeSporadic.Co1), validRows X = true →
      matHom g = rowsMatrix 24 X → m * g = g * m → mulRows 24 T X = mulRows 24 X T := by
    intro X g hXv hg hmg
    refine CFSG.Sporadic.Co1.Module.Odd.rowsMatrix_injective_of_valid
      (CFSG.Sporadic.Co1.Module.Odd.validRows_mulRows hvT hXv)
      (CFSG.Sporadic.Co1.Module.Odd.validRows_mulRows hXv hvT) ?_
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, hTm, ← hg, ← map_mul, ← map_mul, hmg]
  have hTne : T ≠ idRows 24 := by
    intro h
    apply hm
    apply matHom_injective
    rw [← hTm, h, rowsMatrix_idRows, map_one]
  have hpow := himp (hcommT _ _ (by rw [oddX_eq]; exact hv9) hX hx)
    (hcommT _ _ (by rw [oddY_eq]; exact hv14) hY hy) (hcommT _ _ hvs matHom_sBc hs) hTne p hp
  intro hmp
  apply hpow
  refine CFSG.Sporadic.Co1.Module.Odd.rowsMatrix_injective_of_valid (validRows_powRows hvT p)
    CFSG.Sporadic.Co1.Module.Odd.validRows_idRows ?_
  rw [rowsMatrix_powRows, hTm, ← map_pow, hmp, map_one, rowsMatrix_idRows]

@[expose, instance_reducible] def co1SubAct (N : Subgroup NativeSporadic.Co1) :
    MulAction N (Fin 24 → ZMod 2) where
  smul g v := co1Act g v
  one_smul v := CFSG.Sporadic.Co1.Module.co1Act_one v
  mul_smul g h v := co1Act_mul g h v

section TwoB

variable {Q : Subgroup NativeSporadic.Co1} (hQt : ∀ q ∈ Q, q * sBc = sBc * q)
  (hnorm : ∀ c : NativeSporadic.Co1, c * sBc = sBc * c → ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
  (hodd : Odd (Nat.card Q))

theorem comm_sBc
    {c : NativeSporadic.Co1}
    (hc : c ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)) : c * sBc = sBc * c := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  exact hc

theorem comm_sBc_inv {c : NativeSporadic.Co1} (hc : c * sBc = sBc * c) :
    c⁻¹ * sBc = sBc * c⁻¹ :=
  comm_inv_of_comm hc

include hnorm hodd in
theorem inter_KB_trivial :
    ∀ q ∈ Q, q ∈ KB → q = 1 := by
  intro q hq hqK
  have hN : (Q.subgroupOf KB).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hk : (k : NativeSporadic.Co1) * sBc = sBc * k := comm_sBc (Subgroup.mem_inf.mp k.2).2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hnorm k hk n hn⟩
  have hcard : Nat.card (Q.subgroupOf KB) ∣ Nat.card Q := by
    rw [← Subgroup.card_map_of_injective (f := KB.subtype) Subtype.val_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h0 := KB_noOddNormal _ hN (hodd.of_dvd_nat hcard)
  have hmem : (⟨q, hqK⟩ : KB) ∈ Q.subgroupOf KB := Subgroup.mem_subgroupOf.mpr hq
  rw [h0, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

include hQt hnorm hodd in
theorem free_fixB :
    ∀ q ∈ Q, ∀ v : Fin 24 → ZMod 2, co1Act sBc v = v → v ≠ 0 →
    co1Act q v = v → q = 1 := by
  intro q hq v hv hv0 hqv
  obtain ⟨t, ht, rfl⟩ := fix_eq_orbit hv hv0
  have hts := comm_sBc ht
  have hq' : t⁻¹ * q * t⁻¹⁻¹ ∈ Q := hnorm t⁻¹ (comm_sBc_inv hts) q hq
  have hqs := hQt q hq
  have hq'K : t⁻¹ * q * t⁻¹⁻¹ ∈ KB := by
    refine mem_KB ?_ ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact conj_comm_of_comm hts hqs
    · rw [inv_inv, co1Act_mul, co1Act_mul, hqv, co1Act_inv_apply]
  exact eq_one_of_conj_eq_one (inter_KB_trivial hnorm hodd _ hq' hq'K)

include hQt hnorm hodd in
theorem card_dvd_4095 :
    Nat.card Q ∣ 4095 := by
  have hfin := CFSG.Sporadic.Co1.Module.finite_co1
  have h0 : co1Act sBc 0 = 0 := by
    rw [CFSG.Sporadic.Co1.Module.co1Act_eq_mulVec, mulVec_zero]
  have hS : ({v : Fin 24 → ZMod 2 | co1Act sBc v = v} \ {0}).ncard = 4095 := by
    rw [Set.ncard_sdiff_singleton_of_mem (show (0 : Fin 24 → ZMod 2) ∈
      {v : Fin 24 → ZMod 2 | co1Act sBc v = v} from h0), ncard_fix_sBc]
    norm_num
  rw [← hS]
  refine @card_dvd_ncard_of_free Q (Fin 24 → ZMod 2) _ (co1SubAct Q) _ _ (Set.toFinite _)
    (fun g v hv => ⟨?_, ?_⟩) fun g v hv h => Subtype.ext (free_fixB hQt hnorm hodd g g.2 v
      hv.1 hv.2 h)
  · show co1Act sBc (co1Act g v) = co1Act g v
    rw [← co1Act_mul, ← hQt g g.2, co1Act_mul, hv.1]
  · intro hg0
    apply hv.2
    refine co1Act_injective (g : NativeSporadic.Co1) ?_
    show co1Act g v = co1Act g 0
    rw [show co1Act (g : NativeSporadic.Co1) 0 = 0 by
      rw [CFSG.Sporadic.Co1.Module.co1Act_eq_mulVec, mulVec_zero]]
    exact hg0

include hnorm in
theorem mem_normalizerB {c : NativeSporadic.Co1}
    (hc : c ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)) :
    c ∈ Subgroup.normalizer (Q : Set NativeSporadic.Co1) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hnorm c (comm_sBc hc) h
  · intro hh
    have := hnorm c⁻¹ (comm_sBc_inv (comm_sBc hc)) _ hh
    rwa [conj_conj_inv] at this

include hQt hnorm hodd in
theorem centralizes_J :
    ∀ g ∈ Subgroup.closure ({bElt 9, bElt 14} : Set NativeSporadic.Co1),
    ∀ q ∈ Q, q * g = g * q := by
  have hfin := CFSG.Sporadic.Co1.Module.finite_co1
  refine centralizes_of_perfect_of_dvd hodd (card_dvd_4095 hQt hnorm hodd) ?_ perfect_J
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with hg | hg
  · rw [hg]; exact mem_normalizerB hnorm (bElt_mem_cent (by simp))
  · rw [Set.mem_singleton_iff.mp hg]; exact mem_normalizerB hnorm (bElt_mem_cent (by simp))

end TwoB

theorem centOddFreeIn_B :
    CentOddFreeIn (⊤ : Subgroup NativeSporadic.Co1) sBc := by
  intro Q _ hQt hnorm' hodd
  have hnorm : ∀ c : NativeSporadic.Co1, c * sBc = sBc * c → ∀ q ∈ Q, c * q * c⁻¹ ∈ Q :=
    fun c hc => hnorm' c trivial hc
  have hfin := CFSG.Sporadic.Co1.Module.finite_co1
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  by_contra hm1
  have hne : Nat.card Q ≠ 1 := by
    intro h1
    apply hm1
    have := (Nat.card_eq_one_iff_unique.mp h1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨m, hm⟩ : Q) 1)
  obtain ⟨p, hp, hpQ⟩ := Nat.exists_prime_and_dvd hne
  have hp' : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) p hpQ
  have hpL := prime_dvd_4095 hp (hpQ.trans (card_dvd_4095 hQt hnorm hodd))
  have hq1 : (q : NativeSporadic.Co1) ≠ 1 := by
    intro h
    have : q = 1 := Subtype.ext h
    rw [this, orderOf_one] at hq
    exact hp.one_lt.ne hq
  have hqp : (q : NativeSporadic.Co1) ^ p = 1 := by
    rw [← SubgroupClass.coe_pow, ← hq, pow_orderOf_eq_one, OneMemClass.coe_one]
  have hx := centralizes_J hQt hnorm hodd _ (Subgroup.subset_closure (Set.mem_insert _ _)) q q.2
  have hy := centralizes_J hQt hnorm hodd _ (Subgroup.subset_closure
    (Set.mem_insert_of_mem _ rfl)) q q.2
  exact cand_spec q hx hy (hQt q q.2) hq1 hpL hqp

end CFSG.Sporadic.Co1Schreier.OddB
