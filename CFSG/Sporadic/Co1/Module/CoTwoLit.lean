module

public import CFSG.Sporadic.Co1.Module.CoTwoChain
public import CFSG.Sporadic.Co1.Module.CoTwoLitInputs
public import CFSG.Sporadic.Co1.Module.InvFam

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.CoTwo

open CFSG.Blueprint CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.CoTwoNative

variable {W : CoTwoW}

theorem lit_lenA (hW : CoTwoOK W) : W.RA.length = 24 := by
  have h := InvFam.progK_len progA 2 hW.progA
  have hp : progA.length = 22 := rfl
  omega

theorem lit_lenS (hW : CoTwoOK W) : W.RS.length = 13 := by
  have h := InvFam.progK_len progS 2 hW.progS
  have hp : progS.length = 11 := rfl
  omega

theorem lit_takeA (hW : CoTwoOK W) : W.RA.take 2 = [getL 0 W.RA 0, getL 0 W.RA 1] := by
  have hl := lit_lenA hW
  match h : W.RA, hl with
  | a :: b :: rest, _ => simp [InvFam.getL_eq]

theorem lit_regsA (hW : CoTwoOK W) : regsRowsA = (W.RA.map (unpackR 24)).toArray := by
  have e : initRowsA = ((W.RA.take 2).map (unpackR 24)).toArray := by
    rw [lit_takeA hW, initRowsA, hW.rA, hW.rB]
    rfl
  rw [regsRowsA, e, prog_sound hW.progA]

theorem lit_rrA (hW : CoTwoOK W) {i : ℕ} (hi : i < 24) : rrA i = unpackR 24 (getL 0 W.RA i) := by
  have hl := lit_lenA hW
  rw [rrA, lit_regsA hW]
  simp [InvFam.getL_eq, hl, hi]

theorem lit_takeS (hW : CoTwoOK W) : W.RS.take 2 = [getL 0 W.RA 13, getL 0 W.RA 18] := by
  have hl := lit_lenS hW
  have h0 := hW.s0
  have h1 := hW.s1
  match h : W.RS, hl with
  | a :: b :: rest, _ =>
    rw [h] at h0 h1
    rw [← h0, ← h1]
    rfl

theorem lit_regsS (hW : CoTwoOK W) : regsRowsS = (W.RS.map (unpackR 24)).toArray := by
  have e : initRowsS = ((W.RS.take 2).map (unpackR 24)).toArray := by
    rw [lit_takeS hW, initRowsS, lit_rrA hW (by norm_num : 13 < 24),
      lit_rrA hW (by norm_num : 18 < 24)]
    rfl
  rw [regsRowsS, e, prog_sound hW.progS]

theorem lit_rrS (hW : CoTwoOK W) {i : ℕ} (hi : i < 13) : rrS i = unpackR 24 (getL 0 W.RS i) := by
  have hl := lit_lenS hW
  rw [rrS, lit_regsS hW]
  simp [InvFam.getL_eq, hl, hi]

theorem lit_trA (hW : CoTwoOK W) {i : ℕ} (hi : i < 24) : trK 24 (getL 0 W.RA i) = getL 0 W.RTA i :=
  beq_iff.1 ((allN_iff _ _).1 hW.trA i (by rw [InvFam.lenL_eq, lit_lenA hW]; exact hi))

theorem lit_trS (hW : CoTwoOK W) {i : ℕ} (hi : i < 13) : trK 24 (getL 0 W.RS i) = getL 0 W.RTS i :=
  beq_iff.1 ((allN_iff _ _).1 hW.trS i (by rw [InvFam.lenL_eq, lit_lenS hW]; exact hi))


theorem lit_pmA (hW : CoTwoOK W) {i : ℕ} (hi : i < 24) : PM (regA i) (getL 0 W.RA i) := by
  unfold PM
  rw [← lit_rrA hW hi]
  exact mat_regA i

theorem lit_pmS (hW : CoTwoOK W) {i : ℕ} (hi : i < 13) : PM (regS i) (getL 0 W.RS i) := by
  unfold PM
  rw [← lit_rrS hW hi]
  exact mat_regS i

theorem lit_actA (hW : CoTwoOK W) {i : ℕ} (hi : i < 24) (v : ℕ) :
    co1Act (regA i) (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 W.RTA i) v) :=
  pm_act (lit_pmA hW hi) (lit_trA hW hi) v

theorem lit_actS (hW : CoTwoOK W) {i : ℕ} (hi : i < 13) (v : ℕ) :
    co1Act (regS i) (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 W.RTS i) v) :=
  pm_act (lit_pmS hW hi) (lit_trS hW hi) v

theorem lit_fixAllA (hW : CoTwoOK W) {I vs : List ℕ} (hI : ∀ i ∈ I, i < 24)
    (h : fixAllK W.RTA I vs = true) :
    ∀ i ∈ I, ∀ v ∈ vs, co1Act (regA i) (toVecD 24 v) = toVecD 24 v := by
  intro i hi v hv
  rw [lit_actA hW (hI i hi), InvFam.fixAll_spec h i hi v hv]

theorem lit_fixAllS (hW : CoTwoOK W) {I vs : List ℕ} (hI : ∀ i ∈ I, i < 13)
    (h : fixAllK W.RTS I vs = true) :
    ∀ i ∈ I, ∀ v ∈ vs, co1Act (regS i) (toVecD 24 v) = toVecD 24 v := by
  intro i hi v hv
  rw [lit_actS hW (hI i hi), InvFam.fixAll_spec h i hi v hv]

theorem lit_finite : Finite NativeSporadic.Co1 :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)

theorem lit_fixP (hW : CoTwoOK W) : ∀ s ∈ [9, 10, 14, 15],
    co1Act (regA s) (toVecD 24 2) = toVecD 24 2 ∧
      co1Act (regA s) (toVecD 24 y₀code) = toVecD 24 y₀code := by
  have hI : ∀ i ∈ [9, 10, 14, 15], i < 24 := by decide
  intro s hs
  exact ⟨lit_fixAllA hW hI hW.fixP s hs 2 (by simp),
    lit_fixAllA hW hI hW.fixP s hs y₀code (by simp)⟩

theorem lit_fixE (hW : CoTwoOK W) : ∀ s ∈ [19, 20], co1Act (regA s) (toVecD 24 2) = toVecD 24 2 := by
  have hI : ∀ i ∈ [19, 20], i < 24 := by decide
  intro s hs
  exact lit_fixAllA hW hI hW.fixE s hs 2 (by simp)

theorem lit_fixY (hW : CoTwoOK W) : ∀ s ∈ [13, 18],
    co1Act (regA s) (toVecD 24 y₀code) = toVecD 24 y₀code := by
  have hI : ∀ i ∈ [13, 18], i < 24 := by decide
  intro s hs
  exact lit_fixAllA hW hI hW.fixY s hs y₀code (by simp)

theorem lit_pm_inv {x : NativeSporadic.Co1} {A B : ℕ} (hx : PM x A) (h : mulF 24 A B = idF 24) :
    PM x⁻¹ B := by
  unfold PM at *
  refine matHom_inv_eq ?_
  rw [hx, rM_mul, h, unpackR_idF, rowsMatrix_idRows]

theorem lit_inv_of (hW : CoTwoOK W) {a b : ℕ} (ha : a < 24) (hb : b < 24)
    (h : mulF 24 (getL 0 W.RA a) (getL 0 W.RA b) = idF 24) : regA b = (regA a)⁻¹ :=
  matHom_injective ((lit_pmA hW hb).trans (lit_pm_inv (lit_pmA hW ha) h).symm)

theorem lit_inv (hW : CoTwoOK W) : regA 11 = (regA 9)⁻¹ ∧ regA 12 = (regA 10)⁻¹ ∧
    regA 16 = (regA 14)⁻¹ ∧ regA 17 = (regA 15)⁻¹ ∧ regA 21 = (regA 19)⁻¹ ∧
    regA 22 = (regA 20)⁻¹ := by
  have h := (allN_iff _ _).1 (andB_true_iff.1 hW.inv).2
  have e : ∀ l < 6, mulF 24 (getL 0 W.RA (getL 0 [9, 10, 14, 15, 19, 20] l))
      (getL 0 W.RA (getL 0 [11, 12, 16, 17, 21, 22] l)) = idF 24 :=
    fun l hl => beq_iff.1 (h l hl)
  exact ⟨lit_inv_of hW (by norm_num) (by norm_num) (e 0 (by norm_num)),
    lit_inv_of hW (by norm_num) (by norm_num) (e 1 (by norm_num)),
    lit_inv_of hW (by norm_num) (by norm_num) (e 2 (by norm_num)),
    lit_inv_of hW (by norm_num) (by norm_num) (e 3 (by norm_num)),
    lit_inv_of hW (by norm_num) (by norm_num) (e 4 (by norm_num)),
    lit_inv_of hW (by norm_num) (by norm_num) (e 5 (by norm_num))⟩

theorem lit_comm_of (hW : CoTwoOK W) {c ia ib a b : ℕ} (hc : c < 24) (hia : ia < 24)
    (hib : ib < 24) (ha : a < 24) (hb : b < 24) (h : commK W.RA c ia ib a b = true) :
    regA c = regA ia * regA ib * regA a * regA b := by
  have h2 := pm_mul (pm_mul (pm_mul (lit_pmA hW hia) (lit_pmA hW hib)) (lit_pmA hW ha))
    (lit_pmA hW hb)
  have h1 := lit_pmA hW hc
  have e : getL 0 W.RA c = mulF 24 (mulF 24 (mulF 24 (getL 0 W.RA ia) (getL 0 W.RA ib))
      (getL 0 W.RA a)) (getL 0 W.RA b) := beq_iff.1 h
  rw [e] at h1
  exact matHom_injective (h1.trans h2.symm)

theorem lit_comm (hW : CoTwoOK W) : regA 13 = regA 11 * regA 12 * regA 9 * regA 10 ∧
    regA 18 = regA 16 * regA 17 * regA 14 * regA 15 ∧
    regA 23 = regA 21 * regA 22 * regA 19 * regA 20 := by
  obtain ⟨h1, h2⟩ := andB_true_iff.1 hW.comm
  obtain ⟨h2, h3⟩ := andB_true_iff.1 h2
  exact ⟨lit_comm_of hW (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1,
    lit_comm_of hW (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h2,
    lit_comm_of hW (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3⟩

@[expose] def stabV (v : Vec24) : Subgroup NativeSporadic.Co1 where
  carrier := {g | co1Act g v = v}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Odd.co1Act_mul', hh, hg]
  one_mem' := Odd.co1Act_one' v
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    exact InvFam.co1Act_inv hg

theorem mem_stabV {g : NativeSporadic.Co1} {v : Vec24} : g ∈ stabV v ↔ co1Act g v = v := Iff.rfl

@[expose] def chainC (H : Subgroup NativeSporadic.Co1) : ℕ → Subgroup NativeSporadic.Co1
  | 0 => H
  | n + 1 => chainC H n ⊓ stabV (toVecD 24 (baseS.getD n 0))

theorem mem_chainC {H : Subgroup NativeSporadic.Co1} {g : NativeSporadic.Co1} :
    ∀ {n : ℕ}, g ∈ chainC H n ↔ g ∈ H ∧
      ∀ j < n, co1Act g (toVecD 24 (baseS.getD j 0)) = toVecD 24 (baseS.getD j 0)
  | 0 => by simp [chainC]
  | n + 1 => by
    rw [chainC, Subgroup.mem_inf, mem_chainC, mem_stabV]
    constructor
    · rintro ⟨⟨hH, hj⟩, hn⟩
      refine ⟨hH, fun j hj' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | rfl
      · exact hj j h
      · exact hn
    · rintro ⟨hH, hj⟩
      exact ⟨⟨hH, fun j h => hj j (by omega)⟩, hj n (by omega)⟩

theorem take_mem' {base : List ℕ} {j n : ℕ} (hj : j < n) (hn : n ≤ base.length) :
    base.getD j 0 ∈ base.take n := by
  have hjt : j < (base.take n).length := by rw [List.length_take]; omega
  have e : (base.take n)[j] = base.getD j 0 := by
    rw [List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
  rw [← e]
  exact List.getElem_mem hjt

theorem getD_mem' {α : Type*} {L : List α} {i : ℕ} (d : α) (hi : i < L.length) : L.getD i d ∈ L := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem le_ncard_of_inj' {α : Type*} {s : Set α} {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite) : n ≤ s.ncard := by
  have hsub : f '' Set.Iio n ⊆ s := by
    rintro _ ⟨i, hi, rfl⟩
    exact hf i hi
  have hinj' : Set.InjOn f (Set.Iio n) := fun i hi j hj e => hinj i hi j hj e
  have hc : (f '' Set.Iio n).ncard = n := by
    rw [hinj'.ncard_image, Set.ncard_Iio_nat]
  calc n = (f '' Set.Iio n).ncard := hc.symm
    _ ≤ s.ncard := Set.ncard_le_ncard hsub hs

theorem lit_chain_card (hW : CoTwoOK W) :
    ∀ n ≤ baseS.length, ((List.range n).map fun j => W.SZ.getD j 0).prod *
      Nat.card (chainC (Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1)) n) ≤
        Nat.card (Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1)) := by
  have hfin := lit_finite
  have hcs := @card_step NativeSporadic.Co1 Vec24 _ co1Act hfin Odd.co1Act_mul' Odd.co1Act_one'
  have hbase := InvFam.bnd_spec hW.base
  set H := Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1) with hH
  intro n
  induction n with
  | zero => intro _; simp [chainC]
  | succ n ih =>
    intro hn
    have hn' : n < baseS.length := hn
    have ih' := ih hn'.le
    have hLV : W.LV.getD n [] ∈ W.LV := getD_mem' [] (by rw [hW.lenLV]; exact hn')
    have hIr : ∀ i ∈ W.LV.getD n [], i < 13 := fun i hi => by
      have := InvFam.bnd_spec hW.idx i (List.mem_flatten.2 ⟨_, hLV, hi⟩)
      rwa [InvFam.lenL_eq, lit_lenS hW] at this
    have hfix := lit_fixAllS hW hIr (hW.fix n hn')
    have hmem : ∀ l ∈ W.LV.getD n [], regS l ∈ chainC H n := by
      intro l hl
      rw [mem_chainC]
      exact ⟨regS_mem_closure l, fun j hj => hfix l hl _ (take_mem' hj hn'.le)⟩
    obtain ⟨t, ht, hinj⟩ := InvFam.vec_family (chainC H n) (hW.tree n hn')
      (hbase _ (getD_mem' 0 hn')) (fun l => regS (getL 0 (W.LV.getD n []) l))
      (fun l hl => hmem _ (InvFam.getL_mem hl))
      (fun l hl v => lit_actS hW (hIr _ (InvFam.getL_mem hl)) v)
    have horb : W.SZ.getD n 0 ≤
        (orbitSet co1Act (chainC H n) (toVecD 24 (baseS.getD n 0))).ncard :=
      le_ncard_of_inj' (fun i => co1Act (t i) (toVecD 24 (baseS.getD n 0)))
        (fun i hi => ⟨t i, (ht i hi).1, rfl⟩) hinj (Set.toFinite _)
    have hstep := hcs (H := chainC H n) (K := chainC H (n + 1)) inf_le_left
      (x := toVecD 24 (baseS.getD n 0)) (fun g hg => (Subgroup.mem_inf.1 hg).2) horb
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    calc ((List.range n).map fun j => W.SZ.getD j 0).prod * W.SZ.getD n 0 *
          Nat.card (chainC H (n + 1))
        = ((List.range n).map fun j => W.SZ.getD j 0).prod *
            (W.SZ.getD n 0 * Nat.card (chainC H (n + 1))) := by ring
      _ ≤ ((List.range n).map fun j => W.SZ.getD j 0).prod * Nat.card (chainC H n) :=
          Nat.mul_le_mul_left _ hstep
      _ ≤ _ := ih'

theorem lit_two_ge (hW : CoTwoOK W) :
    898128000 ≤ Nat.card (Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1)) := by
  have hfin := lit_finite
  have h := lit_chain_card hW baseS.length le_rfl
  have hpos : 1 ≤ Nat.card (chainC (Subgroup.closure ({regA 13, regA 18} :
      Set NativeSporadic.Co1)) baseS.length) := Nat.card_pos
  calc 898128000 ≤ ((List.range baseS.length).map fun j => W.SZ.getD j 0).prod := hW.prod
    _ ≤ ((List.range baseS.length).map fun j => W.SZ.getD j 0).prod *
          Nat.card (chainC (Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1))
            baseS.length) := Nat.le_mul_of_pos_right _ hpos
    _ ≤ _ := h

theorem lit_three_ge (hW : CoTwoOK W) :
    47104 * Nat.card (Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1)) ≤
      Nat.card (Subgroup.closure ({regA 13, regA 18, regA 23} : Set NativeSporadic.Co1)) := by
  have hfin := lit_finite
  have hcs := @card_step NativeSporadic.Co1 Vec24 _ co1Act hfin Odd.co1Act_mul' Odd.co1Act_one'
  set H := Subgroup.closure ({regA 13, regA 18, regA 23} : Set NativeSporadic.Co1) with hH
  set K := Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1) with hK
  have hKH : K ≤ H := by
    refine Subgroup.closure_mono ?_
    rintro g (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hy := lit_fixY hW
  have hKy : K ≤ stabV (toVecD 24 y₀code) := by
    rw [hK, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hy 13 (by simp)
    · exact hy 18 (by simp)
  have hI : ∀ i ∈ [13, 18, 23], i < 24 := by decide
  obtain ⟨t, ht, hinj⟩ := InvFam.vec_family H hW.ty (by decide)
    (fun l => regA (getL 0 [13, 18, 23] l))
    (fun l hl => by
      have hm := InvFam.getL_mem hl
      refine Subgroup.subset_closure ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr (Or.inl rfl)
      · rw [h]; exact Or.inr (Or.inr rfl))
    (fun l hl v => lit_actA hW (hI _ (InvFam.getL_mem hl)) v)
  have horb : 47104 ≤ (orbitSet co1Act H (toVecD 24 y₀code)).ncard :=
    le_ncard_of_inj' (fun i => co1Act (t i) (toVecD 24 y₀code))
      (fun i hi => ⟨t i, (ht i hi).1, rfl⟩) hinj (Set.toFinite _)
  exact hcs hKH (fun g hg => hKy hg) horb

end CFSG.Sporadic.Co1.Module.CoTwo

end
