module

public import CFSG.Sporadic.Co1.Module.Co2StabLitInputs
public import CFSG.Sporadic.Co1.Module.InvFam
public import CFSG.Sporadic.Co1.Module.CoTwoChain
public import CFSG.Sporadic.Co1.Module.TwoBSylow
public import CFSG.Certificates.Kernel.XorSpan

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.Co2Stab

open CFSG.Blueprint CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree
  CFSG.KC.Co1M CFSG.KC.XorSel CFSG.KC.Syl64 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.TwoBFrame

theorem allN64 {n : ℕ} {f : ℕ → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    have h' : andB (f n) (allN n f) = true := h
    obtain ⟨h1, h2⟩ := andB_iff.1 h'
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

theorem beq64 {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem mulL_length (N : ℕ) : ∀ E : List ℕ, (mulL E N).length = E.length
  | [] => rfl
  | _ :: E => congrArg Nat.succ (mulL_length N E)

theorem mulL_getD (N : ℕ) : ∀ (E : List ℕ) (j : ℕ), j < E.length →
    (mulL E N).getD j 0 = mulF 24 (E.getD j 0) N
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: E, j + 1, h => mulL_getD N E j (by simpa using h)

theorem rM_apply (m : ℕ) (i j : Fin 24) :
    rowsMatrix 24 (unpackR 24 m) i j = if m.testBit (24 * i.val + j.val) then 1 else 0 := by
  have e : (unpackR 24 m)[i.val]?.getD 0 = m / 2 ^ (24 * i.val) % 2 ^ 24 := by
    simp only [unpackR, Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [rowsMatrix_apply, toVecD_apply, e, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [j.isLt, decide_true, Bool.true_and]
  rw [Nat.add_comm]

theorem rM_xor (a b : ℕ) : rowsMatrix 24 (unpackR 24 (a ^^^ b)) =
    rowsMatrix 24 (unpackR 24 a) + rowsMatrix 24 (unpackR 24 b) := by
  ext i j
  rw [Matrix.add_apply, rM_apply, rM_apply, rM_apply, Nat.testBit_xor]
  cases a.testBit (24 * i.val + j.val) <;> cases b.testBit (24 * i.val + j.val) <;> decide

theorem rM_nxor (a b : ℕ) : rowsMatrix 24 (unpackR 24 (Nat.xor a b)) =
    rowsMatrix 24 (unpackR 24 a) + rowsMatrix 24 (unpackR 24 b) := rM_xor a b

theorem rM_zero : rowsMatrix 24 (unpackR 24 0) = 0 := by
  ext i j
  rw [rM_apply]
  simp

theorem rM_idF : rowsMatrix 24 (unpackR 24 (idF 24)) = 1 := by
  rw [unpackR_idF, rowsMatrix_idRows]

theorem rM_eq_of_tv {a b : ℕ} (h : tv 576 a = tv 576 b) :
    rowsMatrix 24 (unpackR 24 a) = rowsMatrix 24 (unpackR 24 b) := by
  ext i j
  rw [rM_apply, rM_apply]
  exact congrFun h ⟨24 * i.val + j.val, by omega⟩

theorem tv_eq_of_rM {a b : ℕ}
    (h : rowsMatrix 24 (unpackR 24 a) = rowsMatrix 24 (unpackR 24 b)) : tv 576 a = tv 576 b := by
  funext k
  have hk := k.isLt
  have e : k.val = 24 * (k.val / 24) + k.val % 24 := (Nat.div_add_mod _ _).symm
  have h2 := congrFun (congrFun h ⟨k.val / 24, by omega⟩) ⟨k.val % 24, by omega⟩
  rw [rM_apply, rM_apply] at h2
  simp only [tv]
  rw [e]
  exact h2

theorem rM_selK_cons (e : ℕ) (L : List ℕ) (c : ℕ) :
    rowsMatrix 24 (unpackR 24 (selK (e :: L) c)) =
      (if c.testBit 0 then rowsMatrix 24 (unpackR 24 e) else 0) +
        rowsMatrix 24 (unpackR 24 (selK L (c >>> 1))) := by
  rw [selK_cons, rM_xor]
  split_ifs
  · rfl
  · rw [rM_zero]

theorem rM_selK_mul {E' : List ℕ} {Y : Matrix (Fin 24) (Fin 24) (ZMod 2)} :
    ∀ (E M : List ℕ), M.length = E.length →
    (∀ j < E.length, rowsMatrix 24 (unpackR 24 (E.getD j 0)) * Y =
      rowsMatrix 24 (unpackR 24 (selK E' (M.getD j 0)))) →
    ∀ c, rowsMatrix 24 (unpackR 24 (selK E c)) * Y =
      rowsMatrix 24 (unpackR 24 (selK E' (selK M c)))
  | [], [], _, _, c => by
    change rowsMatrix 24 (unpackR 24 0) * Y = rowsMatrix 24 (unpackR 24 (selK E' 0))
    rw [selK_zero, rM_zero, zero_mul]
  | [], _ :: _, hl, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _ => absurd hl (by simp)
  | e :: E, m :: M, hl, h, c => by
    have key : (if c.testBit 0 then rowsMatrix 24 (unpackR 24 e) else 0) * Y =
        rowsMatrix 24 (unpackR 24 (selK E' (if c.testBit 0 then m else 0))) := by
      split_ifs
      · exact h 0 (by simp)
      · rw [zero_mul, selK_zero, rM_zero]
    rw [rM_selK_cons, add_mul, selK_cons m M c, selK_xor, rM_xor,
      rM_selK_mul E M (by simpa using hl) (fun j hj => h (j + 1) (by simpa using hj)) (c >>> 1),
      key]

theorem rM_selK_conj (G Gi : ℕ) : ∀ (E : List ℕ) (c : ℕ),
    rowsMatrix 24 (unpackR 24 G) * rowsMatrix 24 (unpackR 24 (selK E c)) *
      rowsMatrix 24 (unpackR 24 Gi) = rowsMatrix 24 (unpackR 24 (selK (conjL G Gi E) c))
  | [], c => by
    change rowsMatrix 24 (unpackR 24 G) * rowsMatrix 24 (unpackR 24 0) *
      rowsMatrix 24 (unpackR 24 Gi) = rowsMatrix 24 (unpackR 24 0)
    rw [rM_zero, mul_zero, zero_mul]
  | e :: E, c => by
    have hc : conjL G Gi (e :: E) = mulF 24 (mulF 24 G e) Gi :: conjL G Gi E := rfl
    have key : rowsMatrix 24 (unpackR 24 G) *
        (if c.testBit 0 then rowsMatrix 24 (unpackR 24 e) else 0) * rowsMatrix 24 (unpackR 24 Gi) =
        if c.testBit 0 then rowsMatrix 24 (unpackR 24 (mulF 24 (mulF 24 G e) Gi)) else 0 := by
      split_ifs
      · rw [rM_mul, rM_mul]
      · rw [mul_zero, zero_mul]
    rw [hc, rM_selK_cons, rM_selK_cons, mul_add, add_mul, rM_selK_conj G Gi E, key]

theorem lineGo_in (H : Subgroup NativeSporadic.Co1) (R : List ℕ) : ∀ fac : List (ℕ × ℕ),
    (∀ p ∈ fac, ∃ x ∈ H, PM x (getL (idF 24) R p.1)) →
    ∀ (acc : ℕ) (x : NativeSporadic.Co1), x ∈ H → PM x acc →
      ∃ z ∈ H, PM z (InvFam.lineGo R fac acc)
  | [], _, _, x, hx, h => ⟨x, hx, h⟩
  | (i, e) :: fac, hf, acc, x, hx, h => by
    obtain ⟨y, hyH, hy⟩ := hf (i, e) List.mem_cons_self
    have e1 : InvFam.lineGo R ((i, e) :: fac) acc =
        InvFam.lineGo R fac (mulF 24 acc (powK 24 (getL (idF 24) R i) e)) :=
      strictN_eq (mulF 24 acc (powK 24 (getL (idF 24) R i) e)) (InvFam.lineGo R fac)
    rw [e1]
    exact lineGo_in H R fac (fun p hp => hf p (List.mem_cons_of_mem _ hp)) _ _
      (H.mul_mem hx (H.pow_mem hyH e)) (pm_mul h (pm_pow hy e))

theorem prog_elems_in (H : Subgroup NativeSporadic.Co1) {R : List ℕ} :
    ∀ (P : List (List (ℕ × ℕ))) (t : ℕ), progK 24 R P t = true →
    (∀ i < t, ∃ x ∈ H, PM x (getL 0 R i)) → ∀ i < R.length, ∃ x ∈ H, PM x (getL 0 R i)
  | [], t, h, hin => by
    have e := InvFam.progK_len [] t h
    simp only [List.length_nil, Nat.add_zero] at e
    intro i hi
    exact hin i (by omega)
  | fac :: P, t, h, hin => by
    obtain ⟨h1, h2, h3⟩ := InvFam.progK_unfold h
    have hlen := InvFam.progK_len (fac :: P) t h
    simp only [List.length_cons] at hlen
    refine prog_elems_in H P (t + 1) h3 (fun i hi => ?_)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hin i hi
    · rw [h2, InvFam.lineK_eq]
      refine lineGo_in H R fac (fun p hp => ?_) (idF 24) 1 H.one_mem pm_one
      have hpt := InvFam.facBelow_spec h1 p hp
      rw [InvFam.getL_idF (by omega)]
      exact hin p.1 hpt

theorem pm_inv64 {x : NativeSporadic.Co1} {A B : ℕ} (hx : PM x A) (h : mulF 24 A B = idF 24) :
    PM x⁻¹ B := by
  unfold PM at *
  refine matHom_inv_eq ?_
  rw [hx, rM_mul, h, unpackR_idF, rowsMatrix_idRows]

@[expose] def chain64 (H : Subgroup NativeSporadic.Co1) (base : List ℕ) :
    ℕ → Subgroup NativeSporadic.Co1
  | 0 => H
  | n + 1 => chain64 H base n ⊓ stabOf (toVecD 24 (base.getD n 0))

theorem mem_chain64 {H : Subgroup NativeSporadic.Co1} {base : List ℕ} {g : NativeSporadic.Co1} :
    ∀ {n : ℕ}, g ∈ chain64 H base n ↔ g ∈ H ∧
      ∀ j < n, co1Act g (toVecD 24 (base.getD j 0)) = toVecD 24 (base.getD j 0)
  | 0 => by simp [chain64]
  | n + 1 => by
    rw [chain64, Subgroup.mem_inf, mem_chain64, mem_stabOf]
    constructor
    · rintro ⟨⟨hH, hj⟩, hn⟩
      refine ⟨hH, fun j hj' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | rfl
      · exact hj j h
      · exact hn
    · rintro ⟨hH, hj⟩
      exact ⟨⟨hH, fun j h => hj j (by omega)⟩, hj n (by omega)⟩

theorem take_mem64 {base : List ℕ} {j n : ℕ} (hj : j < n) (hn : n ≤ base.length) :
    base.getD j 0 ∈ base.take n := by
  have hjt : j < (base.take n).length := by rw [List.length_take]; omega
  have e : (base.take n)[j] = base.getD j 0 := by
    rw [List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
  rw [← e]
  exact List.getElem_mem hjt

theorem getD_mem64 {α : Type*} {L : List α} {i : ℕ} (d : α) (hi : i < L.length) : L.getD i d ∈ L := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem le_ncard64 {α : Type*} {s : Set α} {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) (hs : s.Finite) : n ≤ s.ncard := by
  have hsub : f '' Set.Iio n ⊆ s := by
    rintro _ ⟨i, hi, rfl⟩
    exact hf i hi
  have hinj' : Set.InjOn f (Set.Iio n) := fun i hi j hj e => hinj i hi j hj e
  have hc : (f '' Set.Iio n).ncard = n := by
    rw [hinj'.ncard_image, Set.ncard_Iio_nat]
  calc n = (f '' Set.Iio n).ncard := hc.symm
    _ ≤ s.ncard := Set.ncard_le_ncard hsub hs

@[expose] def SG (W : SylW) (x : ℕ → NativeSporadic.Co1) : Subgroup NativeSporadic.Co1 :=
  Subgroup.closure ((fun k => x (getL 0 W.SI k)) '' {k | k < 5})

theorem strictB64 (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem mat_two (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) : 1 + (A + 1) = A := by
  rw [add_comm A 1, ← add_assoc, mat_add_self, zero_add]

section Syl

variable {W : SylW} (hW : SylOK W)
include hW

theorem lit_elems : ∃ (x : ℕ → NativeSporadic.Co1),
    (∀ i < W.R.length, PM (x i) (getL 0 W.R i)) ∧
    ∃ y : ℕ → NativeSporadic.Co1, ∀ i < W.RS.length,
      y i ∈ Subgroup.closure ((fun k => x (getL 0 W.SI k)) '' {k | k < 5}) ∧ PM (y i) (getL 0 W.RS i) := by
  have hR := InvFam.prog_elems W.P 2 hW.prog (fun j hj => by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · obtain ⟨g, hg⟩ := exists_co1_matA
      refine ⟨g, ?_⟩
      unfold PM
      rw [← hW.rA]
      exact hg
    · obtain ⟨g, hg⟩ := exists_co1_matB
      refine ⟨g, ?_⟩
      unfold PM
      rw [← hW.rB]
      exact hg)
  have hR' : ∀ i, ∃ z : NativeSporadic.Co1, i < W.R.length → PM z (getL 0 W.R i) := fun i => by
    by_cases h : i < W.R.length
    · obtain ⟨z, hz⟩ := hR i h
      exact ⟨z, fun _ => hz⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose x hx using hR'
  refine ⟨x, hx, ?_⟩
  set S := Subgroup.closure ((fun k => x (getL 0 W.SI k)) '' {k | k < 5})
  have hidx := InvFam.bnd_spec hW.idx
  have hSI : ∀ k < 5, getL 0 W.SI k < W.R.length := fun k hk => by
    have := hidx (getL 0 W.SI k) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (InvFam.getL_mem (by rw [hW.lenSI]; exact hk))))
    rwa [InvFam.lenL_eq] at this
  have hRS := prog_elems_in S W.PS 5 hW.progS (fun k hk => by
    refine ⟨x (getL 0 W.SI k), Subgroup.subset_closure ⟨k, hk, rfl⟩, ?_⟩
    rw [beq64 (allN64 hW.seed k hk)]
    exact hx _ (hSI k hk))
  have hRS' : ∀ i, ∃ z : NativeSporadic.Co1, i < W.RS.length → z ∈ S ∧ PM z (getL 0 W.RS i) :=
    fun i => by
      by_cases h : i < W.RS.length
      · obtain ⟨z, hz, hz'⟩ := hRS i h
        exact ⟨z, fun _ => ⟨hz, hz'⟩⟩
      · exact ⟨1, fun h' => absurd h' h⟩
  choose y hy using hRS'
  exact ⟨y, fun i hi => hy i hi⟩

theorem lit_idx : W.GI < W.R.length ∧ W.GJ < W.R.length ∧ ∀ k < 5, getL 0 W.SI k < W.R.length := by
  have hidx := InvFam.bnd_spec hW.idx
  have h : ∀ i ∈ W.GI :: W.GJ :: W.SI, i < W.R.length := fun i hi => by
    have := hidx i hi
    rwa [InvFam.lenL_eq] at this
  refine ⟨h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self),
    fun k hk => h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (InvFam.getL_mem (by rw [hW.lenSI]; exact hk))))⟩

theorem lit_tr {i : ℕ} (hi : i < W.R.length) : trK 24 (getL 0 W.R i) = getL 0 W.RT i :=
  beq64 (allN64 hW.tr i (by rw [InvFam.lenL_eq]; exact hi))

theorem lit_trS {i : ℕ} (hi : i < W.RS.length) : trK 24 (getL 0 W.RS i) = getL 0 W.RST i :=
  beq64 (allN64 hW.trS i (by rw [InvFam.lenL_eq]; exact hi))

section Elems

variable (x y : ℕ → NativeSporadic.Co1) (hx : ∀ i < W.R.length, PM (x i) (getL 0 W.R i))
include hx

theorem lit_fix : ∀ i ∈ W.GI :: W.SI, co1Act (x i) v₂ = v₂ := by
  intro i hi
  have hiR : i < W.R.length := by
    obtain ⟨h1, -, h3⟩ := lit_idx hW
    rcases List.mem_cons.1 hi with rfl | hi
    · exact h1
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
      have := h3 k (by rw [← hW.lenSI, InvFam.lenL_eq]; exact hk)
      rwa [InvFam.getL_eq, List.getElem?_eq_getElem hk, Option.getD_some] at this
  have hf := InvFam.fixAll_spec hW.fix i hi 2 (by simp)
  rw [← toVecD_v₂, pm_act (hx i hiR) (lit_tr hW hiR), hf]

theorem lit_SG_le : SG W x ≤ stabOf v₂ := by
  rw [SG, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact (mem_stabOf).2 (lit_fix hW x hx _ (List.mem_cons_of_mem _
    (InvFam.getL_mem (by rw [hW.lenSI]; exact hk))))

theorem lit_g_mem : x W.GI ∈ stabOf v₂ := (mem_stabOf).2 (lit_fix hW x hx _ List.mem_cons_self)

theorem lit_pmS {k : ℕ} (hk : k < 5) : PM (x (getL 0 W.SI k)) (getL 0 W.RS k) := by
  rw [beq64 (allN64 hW.seed k hk)]
  exact hx _ ((lit_idx hW).2.2 k hk)

theorem lit_two_pow : ∃ a, Nat.card (SG W x) = 2 ^ a := by
  have := finite_co1
  have hQ : rowsMatrix 24 (unpackR 24 W.QI) * rowsMatrix 24 (unpackR 24 W.Q) = 1 := by
    rw [rM_mul, hW.flag.2, rM_idF]
  have hQ' : rowsMatrix 24 (unpackR 24 W.Q) * rowsMatrix 24 (unpackR 24 W.QI) = 1 := by
    rw [rM_mul, hW.flag.1, rM_idF]
  refine card_closure_two_pow matHom matHom_injective _ _ hQ hQ' _ ?_
  rintro _ ⟨k, hk, rfl⟩
  have e := lit_pmS hW x hx hk
  unfold PM at e
  rw [e, rM_mul, rM_mul]
  exact uniTri_of_check (allN64 hW.uni k hk)

variable (hy : ∀ i < W.RS.length, y i ∈ SG W x ∧ PM (y i) (getL 0 W.RS i))
include hy

omit hx in
theorem lit_chain_card : ∀ n ≤ W.BASE.length, ((List.range n).map fun j => W.SZ.getD j 0).prod *
      Nat.card (chain64 (SG W x) W.BASE n) ≤ Nat.card (SG W x) := by
  have hfin := finite_co1
  have hcs := @CoTwo.card_step NativeSporadic.Co1 Vec24 _ co1Act hfin Odd.co1Act_mul' Odd.co1Act_one'
  have hbase := InvFam.bnd_spec hW.base
  set H := SG W x with hH
  intro n
  induction n with
  | zero => intro _; simp [chain64]
  | succ n ih =>
    intro hn
    have hn' : n < W.BASE.length := hn
    have ih' := ih hn'.le
    have hLV : W.LV.getD n [] ∈ W.LV := getD_mem64 [] (by rw [hW.lenLV]; exact hn')
    have hIr : ∀ i ∈ W.LV.getD n [], i < W.RS.length := fun i hi => by
      have := InvFam.bnd_spec hW.idxS i (List.mem_flatten.2 ⟨_, hLV, hi⟩)
      rwa [InvFam.lenL_eq] at this
    have hfix : ∀ i ∈ W.LV.getD n [], ∀ v ∈ W.BASE.take n,
        co1Act (y i) (toVecD 24 v) = toVecD 24 v := by
      intro i hi v hv
      rw [pm_act (hy i (hIr i hi)).2 (lit_trS hW (hIr i hi)),
        InvFam.fixAll_spec (hW.cfix n hn') i hi v hv]
    have hmem : ∀ l ∈ W.LV.getD n [], y l ∈ chain64 H W.BASE n := by
      intro l hl
      rw [mem_chain64]
      exact ⟨(hy l (hIr l hl)).1, fun j hj => hfix l hl _ (take_mem64 hj hn'.le)⟩
    obtain ⟨t, ht, hinj⟩ := InvFam.vec_family (chain64 H W.BASE n) (hW.tree n hn')
      (hbase _ (getD_mem64 0 hn')) (fun l => y (getL 0 (W.LV.getD n []) l))
      (fun l hl => hmem _ (InvFam.getL_mem hl))
      (fun l hl v => pm_act (hy _ (hIr _ (InvFam.getL_mem hl))).2
        (lit_trS hW (hIr _ (InvFam.getL_mem hl))) v)
    have horb : W.SZ.getD n 0 ≤
        (CoTwo.orbitSet co1Act (chain64 H W.BASE n) (toVecD 24 (W.BASE.getD n 0))).ncard :=
      le_ncard64 (fun i => co1Act (t i) (toVecD 24 (W.BASE.getD n 0)))
        (fun i hi => ⟨t i, (ht i hi).1, rfl⟩) hinj (Set.toFinite _)
    have hstep := hcs (H := chain64 H W.BASE n) (K := chain64 H W.BASE (n + 1)) inf_le_left
      (x := toVecD 24 (W.BASE.getD n 0)) (fun g hg => (Subgroup.mem_inf.1 hg).2) horb
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    calc ((List.range n).map fun j => W.SZ.getD j 0).prod * W.SZ.getD n 0 *
          Nat.card (chain64 H W.BASE (n + 1))
        = ((List.range n).map fun j => W.SZ.getD j 0).prod *
            (W.SZ.getD n 0 * Nat.card (chain64 H W.BASE (n + 1))) := by ring
      _ ≤ ((List.range n).map fun j => W.SZ.getD j 0).prod * Nat.card (chain64 H W.BASE n) :=
          Nat.mul_le_mul_left _ hstep
      _ ≤ _ := ih'

omit hx in
theorem lit_card_ge : 2 ^ 18 ≤ Nat.card (SG W x) := by
  have hfin := finite_co1
  have h := lit_chain_card hW x y hy W.BASE.length le_rfl
  have hpos : 1 ≤ Nat.card (chain64 (SG W x) W.BASE W.BASE.length) := Nat.card_pos
  calc 2 ^ 18 ≤ ((List.range W.BASE.length).map fun j => W.SZ.getD j 0).prod := hW.prod
    _ ≤ ((List.range W.BASE.length).map fun j => W.SZ.getD j 0).prod *
          Nat.card (chain64 (SG W x) W.BASE W.BASE.length) := Nat.le_mul_of_pos_right _ hpos
    _ ≤ _ := h

omit hy

theorem lit_sk {k : ℕ} (hk : k < 5) :
    matHom (x (getL 0 W.SI k)) = 1 + rowsMatrix 24 (unpackR 24 (selK W.E (getL 0 W.CN k))) := by
  have e := lit_pmS hW x hx hk
  unfold PM at e
  rw [e, ← beq64 (allN64 hW.cn k hk), rM_nxor, rM_idF, mat_two]

theorem lit_step {z : NativeSporadic.Co1}
    (hz : ∃ a, matHom z = 1 + rowsMatrix 24 (unpackR 24 (selK W.E a))) {k : ℕ} (hk : k < 5) :
    ∃ a, matHom (z * x (getL 0 W.SI k)) = 1 + rowsMatrix 24 (unpackR 24 (selK W.E a)) := by
  obtain ⟨a, ha⟩ := hz
  obtain ⟨hl, hs⟩ := selAll_spec (hW.cm k hk)
  have hm : rowsMatrix 24 (unpackR 24 (selK W.E a)) *
      rowsMatrix 24 (unpackR 24 (selK W.E (getL 0 W.CN k))) =
        rowsMatrix 24 (unpackR 24 (selK W.E (selK (W.CM.getD k []) a))) := by
    rw [← beq64 (allN64 hW.cn k hk)]
    refine rM_selK_mul W.E (W.CM.getD k []) (by rw [← hl, mulL_length]) (fun j hj => ?_) a
    have e := hs j (by rw [mulL_length]; exact hj)
    rw [mulL_getD _ _ _ hj] at e
    rw [rM_mul, e]
  refine ⟨a ^^^ getL 0 W.CN k ^^^ selK (W.CM.getD k []) a, ?_⟩
  rw [map_mul, ha, lit_sk hW x hx hk, selK_xor, selK_xor, rM_xor, rM_xor, add_mul, one_mul,
    mul_add, mul_one, hm]
  abel

theorem lit_mem_span {z : NativeSporadic.Co1} (hz : z ∈ SG W x) :
    ∃ a, matHom z = 1 + rowsMatrix 24 (unpackR 24 (selK W.E a)) := by
  have := finite_co1
  induction hz using Subgroup.closure_induction_right with
  | one => exact ⟨0, by rw [map_one, selK_zero, rM_zero, add_zero]⟩
  | mul_right z _ s hs ih =>
    obtain ⟨k, hk, rfl⟩ := hs
    exact lit_step hW x hx ih hk
  | mul_inv_cancel z _ s hs ih =>
    obtain ⟨k, hk, rfl⟩ := hs
    have hpow : ∀ j : ℕ, ∃ a, matHom (z * x (getL 0 W.SI k) ^ j) =
        1 + rowsMatrix 24 (unpackR 24 (selK W.E a)) := by
      intro j
      induction j with
      | zero => simpa using ih
      | succ j ihj =>
        rw [pow_succ, ← mul_assoc]
        exact lit_step hW x hx ihj hk
    have hpos := orderOf_pos (x (getL 0 W.SI k))
    have e : (x (getL 0 W.SI k))⁻¹ = x (getL 0 W.SI k) ^ (orderOf (x (getL 0 W.SI k)) - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [e]
    exact hpow _

theorem lit_mem_conj {z : NativeSporadic.Co1}
    (hz : z ∈ (SG W x).map (MulAut.conj (x W.GI)).toMonoidHom) :
    ∃ b, matHom z = 1 + rowsMatrix 24 (unpackR 24 (selK W.E2 b)) := by
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨a, ha⟩ := lit_mem_span hW x hx hw
  obtain ⟨hGI, hGJ, -⟩ := lit_idx hW
  have hg := hx _ hGI
  have hgi := pm_inv64 hg hW.ginv
  refine ⟨a, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  unfold PM at hg hgi
  rw [map_mul, map_mul, ha, hg, hgi, mul_add, add_mul, mul_one, rM_mul, hW.ginv, rM_idF,
    rM_selK_conj]
  rfl

theorem lit_inter :
    SG W x ⊓ (SG W x).map (MulAut.conj (x W.GI)).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨a, ha⟩ := lit_mem_span hW x hx hz1
  obtain ⟨b, hb⟩ := lit_mem_conj hW x hx hz2
  have hab : rowsMatrix 24 (unpackR 24 (selK W.E a)) =
      rowsMatrix 24 (unpackR 24 (selK W.E2 b)) := add_left_cancel (ha.symm.trans hb)
  obtain ⟨t, ht, htv⟩ := inter_sel hW.cl hW.clg hW.cp hW.pvl hW.pvp hW.dim (tv_eq_of_rM hab)
  have hzt : PM z (Nat.xor (idF 24) (selK W.L t)) := by
    unfold PM
    rw [ha, rM_eq_of_tv htv, rM_nxor, rM_idF]
  by_cases t0 : t = 0
  · subst t0
    apply matHom_injective
    unfold PM at hzt
    rw [hzt, selK_zero]
    change rowsMatrix 24 (unpackR 24 (idF 24 ^^^ 0)) = _
    rw [Nat.xor_zero, rM_idF, map_one]
  · exfalso
    have hlt : t - 1 < Nat.sub (pw2 (lenL W.L)) 1 := by
      rw [pw2_eq', InvFam.lenL_eq]
      change t - 1 < 2 ^ W.L.length - 1
      omega
    have hw := allN64 hW.wit (t - 1) hlt
    rw [strictB64] at hw
    obtain ⟨h1, hw⟩ := andB_iff.1 hw
    obtain ⟨h2, h3⟩ := andB_iff.1 hw
    have hu : getL 0 W.U (t - 1) < 2 ^ 24 := by
      have : getL 0 W.U (t - 1) < pw2 24 := by simpa using h1
      rwa [pw2_eq'] at this
    have ht' : Nat.succ (t - 1) = t := by omega
    rw [ht'] at h3
    have hmem := (Pairs.inPts_iff _ hu).1 h2
    rw [← Pairs.orbit_Co1_eq] at hmem
    have h4 := Pairs.orbit_smul_mem z hmem
    change co1Act z (toVecD 24 (getL 0 W.U (t - 1))) ∈ _ at h4
    rw [pm_act hzt rfl, Pairs.orbit_Co1_eq] at h4
    have h5 := (Pairs.inPts_iff _ (CFSG.KC.F2W.vmF_lt 24 _ _)).2 h4
    have h6 := InvFam.notB_true h3
    change Pairs.inPts _ _ 98280 _ = false at h6
    rw [h5] at h6
    exact absurd h6 (by decide)

end Elems

theorem lit_sylow :
    ∃ (S : Subgroup NativeSporadic.Co1) (g : NativeSporadic.Co1), S ≤ stabOf v₂ ∧
      g ∈ stabOf v₂ ∧ (∃ a, Nat.card S = 2 ^ a) ∧ 2 ^ 18 ≤ Nat.card S ∧
      S ⊓ S.map (MulAut.conj g).toMonoidHom = ⊥ := by
  obtain ⟨x, hx, y, hy⟩ := lit_elems hW
  exact ⟨SG W x, x W.GI, lit_SG_le hW x hx, lit_g_mem hW x hx, lit_two_pow hW x hx,
    lit_card_ge hW x y hy, lit_inter hW x hx⟩

end Syl

theorem map_conj_le_stabOf64 {v : Vec24} {S : Subgroup NativeSporadic.Co1} (hS : S ≤ stabOf v)
    (c : NativeSporadic.Co1) : S.map (MulAut.conj c).toMonoidHom ≤ stabOf (co1Act c v) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : co1Act y v = v := hS hy
  rw [mem_stabOf]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [co1Act_mul, co1Act_mul, co1Act_inv_apply, hy']

theorem eq_bot_lit
    (hex : ∃ W : SylW, SylOK W) {v : Vec24} {c : NativeSporadic.Co1}
    (hc : co1Act c v₂ = v) {m : ℕ} (hm : Odd m) (hcard : Nat.card ↥(stabOf v) = 2 ^ 18 * m)
    {H N : Subgroup NativeSporadic.Co1} (hHC : H ≤ stabOf v)
    (hidx : Nat.card ↥(stabOf v) ≤ 2 * Nat.card ↥H) (hNH : N ≤ H)
    (hNnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hNp : IsPGroup 2 N) : N = ⊥ := by
  have := finite_co1
  obtain ⟨W, hW⟩ := hex
  obtain ⟨S, g, hSv, hgv, ⟨a, ha⟩, hge, hint⟩ := lit_sylow hW
  subst hc
  have hT : S.map (MulAut.conj g).toMonoidHom ≤ stabOf v₂ := by
    rintro _ ⟨y, hy, rfl⟩
    exact TwoB.conj_mem_of_mem hgv (hSv hy)
  have hS' := map_conj_le_stabOf64 hSv c
  have hT' := map_conj_le_stabOf64 hT c
  have hS18 : Nat.card S = 2 ^ 18 := by
    refine eq_two_pow_of_dvd ha hge hm ?_
    rw [← hcard, ← TwoB.card_map_conj S c]
    exact Subgroup.card_dvd_of_le hS'
  have h := TwoB.card_le_of_normal_two_subgroup (k := 18) hHC hidx hS' hT' hm hcard
    (by rw [TwoB.card_map_conj, hS18]) (by rw [TwoB.card_map_conj, TwoB.card_map_conj, hS18])
    hNH hNnorm hNp
  rw [← TwoB.map_conj_inf, TwoB.card_map_conj, hint] at h
  exact (Subgroup.card_le_one_iff_eq_bot N).1 (h.trans (by rw [Subgroup.card_bot]))

end CFSG.Sporadic.Co1.Module.Co2Stab

end
