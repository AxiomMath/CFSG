module

public import CFSG.Monster.B.TwoA.Sp8.P0UCoord

set_option linter.unusedSectionVars false

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def xorSpan : List ℕ → List ℕ
  | [] => [0]
  | a :: l => xorSpan l ++ (xorSpan l).map (a ^^^ ·)

@[expose] def flagGens : Fin 4 → List ℕ := ![[1], [1, 2], [1, 2, 12], [1, 2, 12, 48]]

@[expose] def flagGrp (i : Fin 4) : Subgroup Dfull :=
  Subgroup.closure {g | ∃ v ∈ flagGens i, g = tD v}

@[expose] def flagS : Subgroup Dfull :=
  Xgrp ⊓ ⨅ i, Subgroup.normalizer (flagGrp i : Set Dfull)

private theorem tD_zero_eq_one : tD 0 = (1 : Dfull) := by
  have h : tD 0 * tD 0 = tD 0 * 1 := by
    rw [mul_one]
    exact (tD_xor 0 0).symm
  exact mul_left_cancel h

private theorem tD_mul_self (τ : ℕ) : tD τ * tD τ = 1 := by
  rw [← tD_xor, Nat.xor_self, tD_zero_eq_one]

private theorem tD_one_eq_xhat : tD (1 : ℕ) = xhat := by
  simpa [tT] using tD_two_pow (0 : Fin 9)

private theorem tD_one_ne_one : tD (1 : ℕ) ≠ 1 := by
  rw [tD_one_eq_xhat]
  exact xhat_ne_one

private theorem tD_inj_of_lt {τ σ : ℕ} (hτ : τ < 2 ^ 9) (hσ : σ < 2 ^ 9)
    (h : tD τ = tD σ) : τ = σ := by
  have hb : bvec 9 τ = bvec 9 σ := by
    have := congrArg tVec h
    rwa [tVec_tD, tVec_tD] at this
  exact CFSG.KC.BvecLoop.bvec_inj hτ hσ hb

private theorem aEquiv_bvec_eq_tD {v : ℕ} (hv : v < 2 ^ 8) :
    (aEquiv (Multiplicative.ofAdd (bvec 8 v)) : Dfull) = tD v := by
  rw [coe_aEquiv, toAdd_ofAdd, tD_eq, ← Psi9_extV (bvec 8 v)]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [extV, Fin.snoc_last]
    change (0 : ZMod 2) = (if v.testBit 8 then 1 else 0)
    rw [Nat.testBit_eq_false_of_lt hv]
    rfl
  · rw [extV, Fin.snoc_castSucc]
    rfl

private theorem zero_mem_xorSpan : ∀ l : List ℕ, 0 ∈ xorSpan l
  | [] => by simp [xorSpan]
  | _ :: l => by
    rw [xorSpan]
    exact List.mem_append_left _ (zero_mem_xorSpan l)

private theorem mem_xorSpan_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ∈ xorSpan l := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil)
  | cons b l ih =>
    rw [xorSpan]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_append_right _ (List.mem_map.2 ⟨0, zero_mem_xorSpan l, by simp⟩)
    · exact List.mem_append_left _ (ih h)

private theorem xorSpan_closed {l : List ℕ} {a b : ℕ}
    (ha : a ∈ xorSpan l) (hb : b ∈ xorSpan l) : a ^^^ b ∈ xorSpan l := by
  induction l generalizing a b with
  | nil =>
    rw [xorSpan] at ha hb ⊢
    simp only [List.mem_singleton] at ha hb
    rw [ha, hb]
    simp
  | cons c l ih =>
    rw [xorSpan, List.mem_append, List.mem_map] at ha hb ⊢
    rcases ha with ha | ⟨a', ha', rfl⟩
    · rcases hb with hb | ⟨b', hb', rfl⟩
      · exact Or.inl (ih ha hb)
      · refine Or.inr ⟨a ^^^ b', ih ha hb', ?_⟩
        exact (Nat.xor_left_comm a c b').symm
    · rcases hb with hb | ⟨b', hb', rfl⟩
      · refine Or.inr ⟨a' ^^^ b, ih ha' hb, ?_⟩
        exact (Nat.xor_assoc c a' b).symm
      · refine Or.inl ?_
        rw [show (c ^^^ a') ^^^ (c ^^^ b') = a' ^^^ b' by
          rw [Nat.xor_assoc, Nat.xor_left_comm a' c, ← Nat.xor_assoc, Nat.xor_self,
            Nat.zero_xor]]
        exact ih ha' hb'

private theorem xorSpan_lt_two_pow {n : ℕ} (l : List ℕ)
    (h : ∀ a ∈ l, a < 2 ^ n) : ∀ τ ∈ xorSpan l, τ < 2 ^ n := by
  induction l with
  | nil =>
    intro τ hτ
    rw [xorSpan] at hτ
    simp only [List.mem_singleton] at hτ
    rw [hτ]
    exact Nat.two_pow_pos n
  | cons a l ih =>
    intro τ hτ
    rw [xorSpan, List.mem_append, List.mem_map] at hτ
    rcases hτ with hτ | ⟨b, hb, rfl⟩
    · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) τ hτ
    · exact Nat.xor_lt_two_pow (h a (List.mem_cons_self ..))
        (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) b hb)

theorem tD_mem_closure_of_mem_xorSpan {l : List ℕ} {τ : ℕ} (h : τ ∈ xorSpan l) :
    tD τ ∈ Subgroup.closure {g | ∃ v ∈ l, g = tD v} := by
  induction l generalizing τ with
  | nil =>
    rw [xorSpan] at h
    simp only [List.mem_singleton] at h
    rw [h, tD_zero_eq_one]
    exact Subgroup.one_mem _
  | cons a l ih =>
    rw [xorSpan, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨τ', hτ', rfl⟩
    · refine Subgroup.closure_mono ?_ (ih h)
      rintro x ⟨v, hv, rfl⟩
      exact ⟨v, List.mem_cons_of_mem _ hv, rfl⟩
    · have ha_mem : tD a ∈ Subgroup.closure {g | ∃ v ∈ a :: l, g = tD v} :=
        Subgroup.subset_closure ⟨a, List.mem_cons_self .., rfl⟩
      have hτ'_mem : tD τ' ∈ Subgroup.closure {g | ∃ v ∈ a :: l, g = tD v} := by
        refine Subgroup.closure_mono ?_ (ih hτ')
        rintro x ⟨v, hv, rfl⟩
        exact ⟨v, List.mem_cons_of_mem _ hv, rfl⟩
      rw [tD_xor]
      exact Subgroup.mul_mem _ ha_mem hτ'_mem

private theorem xorSpan_flagGens_lt (i : Fin 4) {τ : ℕ}
    (h : τ ∈ xorSpan (flagGens i)) : τ < 2 ^ 6 := by
  refine xorSpan_lt_two_pow (flagGens i) ?_ τ h
  fin_cases i <;> simp [flagGens]

private theorem mem_flagGrp_iff {i : Fin 4} {h : Dfull} :
    h ∈ flagGrp i ↔ ∃ τ ∈ xorSpan (flagGens i), h = tD τ := by
  constructor
  · intro hh
    rw [flagGrp] at hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨v, mem_xorSpan_of_mem hv, rfl⟩
    | one => exact ⟨0, zero_mem_xorSpan _, tD_zero_eq_one.symm⟩
    | mul y z _ _ ihy ihz =>
      obtain ⟨a, ha, rfl⟩ := ihy
      obtain ⟨b, hb, rfl⟩ := ihz
      exact ⟨a ^^^ b, xorSpan_closed ha hb, (tD_xor a b).symm⟩
    | inv y _ ihy =>
      obtain ⟨a, ha, rfl⟩ := ihy
      exact ⟨a, ha, inv_eq_of_mul_eq_one_right (tD_mul_self a)⟩
  · rintro ⟨τ, hτ, rfl⟩
    rw [flagGrp]
    exact tD_mem_closure_of_mem_xorSpan hτ

private theorem tD_mem_flagGrp_iff_of_lt {i : Fin 4} {τ : ℕ} (hτ : τ < 2 ^ 9) :
    tD τ ∈ flagGrp i ↔ τ ∈ xorSpan (flagGens i) := by
  constructor
  · intro h
    obtain ⟨σ, hσ, hστ⟩ := mem_flagGrp_iff.1 h
    have hσlt : σ < 2 ^ 9 := by
      have := xorSpan_flagGens_lt i hσ
      omega
    have hτσ : τ = σ := tD_inj_of_lt hτ hσlt hστ
    rwa [hτσ]
  · intro h
    exact mem_flagGrp_iff.2 ⟨τ, h, rfl⟩

private theorem conj_mem_flagGrp_of_mem_flagS {g : Dfull} (hg : g ∈ flagS) (i : Fin 4)
    {x : Dfull} (hx : x ∈ flagGrp i) : MulAut.conj g x ∈ flagGrp i := by
  have hn : g ∈ Subgroup.normalizer (flagGrp i : Set Dfull) :=
    Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2 i
  have h := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
  simpa [MulAut.conj_apply] using h

private theorem eq_one_or_eq_tD_one_of_mem_flagGrp_zero {h : Dfull}
    (hh : h ∈ flagGrp 0) : h = 1 ∨ h = tD 1 := by
  obtain ⟨τ, hτ, rfl⟩ := mem_flagGrp_iff.1 hh
  have hτ01 : τ = 0 ∨ τ = 1 := by
    simpa [flagGens, xorSpan] using hτ
  rcases hτ01 with rfl | rfl
  · exact Or.inl tD_zero_eq_one
  · exact Or.inr rfl

private theorem conj_tD_one_ne_one (g : Dfull) : MulAut.conj g (tD 1) ≠ 1 := by
  intro h
  have h' : g * tD 1 * g⁻¹ = 1 := by simpa [MulAut.conj_apply] using h
  apply tD_one_ne_one
  calc tD 1 = g⁻¹ * (g * tD 1 * g⁻¹) * g := by group
    _ = 1 := by rw [h']; group

private theorem xorSpan_pair_mem (i : Fin 3) (a b : Fin 64)
    (ha : (a : ℕ) ∈ xorSpan (flagGens i.succ))
    (hb : (b : ℕ) ∈ xorSpan (flagGens i.succ))
    (hiff : ((a : ℕ) ∈ xorSpan (flagGens i.castSucc) ↔
      (b : ℕ) ∈ xorSpan (flagGens i.castSucc))) :
    ((b : ℕ) ^^^ (a : ℕ)) ∈ xorSpan (flagGens i.castSucc) := by
  fin_cases i <;> decide +kernel +revert

private theorem flagGrp_mono {i j : Fin 4} (hij : i ≤ j) : flagGrp i ≤ flagGrp j := by
  rw [flagGrp, flagGrp, Subgroup.closure_le]
  rintro x ⟨v, hv, rfl⟩
  have hvj : v ∈ flagGens j := by
    fin_cases i <;> fin_cases j <;> simp_all [flagGens] <;> tauto
  exact Subgroup.subset_closure ⟨v, hvj, rfl⟩

private theorem mul_self_eq_one_of_mem_flagGrp_three {h : Dfull}
    (hh : h ∈ flagGrp 3) : h * h = 1 := by
  obtain ⟨τ, -, rfl⟩ := mem_flagGrp_iff.1 hh
  exact tD_mul_self τ

private def nBy (g h : Dfull) : Dfull := MulAut.conj g h * h

private theorem nBy_mem_prev {g : Dfull} (hg : g ∈ flagS) (i : Fin 3) {h : Dfull}
    (hh : h ∈ flagGrp i.succ) : nBy g h ∈ flagGrp i.castSucc := by
  obtain ⟨τ, hτ, rfl⟩ := mem_flagGrp_iff.1 hh
  have hτlt : τ < 2 ^ 6 := xorSpan_flagGens_lt i.succ hτ
  have hch : MulAut.conj g (tD τ) ∈ flagGrp i.succ :=
    conj_mem_flagGrp_of_mem_flagS hg i.succ (mem_flagGrp_iff.2 ⟨τ, hτ, rfl⟩)
  obtain ⟨τ', hτ', hτ'eq⟩ := mem_flagGrp_iff.1 hch
  have hτ'lt : τ' < 2 ^ 6 := xorSpan_flagGens_lt i.succ hτ'
  have hτ'eq' : g * tD τ * g⁻¹ = tD τ' := by
    simpa [MulAut.conj_apply] using hτ'eq
  have hiff : τ ∈ xorSpan (flagGens i.castSucc) ↔
      τ' ∈ xorSpan (flagGens i.castSucc) := by
    have hn : g ∈ Subgroup.normalizer (flagGrp i.castSucc : Set Dfull) :=
      Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2 i.castSucc
    have h1 : tD τ ∈ flagGrp i.castSucc ↔ tD τ' ∈ flagGrp i.castSucc := by
      have h2 := (Subgroup.mem_normalizer_iff.1 hn (tD τ))
      rwa [hτ'eq'] at h2
    exact (tD_mem_flagGrp_iff_of_lt (i := i.castSucc) (by omega)).symm.trans
      (h1.trans (tD_mem_flagGrp_iff_of_lt (i := i.castSucc) (by omega)))
  have hxor : τ' ^^^ τ ∈ xorSpan (flagGens i.castSucc) := by
    have hcheck := xorSpan_pair_mem i ⟨τ, by omega⟩ ⟨τ', by omega⟩
      (by simpa using hτ) (by simpa using hτ') (by simpa using hiff)
    simpa using hcheck
  refine mem_flagGrp_iff.2 ⟨τ' ^^^ τ, hxor, ?_⟩
  rw [nBy, hτ'eq, ← tD_xor]

private theorem nBy_eq_one_of_mem_zero {g : Dfull} (hg : g ∈ flagS) {h : Dfull}
    (hh : h ∈ flagGrp 0) : nBy g h = 1 := by
  rcases eq_one_or_eq_tD_one_of_mem_flagGrp_zero hh with rfl | rfl
  · simp [nBy]
  · have hmem : MulAut.conj g (tD (1 : ℕ)) ∈ flagGrp 0 :=
      conj_mem_flagGrp_of_mem_flagS hg 0
        (mem_flagGrp_iff.2 ⟨1, mem_xorSpan_of_mem (by simp [flagGens]), rfl⟩)
    rcases eq_one_or_eq_tD_one_of_mem_flagGrp_zero hmem with h1 | h1
    · exact absurd h1 (conj_tD_one_ne_one g)
    · rw [nBy, h1, tD_mul_self]

private theorem conj_sq_eq {g h : Dfull} (hh : h ∈ flagGrp 3)
    (hn : nBy g h ∈ flagGrp 3) :
    MulAut.conj g (MulAut.conj g h) = nBy g (nBy g h) * h := by
  have hh_sq : h * h = 1 := mul_self_eq_one_of_mem_flagGrp_three hh
  have hn_sq : nBy g h * nBy g h = 1 := mul_self_eq_one_of_mem_flagGrp_three hn
  have hch : MulAut.conj g h = nBy g h * h := by
    rw [nBy, mul_assoc, hh_sq, mul_one]
  have hcn : MulAut.conj g (nBy g h) = nBy g (nBy g h) * nBy g h := by
    rw [show nBy g (nBy g h) = MulAut.conj g (nBy g h) * nBy g h from rfl,
      mul_assoc, hn_sq, mul_one]
  calc MulAut.conj g (MulAut.conj g h)
      = MulAut.conj g (nBy g h * h) := by rw [hch]
    _ = MulAut.conj g (nBy g h) * MulAut.conj g h := by rw [map_mul]
    _ = (nBy g (nBy g h) * nBy g h) * (nBy g h * h) := by rw [hcn, hch]
    _ = (nBy g (nBy g h) * (nBy g h * nBy g h)) * h := by group
    _ = nBy g (nBy g h) * h := by rw [hn_sq, mul_one]

private theorem conj_four_eq {g : Dfull} (hg : g ∈ flagS) {h : Dfull}
    (hh : h ∈ flagGrp 3) :
    MulAut.conj g (MulAut.conj g (MulAut.conj g (MulAut.conj g h))) = h := by
  have hn1_2 : nBy g h ∈ flagGrp 2 := nBy_mem_prev hg 2 hh
  have hn1_3 : nBy g h ∈ flagGrp 3 := flagGrp_mono (by decide) hn1_2
  have hn2_1 : nBy g (nBy g h) ∈ flagGrp 1 := nBy_mem_prev hg 1 hn1_2
  have hn2_3 : nBy g (nBy g h) ∈ flagGrp 3 := flagGrp_mono (by decide) hn2_1
  have hn3_0 : nBy g (nBy g (nBy g h)) ∈ flagGrp 0 := nBy_mem_prev hg 0 hn2_1
  have hn3_3 : nBy g (nBy g (nBy g h)) ∈ flagGrp 3 := flagGrp_mono (by decide) hn3_0
  have hn4 : nBy g (nBy g (nBy g (nBy g h))) = 1 := nBy_eq_one_of_mem_zero hg hn3_0
  have h2 : MulAut.conj g (MulAut.conj g h) = nBy g (nBy g h) * h :=
    conj_sq_eq hh hn1_3
  have h4 : MulAut.conj g (MulAut.conj g (nBy g (nBy g h))) =
      nBy g (nBy g (nBy g (nBy g h))) * nBy g (nBy g h) :=
    conj_sq_eq hn2_3 hn3_3
  calc MulAut.conj g (MulAut.conj g (MulAut.conj g (MulAut.conj g h)))
      = MulAut.conj g (MulAut.conj g (nBy g (nBy g h) * h)) := by rw [h2]
    _ = MulAut.conj g (MulAut.conj g (nBy g (nBy g h))) *
        MulAut.conj g (MulAut.conj g h) := by rw [map_mul, map_mul]
    _ = (nBy g (nBy g (nBy g (nBy g h))) * nBy g (nBy g h)) *
        (nBy g (nBy g h) * h) := by rw [h4, h2]
    _ = (nBy g (nBy g (nBy g (nBy g h))) *
          (nBy g (nBy g h) * nBy g (nBy g h))) * h := by group
    _ = nBy g (nBy g (nBy g (nBy g h))) * h := by
        rw [mul_self_eq_one_of_mem_flagGrp_three hn2_3, mul_one]
    _ = h := by rw [hn4, one_mul]

private theorem pow_four_conj_eq {g : Dfull} (hg : g ∈ flagS) {h : Dfull}
    (hh : h ∈ flagGrp 3) : g ^ 4 * h * (g ^ 4)⁻¹ = h := by
  have hc4 := conj_four_eq hg hh
  have h1 : ((MulAut.conj g) ^ 4) h = h := by
    change MulAut.conj g (MulAut.conj g (MulAut.conj g (MulAut.conj g h))) = h
    exact hc4
  have h2 : MulAut.conj (g ^ 4) h = h := by
    rw [map_pow]
    exact h1
  simpa only [MulAut.conj_apply] using h2

private theorem aEquiv_bvec_flag_mem {v : ℕ} (hv : v ∈ [1, 2, 12, 48]) :
    (aEquiv (Multiplicative.ofAdd (bvec 8 v)) : Dfull) ∈ flagGrp 3 := by
  have hvlt : v < 2 ^ 8 := by
    have h := hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> norm_num
  rw [aEquiv_bvec_eq_tD hvlt]
  have hv3 : v ∈ flagGens 3 := by simpa [flagGens] using hv
  exact mem_flagGrp_iff.2 ⟨v, mem_xorSpan_of_mem hv3, rfl⟩

private theorem aEquiv_lam0_le_flagGrp_three :
    ((fun v : V8 => (aEquiv (Multiplicative.ofAdd v) : Dfull)) '' (lam0 : Set V8)) ⊆
      (flagGrp 3 : Set Dfull) := by
  rintro x ⟨v, hv, rfl⟩
  rw [lam0] at hv
  refine Submodule.span_induction (p := fun v _ =>
    (aEquiv (Multiplicative.ofAdd v) : Dfull) ∈ flagGrp 3) ?_ ?_ ?_ ?_ hv
  · intro y hy
    have hy4 : y = bvec 8 1 ∨ y = bvec 8 2 ∨ y = bvec 8 12 ∨ y = bvec 8 48 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_false] using hy
    rcases hy4 with rfl | rfl | rfl | rfl
    · exact aEquiv_bvec_flag_mem (by simp)
    · exact aEquiv_bvec_flag_mem (by simp)
    · exact aEquiv_bvec_flag_mem (by simp)
    · exact aEquiv_bvec_flag_mem (by simp)
  · rw [ofAdd_zero, map_one]
    exact (flagGrp 3).one_mem
  · intro x y _ _ ihx ihy
    rw [ofAdd_add, map_mul]
    exact (flagGrp 3).mul_mem ihx ihy
  · intro a x _ ih
    rcases zmod2_cases a with rfl | rfl
    · rw [zero_smul, ofAdd_zero, map_one]
      exact (flagGrp 3).one_mem
    · rw [one_smul]
      exact ih

private theorem pow_four_mem_P0 {g : Dfull} (hg : g ∈ flagS) : g ^ 4 ∈ P0 := by
  have hX : g ^ 4 ∈ Xgrp := Xgrp.pow_mem (Subgroup.mem_inf.1 hg).1 4
  rw [P0, PLam]
  refine ⟨hX, Subgroup.mem_centralizer_iff.2 ?_⟩
  rintro x ⟨v, hv, rfl⟩
  have hx : (aEquiv (Multiplicative.ofAdd v) : Dfull) ∈ flagGrp 3 :=
    aEquiv_lam0_le_flagGrp_three ⟨v, hv, rfl⟩
  exact (mul_inv_eq_iff_eq_mul.1 (pow_four_conj_eq hg hx)).symm

theorem flagS_le_Xgrp : flagS ≤ Xgrp := inf_le_left

theorem mem_flagS_of {g : Dfull} (hg : g ∈ Xgrp)
    (h : ∀ i, ∀ v ∈ flagGens i, ∃ w ∈ xorSpan (flagGens i), g * tD v * g⁻¹ = tD w) :
    g ∈ flagS := by
  rw [flagS, Subgroup.mem_inf]
  refine ⟨hg, Subgroup.mem_iInf.2 fun i => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hmap_le : (flagGrp i).map (MulAut.conj g).toMonoidHom ≤ flagGrp i := by
    rw [flagGrp, MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hz
    obtain ⟨w, hw, hw_eq⟩ := h i v hv
    have hval : (MulAut.conj g).toMonoidHom (tD v) = tD w := by
      simpa [MulAut.conj_apply] using hw_eq
    rw [hval]
    exact tD_mem_closure_of_mem_xorSpan hw
  have hmap_eq : (flagGrp i).map (MulAut.conj g).toMonoidHom = flagGrp i := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  constructor
  · intro hx
    have hx' : (MulAut.conj g).toMonoidHom x ∈
        (flagGrp i).map (MulAut.conj g).toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rwa [hmap_eq] at hx'
  · intro hx
    have hx' : (MulAut.conj g).toMonoidHom x ∈
        (flagGrp i).map (MulAut.conj g).toMonoidHom := by
      rw [hmap_eq]
      simpa [MulAut.conj_apply] using hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
    have hy_eq : y = x := (MulAut.conj g).injective hyx
    rwa [hy_eq] at hy

theorem flagS_le_Jhat : flagS ≤ Jhat := by
  intro g hg
  rw [← centralizer_xhat]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [← tD_one_eq_xhat]
  have hmem : MulAut.conj g (tD (1 : ℕ)) ∈ flagGrp 0 := by
    refine conj_mem_flagGrp_of_mem_flagS hg 0 ?_
    exact mem_flagGrp_iff.2 ⟨1, mem_xorSpan_of_mem (by simp [flagGens]), rfl⟩
  have hconj : MulAut.conj g (tD 1) = tD 1 := by
    rcases eq_one_or_eq_tD_one_of_mem_flagGrp_zero hmem with h1 | h1
    · exact absurd h1 (conj_tD_one_ne_one g)
    · exact h1
  have hc : g * tD 1 * g⁻¹ = tD 1 := by
    simpa [MulAut.conj_apply] using hconj
  exact (mul_inv_eq_iff_eq_mul.1 hc).symm

theorem P0_le_flagS : P0 ≤ flagS := by
  intro g hg
  have hgX : g ∈ Xgrp := (Subgroup.mem_inf.1 hg).1
  have hgC : g ∈ Subgroup.centralizer
      ((fun v : V8 => (aEquiv (Multiplicative.ofAdd v) : Dfull)) '' (lam0 : Set V8)) :=
    (Subgroup.mem_inf.1 hg).2
  refine mem_flagS_of hgX ?_
  intro i v hv
  have hv4 : v = 1 ∨ v = 2 ∨ v = 12 ∨ v = 48 := by
    fin_cases i <;> simp [flagGens] at hv ⊢ <;> tauto
  have hvlt : v < 2 ^ 8 := by
    rcases hv4 with rfl | rfl | rfl | rfl <;> norm_num
  have hb : bvec 8 v ∈ (lam0 : Set V8) := by
    rw [lam0]
    rcases hv4 with rfl | rfl | rfl | rfl <;> exact Submodule.subset_span (by simp)
  refine ⟨v, mem_xorSpan_of_mem hv, ?_⟩
  have hcomm : g * (aEquiv (Multiplicative.ofAdd (bvec 8 v)) : Dfull) * g⁻¹ =
      (aEquiv (Multiplicative.ofAdd (bvec 8 v)) : Dfull) := by
    have h := (Subgroup.mem_centralizer_iff.1 hgC _ ⟨bvec 8 v, hb, rfl⟩).symm
    calc g * (aEquiv (Multiplicative.ofAdd (bvec 8 v)) : Dfull) * g⁻¹
        = (aEquiv (Multiplicative.ofAdd (bvec 8 v)) : Dfull) * g * g⁻¹ := by rw [h]
      _ = (aEquiv (Multiplicative.ofAdd (bvec 8 v)) : Dfull) := by group
  rw [← aEquiv_bvec_eq_tD hvlt]
  exact hcomm

theorem isPGroup_flagS : IsPGroup 2 flagS := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨37, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  have hg : (g : Dfull) ∈ flagS := g.2
  have h4 : (g : Dfull) ^ 4 ∈ P0 := pow_four_mem_P0 hg
  have hcard : ((⟨(g : Dfull) ^ 4, h4⟩ : P0) ^ Nat.card P0) = 1 := pow_card_eq_one'
  have h := congrArg Subtype.val hcard
  simp only [Subgroup.coe_pow, Subgroup.coe_one, natCard_P0] at h
  rw [show (g : Dfull) ^ 2 ^ 37 = ((g : Dfull) ^ 4) ^ 2 ^ 35 by
    rw [← pow_mul]
    norm_num]
  exact h

end CFSG.Monster.B.TwoA.Sp8.WordRel
