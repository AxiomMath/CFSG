module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmE27Grp

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega MulAction

@[expose] def TT (i : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Tab :=
  tmul (tmul (tmul (tpow (10, 9, 15, 8, 16, 32) i.1.val) (tpow (2, 1, 4, 8, 16, 32) i.2.1.val))
    (tpow (1, 2, 4, 8, 32, 16) i.2.2.1.val)) (tpow (28, 44, 55, 59, 13, 14) i.2.2.2.val)

@[expose] def gT (i : Fin 2 × Fin 2 × Fin 2 × Fin 2) : GL6 :=
  s1 ^ i.1.val * s2 ^ i.2.1.val * s3 ^ i.2.2.1.val * tu ^ i.2.2.2.val

theorem gT_tab (i : Fin 2 × Fin 2 × Fin 2 × Fin 2) : tab (gT i) = TT i := by
  simp only [gT, TT, tab_mul, tab_pow, tab_s1, tab_s2, tab_s3, tab_tu]

@[expose] def shiftT (k : Fin 2) (e : Fin 2 × Fin 2 × Fin 2) : Fin 2 × Fin 2 × Fin 2 :=
  if k = 0 then e else (e.1, e.2.2, e.2.1)

@[expose] def nfT (i j : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Fin 2 × Fin 2 × Fin 2 × Fin 2 :=
  let e := shiftT i.2.2.2 (j.1, j.2.1, j.2.2.1)
  (i.1 + e.1, i.2.1 + e.2.1, i.2.2.1 + e.2.2, i.2.2.2 + j.2.2.2)

@[expose] def invT (i : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Fin 2 × Fin 2 × Fin 2 × Fin 2 :=
  let e := shiftT i.2.2.2 (i.1, i.2.1, i.2.2.1)
  (e.1, e.2.1, e.2.2, i.2.2.2)

theorem TT_mul : ∀ i j, tmul (TT i) (TT j) = TT (nfT i j) := by decide +kernel

theorem TT_inv : ∀ i, tmul (TT i) (TT (invT i)) = tid := by decide +kernel

theorem TT_inj : Function.Injective TT := by decide +kernel

theorem TT_one : TT (0, 0, 0, 0) = tid := by decide +kernel

theorem gT_mul (i j : Fin 2 × Fin 2 × Fin 2 × Fin 2) : gT i * gT j = gT (nfT i j) :=
  tab_inj (by rw [tab_mul, gT_tab, gT_tab, gT_tab]; exact TT_mul i j)

theorem gT_inv (i : Fin 2 × Fin 2 × Fin 2 × Fin 2) : gT i * gT (invT i) = 1 :=
  tab_inj (by rw [tab_mul, gT_tab, gT_tab, tab_one]; exact TT_inv i)

theorem gT_one : gT (0, 0, 0, 0) = 1 :=
  tab_inj (by rw [gT_tab, tab_one]; exact TT_one)

theorem gT_inj : Function.Injective gT := fun i j h => TT_inj (by rw [← gT_tab, ← gT_tab, h])

theorem gT_mem (i : Fin 2 × Fin 2 × Fin 2 × Fin 2) : gT i ∈ O6 :=
  mul_mem (mul_mem (mul_mem (pow_mem s1_mem _) (pow_mem s2_mem _)) (pow_mem s3_mem _))
    (pow_mem tu_mem _)

@[expose] noncomputable def T16 : Subgroup GL6 :=
  famSub gT (0, 0, 0, 0) gT_one nfT gT_mul invT gT_inv

theorem card_T16 : Nat.card T16 = 16 := by
  refine le_antisymm ?_ ?_
  · refine card_famSub_le.trans ?_
    simp [Nat.card_eq_fintype_card]
  · refine le_trans ?_ (card_famSub_ge gT_inj)
    simp [Nat.card_eq_fintype_card]

theorem T16_le_O6 : T16 ≤ O6 := by
  rintro _ ⟨i, rfl⟩
  exact gT_mem i

theorem P_norm : ∀ (i : Fin 3 × Fin 3 × Fin 3 × Fin 3) (e : Fin 3 × Fin 3 × Fin 3),
    tmul (TP i) (TP (EE e)) = tmul (TP (EE (rotK i.2.2.2 e))) (TP i) := by
  decide +kernel

theorem T_norm : ∀ (i : Fin 2 × Fin 2 × Fin 2 × Fin 2) (e : Fin 3 × Fin 3 × Fin 3),
    ∃ e' : Fin 3 × Fin 3 × Fin 3, tmul (TT i) (TP (EE e)) = tmul (TP (EE e')) (TT i) := by
  decide +kernel

theorem P81_conj_mem {p y : GL6} (hp : p ∈ P81) (hy : y ∈ E0) : p * y * p⁻¹ ∈ E0 := by
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨e, rfl⟩ := hy
  have h : gP i * gP (EE e) = gP (EE (rotK i.2.2.2 e)) * gP i :=
    tab_inj (by rw [tab_mul, tab_mul, gP_tab, gP_tab, gP_tab]; exact P_norm i e)
  rw [h, mul_inv_cancel_right]
  exact ⟨_, rfl⟩

theorem T16_conj_mem {p y : GL6} (hp : p ∈ T16) (hy : y ∈ E0) : p * y * p⁻¹ ∈ E0 := by
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨e, rfl⟩ := hy
  obtain ⟨e', he'⟩ := T_norm i e
  have h : gT i * gP (EE e) = gP (EE e') * gT i :=
    tab_inj (by rw [tab_mul, tab_mul, gT_tab, gP_tab, gP_tab]; exact he')
  rw [h, mul_inv_cancel_right]
  exact ⟨_, rfl⟩

theorem cent_bound : ∀ i : Fin 3 × Fin 3 × Fin 3 × Fin 3, i.2.2.2 ≠ 0 →
    (Finset.univ.filter fun j : Fin 3 × Fin 3 × Fin 3 × Fin 3 =>
      tmul (TP i) (TP j) = tmul (TP j) (TP i)).card ≤ 9 := by
  decide +kernel

theorem eq_E0_of_comm_card {E1 : Subgroup GL6} (hle : E1 ≤ P81) (hc : IsMulCommutative E1)
    (hcard : Nat.card E1 = 27) : E1 = E0 := by
  have hsub : E1 ≤ E0 := by
    intro y hy
    by_contra hyE
    obtain ⟨i, rfl⟩ := hle hy
    have hk : i.2.2.2 ≠ 0 := fun h => hyE (mem_E0_of_snd h)
    classical
    let f : E1 → {j : Fin 3 × Fin 3 × Fin 3 × Fin 3 //
        tmul (TP i) (TP j) = tmul (TP j) (TP i)} := fun z =>
      ⟨Classical.choose (hle z.2), by
        have hz := Classical.choose_spec (hle z.2)
        have hcomm := congrArg Subtype.val (mul_comm' (⟨gP i, hy⟩ : E1) z)
        simp only [Subgroup.coe_mul] at hcomm
        have := congrArg tab hcomm
        rw [tab_mul, tab_mul, gP_tab, ← hz, gP_tab] at this
        exact this⟩
    have hinj : Function.Injective f := by
      intro z z' h
      have h1 := Classical.choose_spec (hle z.2)
      have h2 := Classical.choose_spec (hle z'.2)
      have hh : Classical.choose (hle z.2) = Classical.choose (hle z'.2) :=
        congrArg Subtype.val h
      exact Subtype.ext (by rw [← h1, ← h2, hh])
    have h9 := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_eq_fintype_card (α := {j : Fin 3 × Fin 3 × Fin 3 × Fin 3 //
      tmul (TP i) (TP j) = tmul (TP j) (TP i)}), Fintype.card_subtype] at h9
    have := cent_bound i hk
    omega
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, card_E0])

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
