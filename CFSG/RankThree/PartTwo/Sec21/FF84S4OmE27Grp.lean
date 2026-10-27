module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmE27Elts
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmOrder

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega MulAction

@[expose] def bas (k : Fin 6) : F6 := fun j => if j = k then 1 else 0

theorem eq_of_basis {g h : GL6} (H : ∀ k : Fin 6, g (bas k) = h (bas k)) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v = ∑ k, v k • bas k := by
    funext j
    simp [bas, Finset.sum_apply]
  rw [hv, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, H k]

@[expose] def enc (v : F6) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val + 16 * (v 4).val + 32 * (v 5).val

theorem enc_add : ∀ x y : F6, enc (x + y) = enc x ^^^ enc y := by decide +kernel

theorem enc_smul : ∀ (c : ZMod 2) (x : F6), enc (c • x) = if c = 1 then enc x else 0 := by
  decide +kernel

theorem enc_inj : ∀ x y : F6, enc x = enc y → x = y := by decide +kernel

theorem enc_bits : ∀ v : F6, (enc v).testBit 0 = decide (v 0 = 1) ∧
    (enc v).testBit 1 = decide (v 1 = 1) ∧ (enc v).testBit 2 = decide (v 2 = 1) ∧
    (enc v).testBit 3 = decide (v 3 = 1) ∧ (enc v).testBit 4 = decide (v 4 = 1) ∧
    (enc v).testBit 5 = decide (v 5 = 1) := by
  decide +kernel

abbrev Tab := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

@[expose] def app (t : Tab) (n : ℕ) : ℕ :=
  (if n.testBit 0 then t.1 else 0) ^^^ (if n.testBit 1 then t.2.1 else 0) ^^^
    (if n.testBit 2 then t.2.2.1 else 0) ^^^ (if n.testBit 3 then t.2.2.2.1 else 0) ^^^
    (if n.testBit 4 then t.2.2.2.2.1 else 0) ^^^ (if n.testBit 5 then t.2.2.2.2.2 else 0)

@[expose] def tmul (t u : Tab) : Tab :=
  (app t u.1, app t u.2.1, app t u.2.2.1, app t u.2.2.2.1, app t u.2.2.2.2.1, app t u.2.2.2.2.2)

@[expose] def tid : Tab := (1, 2, 4, 8, 16, 32)

@[expose] def tpow (t : Tab) (n : ℕ) : Tab := (tmul t)^[n] tid

@[expose] def tab (g : GL6) : Tab :=
  (enc (g (bas 0)), enc (g (bas 1)), enc (g (bas 2)), enc (g (bas 3)), enc (g (bas 4)),
    enc (g (bas 5)))

theorem enc_apply (g : GL6) (v : F6) : enc (g v) = app (tab g) (enc v) := by
  have hv : v = ∑ k, v k • bas k := by
    funext j
    simp [bas, Finset.sum_apply]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := enc_bits v
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, Fin.sum_univ_six, map_add, enc_add, enc_smul]
  simp only [app, tab, h0, h1, h2, h3, h4, h5, decide_eq_true_eq]

theorem tab_mul (g h : GL6) : tab (g * h) = tmul (tab g) (tab h) := by
  have e : ∀ k, enc ((g * h) (bas k)) = app (tab g) (enc (h (bas k))) :=
    fun k => enc_apply g (h (bas k))
  exact Prod.ext (e 0) (Prod.ext (e 1) (Prod.ext (e 2) (Prod.ext (e 3)
    (Prod.ext (e 4) (e 5)))))

theorem tab_one : tab 1 = tid := by decide +kernel

theorem tab_pow (g : GL6) (n : ℕ) : tab (g ^ n) = tpow (tab g) n := by
  induction n with
  | zero => rw [pow_zero, tab_one]; rfl
  | succ n ih => rw [pow_succ', tab_mul, ih, tpow, tpow, Function.iterate_succ_apply']

theorem tab_inj {g h : GL6} (H : tab g = tab h) : g = h := by
  simp only [tab, Prod.mk.injEq] at H
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := H
  refine eq_of_basis fun k => enc_inj _ _ ?_
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem tab_a1 : tab a1 = (10, 9, 8, 15, 16, 32) := by decide +kernel
theorem tab_a2 : tab a2 = (2, 15, 10, 6, 16, 32) := by decide +kernel
theorem tab_a3 : tab a3 = (1, 2, 4, 8, 32, 48) := by decide +kernel
theorem tab_s1 : tab s1 = (10, 9, 15, 8, 16, 32) := by decide +kernel
theorem tab_s2 : tab s2 = (2, 1, 4, 8, 16, 32) := by decide +kernel
theorem tab_s3 : tab s3 = (1, 2, 4, 8, 32, 16) := by decide +kernel
theorem tab_sg : tab sg = (28, 23, 43, 59, 13, 14) := by decide +kernel
theorem tab_tu : tab tu = (28, 44, 55, 59, 13, 14) := by decide +kernel

@[expose] def famSub {ι : Type} (f : ι → GL6) (e : ι) (he : f e = 1) (mul : ι → ι → ι)
    (hm : ∀ i j, f i * f j = f (mul i j)) (inv : ι → ι) (hi : ∀ i, f i * f (inv i) = 1) :
    Subgroup GL6 where
  carrier := Set.range f
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨mul i j, (hm i j).symm⟩
  one_mem' := ⟨e, he⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨inv i, (inv_eq_of_mul_eq_one_right (hi i)).symm⟩

theorem card_famSub_le {ι : Type} [Finite ι] {f : ι → GL6} {e he mul hm inv hi} :
    Nat.card (famSub f e he mul hm inv hi) ≤ Nat.card ι := by
  refine Nat.card_le_card_of_surjective (fun i => ⟨f i, ⟨i, rfl⟩⟩) ?_
  rintro ⟨_, i, rfl⟩
  exact ⟨i, rfl⟩

theorem card_famSub_ge {ι : Type} [Finite ι] {f : ι → GL6} {e he mul hm inv hi}
    (hf : Function.Injective f) : Nat.card ι ≤ Nat.card (famSub f e he mul hm inv hi) := by
  refine Nat.card_le_card_of_injective (fun i => ⟨f i, ⟨i, rfl⟩⟩) ?_
  intro i j h
  exact hf (congrArg Subtype.val h)

@[expose] def TP (i : Fin 3 × Fin 3 × Fin 3 × Fin 3) : Tab :=
  tmul (tmul (tmul (tpow (10, 9, 8, 15, 16, 32) i.1.val) (tpow (2, 15, 10, 6, 16, 32) i.2.1.val))
    (tpow (1, 2, 4, 8, 32, 48) i.2.2.1.val)) (tpow (28, 23, 43, 59, 13, 14) i.2.2.2.val)

@[expose] def gP (i : Fin 3 × Fin 3 × Fin 3 × Fin 3) : GL6 :=
  a1 ^ i.1.val * a2 ^ i.2.1.val * a3 ^ i.2.2.1.val * sg ^ i.2.2.2.val

theorem gP_tab (i : Fin 3 × Fin 3 × Fin 3 × Fin 3) : tab (gP i) = TP i := by
  simp only [gP, TP, tab_mul, tab_pow, tab_a1, tab_a2, tab_a3, tab_sg]

@[expose] def rotK (k : Fin 3) (e : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  if k = 0 then e else if k = 1 then (e.2.1, e.2.2, e.1) else (e.2.2, e.1, e.2.1)

@[expose] def nfP (i j : Fin 3 × Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 × Fin 3 :=
  let e := rotK i.2.2.2 (j.1, j.2.1, j.2.2.1)
  (i.1 + e.1, i.2.1 + e.2.1, i.2.2.1 + e.2.2, i.2.2.2 + j.2.2.2)

@[expose] def invP (i : Fin 3 × Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 × Fin 3 :=
  let e := rotK (-i.2.2.2) (-i.1, -i.2.1, -i.2.2.1)
  (e.1, e.2.1, e.2.2, -i.2.2.2)

theorem TP_mul : ∀ i j, tmul (TP i) (TP j) = TP (nfP i j) := by decide +kernel

theorem TP_inv : ∀ i, tmul (TP i) (TP (invP i)) = tid := by decide +kernel

theorem TP_inj : Function.Injective TP := by decide +kernel

theorem TP_one : TP (0, 0, 0, 0) = tid := by decide +kernel

theorem gP_mul (i j : Fin 3 × Fin 3 × Fin 3 × Fin 3) : gP i * gP j = gP (nfP i j) :=
  tab_inj (by rw [tab_mul, gP_tab, gP_tab, gP_tab]; exact TP_mul i j)

theorem gP_inv (i : Fin 3 × Fin 3 × Fin 3 × Fin 3) : gP i * gP (invP i) = 1 :=
  tab_inj (by rw [tab_mul, gP_tab, gP_tab, tab_one]; exact TP_inv i)

theorem gP_one : gP (0, 0, 0, 0) = 1 :=
  tab_inj (by rw [gP_tab, tab_one]; exact TP_one)

theorem gP_inj : Function.Injective gP := fun i j h => TP_inj (by rw [← gP_tab, ← gP_tab, h])

theorem gP_mem (i : Fin 3 × Fin 3 × Fin 3 × Fin 3) : gP i ∈ O6 :=
  mul_mem (mul_mem (mul_mem (pow_mem a1_mem _) (pow_mem a2_mem _)) (pow_mem a3_mem _))
    (pow_mem sg_mem _)

@[expose] noncomputable def P81 : Subgroup GL6 :=
  famSub gP (0, 0, 0, 0) gP_one nfP gP_mul invP gP_inv

theorem card_P81 : Nat.card P81 = 81 := by
  refine le_antisymm ?_ ?_
  · refine card_famSub_le.trans ?_
    simp [Nat.card_eq_fintype_card]
  · refine le_trans ?_ (card_famSub_ge gP_inj)
    simp [Nat.card_eq_fintype_card]

theorem P81_le_O6 : P81 ≤ O6 := by
  rintro _ ⟨i, rfl⟩
  exact gP_mem i

@[expose] def EE (e : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 × Fin 3 :=
  (e.1, e.2.1, e.2.2, 0)

theorem nfP_EE : ∀ e e' : Fin 3 × Fin 3 × Fin 3, nfP (EE e) (EE e') = EE (e + e') := by
  decide +kernel

theorem EE_inj : Function.Injective EE := by
  intro e e' h
  simpa [EE, Prod.ext_iff] using h

@[expose] noncomputable def E0 : Subgroup GL6 :=
  famSub (fun e => gP (EE e)) 0 (by simpa [EE] using gP_one) (· + ·)
    (fun e e' => by rw [gP_mul, nfP_EE])
    (fun e => -e) (fun e => by rw [gP_mul, nfP_EE, add_neg_cancel]; exact gP_one)

theorem card_E0 : Nat.card E0 = 27 := by
  refine le_antisymm ?_ ?_
  · refine card_famSub_le.trans ?_
    simp [Nat.card_eq_fintype_card]
  · refine le_trans ?_ (card_famSub_ge (fun e e' h => EE_inj (gP_inj h)))
    simp [Nat.card_eq_fintype_card]

theorem mem_E0_of_snd {i : Fin 3 × Fin 3 × Fin 3 × Fin 3} (h : i.2.2.2 = 0) : gP i ∈ E0 := by
  refine ⟨(i.1, i.2.1, i.2.2.1), ?_⟩
  have : EE (i.1, i.2.1, i.2.2.1) = i := Prod.ext rfl (Prod.ext rfl (Prod.ext rfl h.symm))
  show gP (EE (i.1, i.2.1, i.2.2.1)) = gP i
  rw [this]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
