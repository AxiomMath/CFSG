module

public import CFSG.LocalAnalysis.StandardType.GGDepEDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAPattern
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGDepEPatternPack

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def lr7ep_tA (n : ℕ) (i j : Fin n) : ℕ :=
  if i = j then 1 else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def lr7ep_tB6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4) then 4
  else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def lr7ep_tD6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 3 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 3)
  then 3 else 2

private def lr7ep_tE6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)
  then 3 else 2

private theorem lr7ep_a6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.A 6 p.1 p.2 = lr7ep_tA 6 p.1 p.2 := by
  decide

private theorem lr7ep_b6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.B 6 p.1 p.2 = lr7ep_tB6 p.1 p.2 := by
  decide

private theorem lr7ep_d6_apply :
    ∀ p : Fin 6 × Fin 6, ggCoxeterMatrixD 6 p.1 p.2 = lr7ep_tD6 p.1 p.2 := by
  decide

private theorem lr7ep_e6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.E₆ p.1 p.2 = lr7ep_tE6 p.1 p.2 := by
  decide

private def lr7ep_emb0 (i : Fin 5) : Fin 6 := ⟨i.val + 1, by omega⟩
private def lr7ep_emb5 (i : Fin 5) : Fin 6 := ⟨i.val, by omega⟩
private def lr7ep_emb1 (i : Fin 5) : Fin 6 := if i.val = 0 then 0 else ⟨i.val + 1, by omega⟩

private def lr7ep_embInv0 (j : Fin 6) : Fin 5 := ⟨j.val - 1, by omega⟩
private def lr7ep_embInv5 (j : Fin 6) : Fin 5 := if h : j.val < 5 then ⟨j.val, h⟩ else 0
private def lr7ep_embInv1 (j : Fin 6) : Fin 5 :=
  if j.val = 0 then 0 else ⟨j.val - 1, by omega⟩

private def lr7ep_g (a0 a1 a2 a3 a4 : Fin 6) : Fin 5 → Fin 6 := ![a0, a1, a2, a3, a4]

private lemma lr7ep_g_apply (f : Fin 5 → Fin 6) (i : Fin 5) :
    lr7ep_g (f 0) (f 1) (f 2) (f 3) (f 4) i = f i := by
  fin_cases i <;> rfl

private def lr7ep_P0 (i j : Fin 5) : ℕ := lr7ep_tE6 (lr7ep_emb0 i) (lr7ep_emb0 j)
private def lr7ep_P5 (i j : Fin 5) : ℕ := lr7ep_tE6 (lr7ep_emb5 i) (lr7ep_emb5 j)
private def lr7ep_P1 (i j : Fin 5) : ℕ := lr7ep_tE6 (lr7ep_emb1 i) (lr7ep_emb1 j)

private def lr7ep_cond0 (k : Fin 5) : Prop := k.val = 0 ∨ k.val = 1 ∨ k.val = 4
private def lr7ep_cond1 (k : Fin 5) : Prop := k.val = 2

private def lr7ep_concl (tab : Fin 6 → Fin 6 → ℕ) (cond : Fin 5 → Prop)
    (a0 a1 a2 a3 a4 : Fin 6) (t : Fin 6) : Prop :=
  ∃ k : Fin 5, cond k ∧ ∀ i : Fin 5,
    tab t (lr7ep_g a0 a1 a2 a3 a4 i) = if i = k then 3 else 2

private theorem lr7ep_cls_A6_b0 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tA 6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P0 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl (lr7ep_tA 6) lr7ep_cond0 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1666748482369984442204035377715537904804401)
    (Pc := 94743748803957159412910662433) (cm := 65553)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond0; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private theorem lr7ep_cls_B6_b0 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tB6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P0 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl lr7ep_tB6 lr7ep_cond0 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1753860851378494425407901333706011834458673)
    (Pc := 94743748803957159412910662433) (cm := 65553)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond0; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private theorem lr7ep_cls_D6_b0 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tD6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P0 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl lr7ep_tD6 lr7ep_cond0 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1585080631232214426175740556965071863030321)
    (Pc := 94743748803957159412910662433) (cm := 65553)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond0; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private theorem lr7ep_cls_E6_b0 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tE6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P0 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl lr7ep_tE6 lr7ep_cond0 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1666748482369984442279593237219391985296161)
    (Pc := 94743748803957159412910662433) (cm := 65553)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond0; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private theorem lr7ep_cls_A6_b5 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tA 6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P5 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl (lr7ep_tA 6) lr7ep_cond0 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1666748482369984442204035377715537904804401)
    (Pc := 94743748822403885898460701473) (cm := 65553)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond0; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private theorem lr7ep_cls_B6_b5 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tB6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P5 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl lr7ep_tB6 lr7ep_cond0 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1753860851378494425407901333706011834458673)
    (Pc := 94743748822403885898460701473) (cm := 65553)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond0; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private theorem lr7ep_cls_D6_b5 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tD6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P5 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl lr7ep_tD6 lr7ep_cond0 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1585080631232214426175740556965071863030321)
    (Pc := 94743748822403885898460701473) (cm := 65553)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond0; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private theorem lr7ep_cls_E6_b5 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tE6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P5 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl lr7ep_tE6 lr7ep_cond0 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1666748482369984442279593237219391985296161)
    (Pc := 94743748822403885898460701473) (cm := 65553)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond0; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private theorem lr7ep_cls_E6_b1 :
    ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, lr7ep_tE6 (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j)
        = lr7ep_P1 i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl lr7ep_tE6 lr7ep_cond1 a0 a1 a2 a3 a4 t := by
  intro a0 a1 a2 a3 a4 h t ht
  exact DepEPack.clsB_sound (T := 1666748482369984442279593237219391985296161)
    (Pc := 94743748803957158313400082993) (cm := 256)
    (by decide +kernel) (by decide +kernel) (by unfold lr7ep_cond1; decide +kernel)
    (by decide +kernel) (lr7ep_g a0 a1 a2 a3 a4) h t ht

private lemma lr7ep_cartanE6_off (i j : Fin 6) (hij : i ≠ j) :
    CartanMatrix.E 6 i j = 0 ∨ CartanMatrix.E 6 i j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma lr7ep_cartanE6_symm (i j : Fin 6) : CartanMatrix.E 6 i j = CartanMatrix.E 6 j i := by
  fin_cases i <;> fin_cases j <;> decide

private lemma lr7ep_coxeterE6_off (i j : Fin 6) (hij : i ≠ j) :
    CoxeterMatrix.E₆ i j = if CartanMatrix.E 6 i j = 0 then 2 else 3 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private lemma lr7ep_mul_eq_three {a b : ℤ} (ha : a < 0) (hb : b < 0) (h : a * b = 3) :
    a = -1 ∨ a = -3 := by
  have hb1 : b ≤ -1 := by omega
  have hge : -3 ≤ a := by nlinarith [h, ha, hb1]
  have hle : a ≤ -1 := by omega
  interval_cases a <;> omega

private lemma lr7ep_mod3_zero_three {c c' e : ℤ} (hc : (c : ZMod 3) = (e : ZMod 3))
    (hc' : (c' : ZMod 3) = (e : ZMod 3)) (h : c * c' = 3) (hcn : c < 0) (hcn' : c' < 0)
    (he : e = 0 ∨ e = -1) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((3 : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc'] at hcc
  rcases he with rfl | rfl
  · rcases lr7ep_mul_eq_three hcn hcn' h with hc1 | hc3
    · rw [hc1] at hc
      norm_num at hc
    · have hc'1 : c' = -1 := by nlinarith [h, hc3]
      rw [hc'1] at hc'
      norm_num at hc'
  · exact absurd hcc (by decide)

private lemma lr7ep_mod3_zero_two {c c' e : ℤ} (hc : (c : ZMod 3) = (e : ZMod 3))
    (hc' : (c' : ZMod 3) = (e : ZMod 3)) (h : c * c' = 2) (he : e = 0) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc', he] at hcc
  exact absurd hcc (by decide)

private lemma lr7ep_mod3_neg_two_three {c c' : ℤ} {k : ℤ} (hc : (c : ZMod 3) = ((-1 : ℤ) : ZMod 3))
    (hc' : (c' : ZMod 3) = ((-1 : ℤ) : ZMod 3)) (h : c * c' = k) (hk : k = 2 ∨ k = 3) : False := by
  have hcc : ((c * c' : ℤ) : ZMod 3) = ((k : ℤ) : ZMod 3) := by rw [h]
  rw [Int.cast_mul, hc, hc'] at hcc
  rcases hk with rfl | rfl <;> exact absurd hcc (by decide)

private lemma lr7ep_MJ_E6 {emb : Fin 5 → Fin 6} (hemb : Function.Injective emb)
    {M : CoxeterMatrix (Option (Fin 5))}
    {C : Matrix (Option (Fin 5)) (Option (Fin 5)) ℤ} (hC : GGIntCartan M C)
    (hJ : ∀ i j : Fin 5, (C (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (emb i) (emb j) : ZMod 3)) :
    ∀ i j : Fin 5, M (some i) (some j) = CoxeterMatrix.E₆ (emb i) (emb j) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal (some i), (CoxeterMatrix.E₆).diagonal (emb i)]
  · have hne : (some i : Option (Fin 5)) ≠ some j := by simp [hij]
    have hkl : emb i ≠ emb j := fun h => hij (hemb h)
    have hJij := hJ i j
    have hJji : (C (some j) (some i) : ZMod 3) =
        ((CartanMatrix.E 6) (emb i) (emb j) : ZMod 3) := by
      rw [hJ j i, lr7ep_cartanE6_symm (emb j) (emb i)]
    have hcase := hC.2 (some i) (some j) hne
    rw [lr7ep_coxeterE6_off (emb i) (emb j) hkl]
    rcases lr7ep_cartanE6_off (emb i) (emb j) hkl with he | he
    · rw [if_pos he]
      rcases hcase with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · exact hm
      · exfalso
        rw [h1, he] at hJij
        norm_num at hJij
      · exfalso
        exact lr7ep_mod3_zero_two hJij hJji h1 he
      · exfalso
        exact lr7ep_mod3_zero_three hJij hJji h1 h2 h3 (Or.inl he)
    · rw [if_neg (by omega)]
      rcases hcase with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
      · exfalso
        rw [h1, he] at hJij
        norm_num at hJij
      · exact hm
      · exfalso
        exact lr7ep_mod3_neg_two_three (by rw [hJij, he]) (by rw [hJji, he]) h1 (Or.inl rfl)
      · exfalso
        exact lr7ep_mod3_neg_two_three (by rw [hJij, he]) (by rw [hJji, he]) h1 (Or.inr rfl)

private lemma lr7ep_row {tab : Fin 6 → Fin 6 → ℕ} {T : CoxeterMatrix (Fin 6)}
    (hT : ∀ p : Fin 6 × Fin 6, T p.1 p.2 = tab p.1 p.2)
    {emb : Fin 5 → Fin 6} {P : Fin 5 → Fin 5 → ℕ} {cond : Fin 5 → Prop}
    (he6 : ∀ i j : Fin 5, CoxeterMatrix.E₆ (emb i) (emb j) = P i j)
    (hfin : ∀ a0 a1 a2 a3 a4 : Fin 6,
      (∀ i j : Fin 5, tab (lr7ep_g a0 a1 a2 a3 a4 i) (lr7ep_g a0 a1 a2 a3 a4 j) = P i j) →
      ∀ t : Fin 6, (∀ i : Fin 5, t ≠ lr7ep_g a0 a1 a2 a3 a4 i) →
        lr7ep_concl tab cond a0 a1 a2 a3 a4 t)
    {M : CoxeterMatrix (Option (Fin 5))} {eT : Fin 6 ≃ Option (Fin 5)}
    (hMe : M = T.reindex eT)
    (hMA : ∀ i j : Fin 5, M (some i) (some j) = CoxeterMatrix.E₆ (emb i) (emb j)) :
    ∃ k : Fin 5, cond k ∧ ∀ i : Fin 5, M none (some i) = if i = k then 3 else 2 := by
  let f : Fin 5 → Fin 6 := fun i => eT.symm (some i)
  let t : Fin 6 := eT.symm none
  have ht : ∀ i : Fin 5, t ≠ f i := by
    intro i h
    have h' : (none : Option (Fin 5)) = some i := eT.symm.injective (by simpa [t, f] using h)
    simp at h'
  let g : Fin 5 → Fin 6 := lr7ep_g (f 0) (f 1) (f 2) (f 3) (f 4)
  have hg : ∀ i : Fin 5, g i = f i := lr7ep_g_apply f
  have hP : ∀ i j : Fin 5, tab (g i) (g j) = P i j := by
    intro i j
    rw [hg i, hg j]
    calc tab (f i) (f j) = T (f i) (f j) := (hT (f i, f j)).symm
      _ = M (some i) (some j) :=
          (show T (f i) (f j) = M (some i) (some j) by
            rw [hMe, CoxeterMatrix.reindex_apply])
      _ = CoxeterMatrix.E₆ (emb i) (emb j) := hMA i j
      _ = P i j := he6 i j
  have ht' : ∀ i : Fin 5, t ≠ g i := fun i h => ht i (h.trans (hg i))
  obtain ⟨k, hk, hrow⟩ := hfin (f 0) (f 1) (f 2) (f 3) (f 4) hP t ht'
  refine ⟨k, hk, fun i => ?_⟩
  have h1 : M none (some i) = tab t (f i) := by
    rw [hMe, CoxeterMatrix.reindex_apply, hT (t, f i)]
  have h2 : tab t (f i) = tab t (g i) := by rw [hg i]
  exact h1.trans (h2.trans (hrow i))

private lemma lr7ep_cartan_of_two {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h2 : M u v = 2) :
    C u v = 0 ∧ C v u = 0 := by
  rcases hC.2 u v huv with ⟨-, h1, h2'⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · exact ⟨h1, h2'⟩
  · rw [h2] at hm; omega
  · rw [h2] at hm; omega
  · rw [h2] at hm; omega

private lemma lr7ep_cartan_of_three {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (h3 : M u v = 3) :
    C u v = -1 ∧ C v u = -1 := by
  rcases hC.2 u v huv with ⟨hm, -, -⟩ | ⟨-, h1, h2'⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
  · rw [h3] at hm; omega
  · exact ⟨h1, h2'⟩
  · rw [h3] at hm; omega
  · rw [h3] at hm; omega

private lemma lr7ep_assemble {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} (e : Fin 6 ≃ Λ)
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (posEquiv : Fin 5 ≃ {i : Λ // i ≠ b}) {emb : Fin 5 → Fin 6}
    (hpos : ∀ i : Fin 5, e.symm ((posEquiv i : {i : Λ // i ≠ b}) : Λ) = emb i)
    (hemb : Function.Injective emb)
    {k : Fin 5} (hpat : GGDepEPat (e.symm b) (emb k) (-1) (-1))
    (hrow : ∀ i : Fin 5, CK none (some (posEquiv i)) = (if i = k then (-1 : ℤ) else 0))
    (hrow' : ∀ i : Fin 5, CK (some (posEquiv i)) none = (if i = k then (-1 : ℤ) else 0)) :
    ∃ (c0 : Fin 6) (m n : ℤ), GGDepEPat (e.symm b) c0 m n ∧
      ∀ i : {i : Λ // i ≠ b}, CK none (some i) = (if e.symm i = c0 then m else 0) ∧
        CK (some i) none = (if e.symm i = c0 then n else 0) := by
  refine ⟨emb k, -1, -1, hpat, fun i => ?_⟩
  set j : Fin 5 := posEquiv.symm i with hj
  have hji : posEquiv j = i := Equiv.apply_symm_apply posEquiv i
  have hes : e.symm (i : Λ) = emb j := by
    rw [← hji, hpos j]
  have hiff : (e.symm (i : Λ) = emb k) ↔ (j = k) := by
    rw [hes]
    exact ⟨fun h => hemb h, fun h => by rw [h]⟩
  have h1 : CK none (some i) = (if j = k then (-1 : ℤ) else 0) := by
    rw [← hji]; exact hrow j
  have h2 : CK (some i) none = (if j = k then (-1 : ℤ) else 0) := by
    rw [← hji]; exact hrow' j
  refine ⟨?_, ?_⟩
  · rw [h1]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos (hiff.mpr hjk)]
    · rw [if_neg hjk, if_neg (fun h => hjk (hiff.mp h))]
  · rw [h2]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos (hiff.mpr hjk)]
    · rw [if_neg hjk, if_neg (fun h => hjk (hiff.mp h))]

private lemma lr7ep_typeE6_reindex {ι ι' : Type} {M : CoxeterMatrix ι} (h : GGIsTypeE6 M)
    (e : ι ≃ ι') : GGIsTypeE6 (M.reindex e) := by
  obtain ⟨e₀, rfl⟩ := h
  refine ⟨e₀.trans e, ?_⟩
  ext a b
  simp [CoxeterMatrix.reindex_apply]

private lemma lr7ep_setup {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} (e : Fin 6 ≃ Λ)
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (hWK : GGIsWeylMatrix MK)
    (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (e.symm i) (e.symm j) : ZMod 3))
    (posEquiv : Fin 5 ≃ {i : Λ // i ≠ b}) {emb : Fin 5 → Fin 6}
    (hpos : ∀ k : Fin 5, e.symm ((posEquiv k : {i : Λ // i ≠ b}) : Λ) = emb k)
    (hemb : Function.Injective emb) :
    ∃ (M : CoxeterMatrix (Option (Fin 5))) (C : Matrix (Option (Fin 5)) (Option (Fin 5)) ℤ),
      M = MK.reindex (Equiv.optionCongr posEquiv).symm ∧
      GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        (∀ i j : Fin 5, (C (some i) (some j) : ZMod 3) =
          ((CartanMatrix.E 6) (emb i) (emb j) : ZMod 3)) ∧
        (∀ i j : Fin 5, M (some i) (some j) = CoxeterMatrix.E₆ (emb i) (emb j)) ∧
        (∀ i : Fin 5, C none (some i) = CK none (some (posEquiv i))) ∧
        (∀ i : Fin 5, C (some i) none = CK (some (posEquiv i)) none) := by
  let σ : Option (Fin 5) ≃ Option {i : Λ // i ≠ b} := Equiv.optionCongr posEquiv
  let M : CoxeterMatrix (Option (Fin 5)) := MK.reindex σ.symm
  let C : Matrix (Option (Fin 5)) (Option (Fin 5)) ℤ := Matrix.reindex σ.symm σ.symm CK
  have hW : GGIsWeylMatrix M := l05nDP4_weyl_reindex hWK σ.symm
  have hC : GGIntCartan M C := by
    refine ⟨fun u => ?_, fun u v huv => ?_⟩
    · simp only [C, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact hCK.1 (σ u)
    · have h := hCK.2 (σ u) (σ v) (fun hh => huv (σ.injective hh))
      simpa [M, C, CoxeterMatrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
        using h
  have hJ' : ∀ i j : Fin 5, (C (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (emb i) (emb j) : ZMod 3) := by
    intro i j
    have h := hJ (posEquiv i) (posEquiv j)
    have h1 : C (some i) (some j) = CK (some (posEquiv i)) (some (posEquiv j)) := by
      show CK (σ (some i)) (σ (some j)) = CK (some (posEquiv i)) (some (posEquiv j))
      simp [σ, Equiv.optionCongr_apply]
    rw [h1, h, hpos i, hpos j]
  have hMA : ∀ i j : Fin 5, M (some i) (some j) = CoxeterMatrix.E₆ (emb i) (emb j) :=
    lr7ep_MJ_E6 hemb hC hJ'
  have hcn : ∀ i : Fin 5, C none (some i) = CK none (some (posEquiv i)) := by
    intro i
    show CK (σ none) (σ (some i)) = CK none (some (posEquiv i))
    simp [σ, Equiv.optionCongr_apply]
  have hnc : ∀ i : Fin 5, C (some i) none = CK (some (posEquiv i)) none := by
    intro i
    show CK (σ (some i)) (σ none) = CK (some (posEquiv i)) none
    simp [σ, Equiv.optionCongr_apply]
  exact ⟨M, C, rfl, hW, hC, hJ', hMA, hcn, hnc⟩

private lemma lr7ep_weyl_row_b0 {M : CoxeterMatrix (Option (Fin 5))}
    (hW : GGIsWeylMatrix M)
    (hMA : ∀ i j : Fin 5, M (some i) (some j) =
      CoxeterMatrix.E₆ (lr7ep_emb0 i) (lr7ep_emb0 j)) :
    ∃ k : Fin 5, lr7ep_cond0 k ∧ ∀ i : Fin 5, M none (some i) = if i = k then 3 else 2 := by
  rw [GGIsWeylMatrix] at hW
  rcases hW with ⟨n, eT, hn, hcase⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ |
    ⟨eT, hMe⟩
  · have hn6 : n = 6 := by
      have hcard := Fintype.card_congr eT
      simp [Fintype.card_fin, Fintype.card_option] at hcard
      omega
    subst hn6
    rcases hcase with hA | ⟨-, hB⟩ | ⟨-, hD⟩
    · exact lr7ep_row (T := CoxeterMatrix.A 6) (tab := lr7ep_tA 6)
        (by intro p; exact lr7ep_a6_apply p) (P := lr7ep_P0) (cond := lr7ep_cond0)
        (by intro i j; exact lr7ep_e6_apply (lr7ep_emb0 i, lr7ep_emb0 j))
        lr7ep_cls_A6_b0 hA hMA
    · exact lr7ep_row (T := CoxeterMatrix.B 6) (tab := lr7ep_tB6)
        (by intro p; exact lr7ep_b6_apply p) (P := lr7ep_P0) (cond := lr7ep_cond0)
        (by intro i j; exact lr7ep_e6_apply (lr7ep_emb0 i, lr7ep_emb0 j))
        lr7ep_cls_B6_b0 hB hMA
    · exact lr7ep_row (T := ggCoxeterMatrixD 6) (tab := lr7ep_tD6)
        (by intro p; exact lr7ep_d6_apply p) (P := lr7ep_P0) (cond := lr7ep_cond0)
        (by intro i j; exact lr7ep_e6_apply (lr7ep_emb0 i, lr7ep_emb0 j))
        lr7ep_cls_D6_b0 hD hMA
  · exact lr7ep_row (T := CoxeterMatrix.E₆) (tab := lr7ep_tE6)
      (by intro p; exact lr7ep_e6_apply p) (P := lr7ep_P0) (cond := lr7ep_cond0)
      (by intro i j; exact lr7ep_e6_apply (lr7ep_emb0 i, lr7ep_emb0 j))
      lr7ep_cls_E6_b0 hMe hMA
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard

private lemma lr7ep_weyl_row_b5 {M : CoxeterMatrix (Option (Fin 5))}
    (hW : GGIsWeylMatrix M)
    (hMA : ∀ i j : Fin 5, M (some i) (some j) =
      CoxeterMatrix.E₆ (lr7ep_emb5 i) (lr7ep_emb5 j)) :
    ∃ k : Fin 5, lr7ep_cond0 k ∧ ∀ i : Fin 5, M none (some i) = if i = k then 3 else 2 := by
  rw [GGIsWeylMatrix] at hW
  rcases hW with ⟨n, eT, hn, hcase⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ | ⟨eT, hMe⟩ |
    ⟨eT, hMe⟩
  · have hn6 : n = 6 := by
      have hcard := Fintype.card_congr eT
      simp [Fintype.card_fin, Fintype.card_option] at hcard
      omega
    subst hn6
    rcases hcase with hA | ⟨-, hB⟩ | ⟨-, hD⟩
    · exact lr7ep_row (T := CoxeterMatrix.A 6) (tab := lr7ep_tA 6)
        (by intro p; exact lr7ep_a6_apply p) (P := lr7ep_P5) (cond := lr7ep_cond0)
        (by intro i j; exact lr7ep_e6_apply (lr7ep_emb5 i, lr7ep_emb5 j))
        lr7ep_cls_A6_b5 hA hMA
    · exact lr7ep_row (T := CoxeterMatrix.B 6) (tab := lr7ep_tB6)
        (by intro p; exact lr7ep_b6_apply p) (P := lr7ep_P5) (cond := lr7ep_cond0)
        (by intro i j; exact lr7ep_e6_apply (lr7ep_emb5 i, lr7ep_emb5 j))
        lr7ep_cls_B6_b5 hB hMA
    · exact lr7ep_row (T := ggCoxeterMatrixD 6) (tab := lr7ep_tD6)
        (by intro p; exact lr7ep_d6_apply p) (P := lr7ep_P5) (cond := lr7ep_cond0)
        (by intro i j; exact lr7ep_e6_apply (lr7ep_emb5 i, lr7ep_emb5 j))
        lr7ep_cls_D6_b5 hD hMA
  · exact lr7ep_row (T := CoxeterMatrix.E₆) (tab := lr7ep_tE6)
      (by intro p; exact lr7ep_e6_apply p) (P := lr7ep_P5) (cond := lr7ep_cond0)
      (by intro i j; exact lr7ep_e6_apply (lr7ep_emb5 i, lr7ep_emb5 j))
      lr7ep_cls_E6_b5 hMe hMA
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard
  · exfalso
    have hcard := Fintype.card_congr eT
    simp [Fintype.card_fin, Fintype.card_option] at hcard

private lemma lr7ep_main_b0 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} (e : Fin 6 ≃ Λ)
    (hb0 : e.symm b = 0)
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (e.symm i) (e.symm j) : ZMod 3))
    (posEquiv : Fin 5 ≃ {i : Λ // i ≠ b})
    (hpos : ∀ k : Fin 5, e.symm ((posEquiv k : {i : Λ // i ≠ b}) : Λ) = lr7ep_emb0 k)
    (hemb : Function.Injective lr7ep_emb0) :
    ∃ (c0 : Fin 6) (m n : ℤ), GGDepEPat (e.symm b) c0 m n ∧
      ∀ i : {i : Λ // i ≠ b}, CK none (some i) = (if e.symm i = c0 then m else 0) ∧
        CK (some i) none = (if e.symm i = c0 then n else 0) := by
  obtain ⟨M, C, -, hW, hC, -, hMA, hcn, hnc⟩ := lr7ep_setup e hWK hCK hJ posEquiv hpos hemb
  obtain ⟨k, hk, hrowk⟩ := lr7ep_weyl_row_b0 hW hMA
  have hCrow : ∀ i : Fin 5, C none (some i) = (if i = k then (-1 : ℤ) else 0) ∧
      C (some i) none = (if i = k then (-1 : ℤ) else 0) := by
    intro i
    by_cases hik : i = k
    · subst hik
      have h3 : M none (some i) = 3 := by rw [hrowk i, if_pos rfl]
      simpa using lr7ep_cartan_of_three hC (by simp) h3
    · have h2 : M none (some i) = 2 := by rw [hrowk i, if_neg hik]
      simpa [hik] using lr7ep_cartan_of_two hC (by simp) h2
  have hpat : GGDepEPat (e.symm b) (lr7ep_emb0 k) (-1) (-1) := by
    rw [hb0]
    unfold GGDepEPat
    refine ⟨rfl, rfl, Or.inl ⟨rfl, ?_⟩⟩
    have hk' : k.val = 0 ∨ k.val = 1 ∨ k.val = 4 := hk
    rcases hk' with h | h | h
    · left; apply Fin.ext; simp [lr7ep_emb0]; omega
    · right; left; apply Fin.ext; simp [lr7ep_emb0]; omega
    · right; right; apply Fin.ext; simp [lr7ep_emb0]; omega
  refine lr7ep_assemble e posEquiv (emb := lr7ep_emb0) hpos hemb hpat ?_ ?_
  · intro i; rw [← hcn i]; exact (hCrow i).1
  · intro i; rw [← hnc i]; exact (hCrow i).2

private lemma lr7ep_main_b5 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} (e : Fin 6 ≃ Λ)
    (hb5 : e.symm b = 5)
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (e.symm i) (e.symm j) : ZMod 3))
    (posEquiv : Fin 5 ≃ {i : Λ // i ≠ b})
    (hpos : ∀ k : Fin 5, e.symm ((posEquiv k : {i : Λ // i ≠ b}) : Λ) = lr7ep_emb5 k)
    (hemb : Function.Injective lr7ep_emb5) :
    ∃ (c0 : Fin 6) (m n : ℤ), GGDepEPat (e.symm b) c0 m n ∧
      ∀ i : {i : Λ // i ≠ b}, CK none (some i) = (if e.symm i = c0 then m else 0) ∧
        CK (some i) none = (if e.symm i = c0 then n else 0) := by
  obtain ⟨M, C, -, hW, hC, -, hMA, hcn, hnc⟩ := lr7ep_setup e hWK hCK hJ posEquiv hpos hemb
  obtain ⟨k, hk, hrowk⟩ := lr7ep_weyl_row_b5 hW hMA
  have hCrow : ∀ i : Fin 5, C none (some i) = (if i = k then (-1 : ℤ) else 0) ∧
      C (some i) none = (if i = k then (-1 : ℤ) else 0) := by
    intro i
    by_cases hik : i = k
    · subst hik
      have h3 : M none (some i) = 3 := by rw [hrowk i, if_pos rfl]
      simpa using lr7ep_cartan_of_three hC (by simp) h3
    · have h2 : M none (some i) = 2 := by rw [hrowk i, if_neg hik]
      simpa [hik] using lr7ep_cartan_of_two hC (by simp) h2
  have hpat : GGDepEPat (e.symm b) (lr7ep_emb5 k) (-1) (-1) := by
    rw [hb5]
    unfold GGDepEPat
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    have hk' : k.val = 0 ∨ k.val = 1 ∨ k.val = 4 := hk
    rcases hk' with h | h | h
    · left; apply Fin.ext; simpa [lr7ep_emb5] using h
    · right; left; apply Fin.ext; simpa [lr7ep_emb5] using h
    · right; right; apply Fin.ext; simpa [lr7ep_emb5] using h
  refine lr7ep_assemble e posEquiv (emb := lr7ep_emb5) hpos hemb hpat ?_ ?_
  · intro i; rw [← hcn i]; exact (hCrow i).1
  · intro i; rw [← hnc i]; exact (hCrow i).2

private lemma lr7ep_main_b1 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} (e : Fin 6 ≃ Λ)
    (hb1 : e.symm b = 1)
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hKE : e.symm b = 1 → GGIsTypeE6 MK)
    (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (e.symm i) (e.symm j) : ZMod 3))
    (posEquiv : Fin 5 ≃ {i : Λ // i ≠ b})
    (hpos : ∀ k : Fin 5, e.symm ((posEquiv k : {i : Λ // i ≠ b}) : Λ) = lr7ep_emb1 k)
    (hemb : Function.Injective lr7ep_emb1) :
    ∃ (c0 : Fin 6) (m n : ℤ), GGDepEPat (e.symm b) c0 m n ∧
      ∀ i : {i : Λ // i ≠ b}, CK none (some i) = (if e.symm i = c0 then m else 0) ∧
        CK (some i) none = (if e.symm i = c0 then n else 0) := by
  obtain ⟨M, C, hMdef, hW, hC, -, hMA, hcn, hnc⟩ := lr7ep_setup e hWK hCK hJ posEquiv hpos hemb
  have hMe : GGIsTypeE6 M := by
    rw [hMdef]
    exact lr7ep_typeE6_reindex (hKE hb1) (Equiv.optionCongr posEquiv).symm
  obtain ⟨eT, hMe'⟩ := hMe
  obtain ⟨k, hk, hrowk⟩ := lr7ep_row (T := CoxeterMatrix.E₆) (tab := lr7ep_tE6)
      (by intro p; exact lr7ep_e6_apply p) (P := lr7ep_P1) (cond := lr7ep_cond1)
      (by intro i j; exact lr7ep_e6_apply (lr7ep_emb1 i, lr7ep_emb1 j))
      lr7ep_cls_E6_b1 hMe' hMA
  have hk2 : k.val = 2 := hk
  have hCrow : ∀ i : Fin 5, C none (some i) = (if i = k then (-1 : ℤ) else 0) ∧
      C (some i) none = (if i = k then (-1 : ℤ) else 0) := by
    intro i
    by_cases hik : i = k
    · subst hik
      have h3 : M none (some i) = 3 := by rw [hrowk i, if_pos rfl]
      simpa using lr7ep_cartan_of_three hC (by simp) h3
    · have h2 : M none (some i) = 2 := by rw [hrowk i, if_neg hik]
      simpa [hik] using lr7ep_cartan_of_two hC (by simp) h2
  have hpat : GGDepEPat (e.symm b) (lr7ep_emb1 k) (-1) (-1) := by
    rw [hb1]
    unfold GGDepEPat
    refine ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
    apply Fin.ext
    simp [lr7ep_emb1, hk2]
  refine lr7ep_assemble e posEquiv (emb := lr7ep_emb1) hpos hemb hpat ?_ ?_
  · intro i; rw [← hcn i]; exact (hCrow i).1
  · intro i; rw [← hnc i]; exact (hCrow i).2

theorem ggDepE_pattern {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} (e : Fin 6 ≃ Λ)
    (hb : e.symm b = 0 ∨ e.symm b = 1 ∨ e.symm b = 5)
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod 3) =
      ((CartanMatrix.E 6) (e.symm i) (e.symm j) : ZMod 3))
    (hKE : e.symm b = 1 → GGIsTypeE6 MK) :
    ∃ (c0 : Fin 6) (m n : ℤ), GGDepEPat (e.symm b) c0 m n ∧
      ∀ i : {i : Λ // i ≠ b}, CK none (some i) = (if e.symm i = c0 then m else 0) ∧
        CK (some i) none = (if e.symm i = c0 then n else 0) := by
  rcases hb with hb0 | hb1 | hb5
  ·
    have hemb0_inv : ∀ k : Fin 5, lr7ep_embInv0 (lr7ep_emb0 k) = k := by
      intro k; apply Fin.ext; simp [lr7ep_embInv0, lr7ep_emb0]
    have hemb0_ne : ∀ k : Fin 5, lr7ep_emb0 k ≠ e.symm b := by
      rw [hb0]
      decide
    have hemb0_inv' : ∀ j : Fin 6, j ≠ e.symm b → lr7ep_emb0 (lr7ep_embInv0 j) = j := by
      intro j hj
      have hj0 : j.val ≠ 0 := by
        rw [hb0] at hj
        intro h
        exact hj (Fin.ext h)
      apply Fin.ext
      simp [lr7ep_emb0, lr7ep_embInv0]
      omega
    have hemb0 : Function.Injective lr7ep_emb0 := by
      intro a b h
      have := congrArg lr7ep_embInv0 h
      rwa [hemb0_inv a, hemb0_inv b] at this
    let posEquiv : Fin 5 ≃ {i : Λ // i ≠ b} :=
      { toFun := fun k => ⟨e (lr7ep_emb0 k), by
          intro h
          have h' : lr7ep_emb0 k = e.symm b := by
            rw [← e.symm_apply_apply (lr7ep_emb0 k), h]
          exact hemb0_ne k h'⟩
        invFun := fun i => lr7ep_embInv0 (e.symm i.val)
        left_inv := fun k => by
          show lr7ep_embInv0 (e.symm (e (lr7ep_emb0 k))) = k
          rw [e.symm_apply_apply]
          exact hemb0_inv k
        right_inv := fun i => by
          apply Subtype.ext
          show e (lr7ep_emb0 (lr7ep_embInv0 (e.symm i.val))) = i.val
          have hne : e.symm i.val ≠ e.symm b := fun h => i.property (e.symm.injective h)
          rw [hemb0_inv' (e.symm i.val) hne]
          exact e.apply_symm_apply i.val }
    have hpos : ∀ k : Fin 5, e.symm ((posEquiv k : {i : Λ // i ≠ b}) : Λ) = lr7ep_emb0 k := by
      intro k
      show e.symm (e (lr7ep_emb0 k)) = lr7ep_emb0 k
      exact e.symm_apply_apply (lr7ep_emb0 k)
    exact lr7ep_main_b0 e hb0 hWK hCK hJ posEquiv hpos hemb0
  ·
    have hemb1_inv : ∀ k : Fin 5, lr7ep_embInv1 (lr7ep_emb1 k) = k := by
      intro k
      fin_cases k <;> simp [lr7ep_embInv1, lr7ep_emb1]
    have hemb1_ne : ∀ k : Fin 5, lr7ep_emb1 k ≠ e.symm b := by
      rw [hb1]
      decide
    have hemb1_inv' : ∀ j : Fin 6, j ≠ e.symm b → lr7ep_emb1 (lr7ep_embInv1 j) = j := by
      intro j hj
      have hj1 : j.val ≠ 1 := by
        rw [hb1] at hj
        intro h
        exact hj (Fin.ext h)
      fin_cases j <;> simp_all [lr7ep_emb1, lr7ep_embInv1]
    have hemb1 : Function.Injective lr7ep_emb1 := by
      intro a b h
      have := congrArg lr7ep_embInv1 h
      rwa [hemb1_inv a, hemb1_inv b] at this
    let posEquiv : Fin 5 ≃ {i : Λ // i ≠ b} :=
      { toFun := fun k => ⟨e (lr7ep_emb1 k), by
          intro h
          have h' : lr7ep_emb1 k = e.symm b := by
            rw [← e.symm_apply_apply (lr7ep_emb1 k), h]
          exact hemb1_ne k h'⟩
        invFun := fun i => lr7ep_embInv1 (e.symm i.val)
        left_inv := fun k => by
          show lr7ep_embInv1 (e.symm (e (lr7ep_emb1 k))) = k
          rw [e.symm_apply_apply]
          exact hemb1_inv k
        right_inv := fun i => by
          apply Subtype.ext
          show e (lr7ep_emb1 (lr7ep_embInv1 (e.symm i.val))) = i.val
          have hne : e.symm i.val ≠ e.symm b := fun h => i.property (e.symm.injective h)
          rw [hemb1_inv' (e.symm i.val) hne]
          exact e.apply_symm_apply i.val }
    have hpos : ∀ k : Fin 5, e.symm ((posEquiv k : {i : Λ // i ≠ b}) : Λ) = lr7ep_emb1 k := by
      intro k
      show e.symm (e (lr7ep_emb1 k)) = lr7ep_emb1 k
      exact e.symm_apply_apply (lr7ep_emb1 k)
    exact lr7ep_main_b1 e hb1 hWK hKE hCK hJ posEquiv hpos hemb1
  ·
    have hemb5_inv : ∀ k : Fin 5, lr7ep_embInv5 (lr7ep_emb5 k) = k := by
      intro k
      unfold lr7ep_embInv5 lr7ep_emb5
      rw [dif_pos k.isLt]
    have hemb5_ne : ∀ k : Fin 5, lr7ep_emb5 k ≠ e.symm b := by
      rw [hb5]
      decide
    have hemb5_inv' : ∀ j : Fin 6, j ≠ e.symm b → lr7ep_emb5 (lr7ep_embInv5 j) = j := by
      intro j hj
      have hj5 : j.val ≠ 5 := by
        rw [hb5] at hj
        intro h
        exact hj (Fin.ext h)
      have hjlt : j.val < 5 := by omega
      unfold lr7ep_embInv5 lr7ep_emb5
      rw [dif_pos hjlt]
    have hemb5 : Function.Injective lr7ep_emb5 := by
      intro a b h
      have := congrArg lr7ep_embInv5 h
      rwa [hemb5_inv a, hemb5_inv b] at this
    let posEquiv : Fin 5 ≃ {i : Λ // i ≠ b} :=
      { toFun := fun k => ⟨e (lr7ep_emb5 k), by
          intro h
          have h' : lr7ep_emb5 k = e.symm b := by
            rw [← e.symm_apply_apply (lr7ep_emb5 k), h]
          exact hemb5_ne k h'⟩
        invFun := fun i => lr7ep_embInv5 (e.symm i.val)
        left_inv := fun k => by
          show lr7ep_embInv5 (e.symm (e (lr7ep_emb5 k))) = k
          rw [e.symm_apply_apply]
          exact hemb5_inv k
        right_inv := fun i => by
          apply Subtype.ext
          show e (lr7ep_emb5 (lr7ep_embInv5 (e.symm i.val))) = i.val
          have hne : e.symm i.val ≠ e.symm b := fun h => i.property (e.symm.injective h)
          rw [hemb5_inv' (e.symm i.val) hne]
          exact e.apply_symm_apply i.val }
    have hpos : ∀ k : Fin 5, e.symm ((posEquiv k : {i : Λ // i ≠ b}) : Λ) = lr7ep_emb5 k := by
      intro k
      show e.symm (e (lr7ep_emb5 k)) = lr7ep_emb5 k
      exact e.symm_apply_apply (lr7ep_emb5 k)
    exact lr7ep_main_b5 e hb5 hWK hCK hJ posEquiv hpos hemb5

end CFSG.StandardType
