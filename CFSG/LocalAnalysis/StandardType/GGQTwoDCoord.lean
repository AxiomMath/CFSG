module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import Mathlib.Algebra.Group.Subgroup.Map

public section

open Module

namespace CFSG.StandardType

@[expose] def ggDSimple (p m : ℕ) (i : Fin m) : Fin m → ZMod p := fun j =>
  if (i : ℕ) + 1 < m then
    (if (j : ℕ) = i then 1 else if (j : ℕ) = i + 1 then -1 else 0)
  else
    (if (j : ℕ) + 2 = m ∨ (j : ℕ) + 1 = m then 1 else 0)

private lemma ggQ2x_sum_nat_indicator (p m : ℕ) (k : ℕ) (hk : k < m)
    (c : ZMod p) (g : Fin m → ZMod p) :
    ∑ l : Fin m, (if (l:ℕ) = k then c else 0) * g l = c * g ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro b _ hb
    have hb' : (b:ℕ) ≠ k := fun h => hb (Fin.ext h)
    simp [hb']
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma ggQ2x_sum_ggDSimple (p m : ℕ) (i : Fin m) (hi : (i:ℕ)+1 < m)
    (g : Fin m → ZMod p) :
    ∑ l : Fin m, ggDSimple p m i l * g l = g i - g ⟨(i:ℕ)+1, hi⟩ := by
  have hpoint : ∀ l : Fin m, ggDSimple p m i l =
      (if (l:ℕ) = (i:ℕ) then (1:ZMod p) else 0) +
      (if (l:ℕ) = (i:ℕ)+1 then (-1:ZMod p) else 0) := by
    intro l
    rw [ggDSimple, if_pos hi]
    by_cases h1 : (l:ℕ) = (i:ℕ)
    · have h2 : ¬ (l:ℕ) = (i:ℕ)+1 := by omega
      simp [h1, h2]
    · by_cases h2 : (l:ℕ) = (i:ℕ)+1
      · simp [h1, h2]
      · simp [h1, h2]
  calc ∑ l : Fin m, ggDSimple p m i l * g l
      = ∑ l : Fin m, ((if (l:ℕ) = (i:ℕ) then (1:ZMod p) else 0) * g l +
              (if (l:ℕ) = (i:ℕ)+1 then (-1:ZMod p) else 0) * g l) := by
          apply Finset.sum_congr rfl; intro l _; rw [hpoint l]; ring
    _ = (∑ l : Fin m, (if (l:ℕ) = (i:ℕ) then (1:ZMod p) else 0) * g l) +
        (∑ l : Fin m, (if (l:ℕ) = (i:ℕ)+1 then (-1:ZMod p) else 0) * g l) := by
          rw [Finset.sum_add_distrib]
    _ = 1 * g i + (-1) * g ⟨(i:ℕ)+1, hi⟩ := by
          rw [ggQ2x_sum_nat_indicator (k := (i:ℕ)) (hk := i.isLt),
            ggQ2x_sum_nat_indicator (k := (i:ℕ)+1) (hk := hi)]
    _ = g i - g ⟨(i:ℕ)+1, hi⟩ := by ring

private lemma ggQ2x_sum_ggDSimple_fork (p m : ℕ) (hm : 2 ≤ m) (i : Fin m)
    (hi : ¬ (i:ℕ)+1 < m) (g : Fin m → ZMod p) :
    ∑ l : Fin m, ggDSimple p m i l * g l = g ⟨m-2, by omega⟩ + g ⟨m-1, by omega⟩ := by
  have hpoint : ∀ l : Fin m, ggDSimple p m i l =
      (if (l:ℕ) = m-2 then (1:ZMod p) else 0) +
      (if (l:ℕ) = m-1 then (1:ZMod p) else 0) := by
    intro l
    rw [ggDSimple, if_neg hi]
    by_cases h2 : (l:ℕ)+2 = m
    · have h : (l:ℕ) = m - 2 := by omega
      rw [if_pos (Or.inl h2), h]
      have hlt : ¬ (m - 2 : ℕ) = m - 1 := by omega
      simp [hlt]
    · by_cases h1 : (l:ℕ)+1 = m
      · have h : (l:ℕ) = m - 1 := by omega
        rw [if_pos (Or.inr h1), h]
        have hlt : ¬ (m - 1 : ℕ) = m - 2 := by omega
        simp [hlt]
      · have hc : ¬ ((l:ℕ)+2 = m ∨ (l:ℕ)+1 = m) := by omega
        rw [if_neg hc]
        have hlt2 : ¬ (l:ℕ) = m - 2 := by omega
        have hlt1 : ¬ (l:ℕ) = m - 1 := by omega
        simp [hlt2, hlt1]
  calc ∑ l : Fin m, ggDSimple p m i l * g l
      = ∑ l : Fin m, ((if (l:ℕ) = m-2 then (1:ZMod p) else 0) * g l +
              (if (l:ℕ) = m-1 then (1:ZMod p) else 0) * g l) := by
          apply Finset.sum_congr rfl; intro l _; rw [hpoint l]; ring
    _ = (∑ l : Fin m, (if (l:ℕ) = m-2 then (1:ZMod p) else 0) * g l) +
        (∑ l : Fin m, (if (l:ℕ) = m-1 then (1:ZMod p) else 0) * g l) := by
          rw [Finset.sum_add_distrib]
    _ = 1 * g ⟨m-2, by omega⟩ + 1 * g ⟨m-1, by omega⟩ := by
          rw [ggQ2x_sum_nat_indicator (k := m-2) (hk := by omega),
            ggQ2x_sum_nat_indicator (k := m-1) (hk := by omega)]
    _ = g ⟨m-2, by omega⟩ + g ⟨m-1, by omega⟩ := by ring

private lemma ggQ2x_eval_chain (p m : ℕ) (j : Fin m) (hj : (j:ℕ)+1 < m) (l : Fin m) :
    ggDSimple p m j l =
      (if (l:ℕ) = (j:ℕ) then (1:ZMod p) else 0) +
      (if (l:ℕ) = (j:ℕ)+1 then (-1:ZMod p) else 0) := by
  rw [ggDSimple, if_pos hj]
  by_cases h1 : (l:ℕ) = (j:ℕ)
  · have h2 : ¬ (l:ℕ) = (j:ℕ)+1 := by omega
    simp [h1, h2]
  · by_cases h2 : (l:ℕ) = (j:ℕ)+1
    · simp [h1, h2]
    · simp [h1, h2]

private lemma ggQ2x_eval_fork (p m : ℕ) (j : Fin m) (hj : ¬ (j:ℕ)+1 < m) (l : Fin m) :
    ggDSimple p m j l =
      (if (l:ℕ)+2 = m ∨ (l:ℕ)+1 = m then (1:ZMod p) else 0) := by
  rw [ggDSimple, if_neg hj]

private lemma ggQ2x_dot_cc (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : (i:ℕ)+1 < m) (hj : (j:ℕ)+1 < m) :
    (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (CartanMatrix.D m i j : ZMod p) := by
  have hi' : (i:ℕ) < m := i.isLt
  have hj' : (j:ℕ) < m := j.isLt
  rw [ggQ2x_sum_ggDSimple p m i hi]
  rw [ggQ2x_eval_chain p m j hj i, ggQ2x_eval_chain p m j hj ⟨(i:ℕ)+1, hi⟩]
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2x_dot_cf (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : (i:ℕ)+1 < m) (hj : ¬ (j:ℕ)+1 < m) :
    (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (CartanMatrix.D m i j : ZMod p) := by
  have hi' : (i:ℕ) < m := i.isLt
  have hj' : (j:ℕ) < m := j.isLt
  rw [ggQ2x_sum_ggDSimple p m i hi]
  rw [ggQ2x_eval_fork p m j hj i, ggQ2x_eval_fork p m j hj ⟨(i:ℕ)+1, hi⟩]
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2x_dot_fc (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : ¬ (i:ℕ)+1 < m) (hj : (j:ℕ)+1 < m) :
    (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (CartanMatrix.D m i j : ZMod p) := by
  have hi' : (i:ℕ) < m := i.isLt
  have hj' : (j:ℕ) < m := j.isLt
  rw [ggQ2x_sum_ggDSimple_fork p m (by omega) i hi]
  rw [ggQ2x_eval_chain p m j hj ⟨m-2, by omega⟩, ggQ2x_eval_chain p m j hj ⟨m-1, by omega⟩]
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2x_dot_ff (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m)
    (hi : ¬ (i:ℕ)+1 < m) (hj : ¬ (j:ℕ)+1 < m) :
    (∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l) =
      (CartanMatrix.D m i j : ZMod p) := by
  have hi' : (i:ℕ) < m := i.isLt
  have hj' : (j:ℕ) < m := j.isLt
  rw [ggQ2x_sum_ggDSimple_fork p m (by omega) i hi]
  rw [ggQ2x_eval_fork p m j hj ⟨m-2, by omega⟩, ggQ2x_eval_fork p m j hj ⟨m-1, by omega⟩]
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2x_simple_dot (p m : ℕ) (hm : 4 ≤ m) (i j : Fin m) :
    ∑ l : Fin m, ggDSimple p m i l * ggDSimple p m j l =
      (CartanMatrix.D m i j : ZMod p) := by
  by_cases hi : (i:ℕ)+1 < m
  · by_cases hj : (j:ℕ)+1 < m
    · exact ggQ2x_dot_cc p m hm i j hi hj
    · exact ggQ2x_dot_cf p m hm i j hi hj
  · by_cases hj : (j:ℕ)+1 < m
    · exact ggQ2x_dot_fc p m hm i j hi hj
    · exact ggQ2x_dot_ff p m hm i j hi hj

private noncomputable def ggQ2x_fvec (p m : ℕ) (k : Fin m) : Fin m → ZMod p :=
  Pi.single k 1

private noncomputable def ggQ2x_g (p m : ℕ) (l : ℕ) : Fin m → ZMod p :=
  if h : l < m then ggQ2x_fvec p m ⟨l, h⟩ else 0

private noncomputable def ggQ2x_h (p m : ℕ) (l : ℕ) : Fin m → ZMod p :=
  if h : l < m then ggDSimple p m ⟨l, h⟩ else 0

private lemma ggQ2x_chain_rel (p m : ℕ) (i : Fin m) (hi : (i:ℕ)+1 < m) :
    ggDSimple p m i = ggQ2x_fvec p m i - ggQ2x_fvec p m ⟨(i:ℕ)+1, hi⟩ := by
  funext j
  rw [ggDSimple, if_pos hi]
  simp only [ggQ2x_fvec, Pi.sub_apply]
  by_cases h1 : (j:ℕ) = (i:ℕ)
  · have hj : j = i := Fin.ext h1
    subst j
    have hne : (Pi.single (⟨(i:ℕ)+1, hi⟩ : Fin m) (1:ZMod p) : Fin m → ZMod p) i = 0 := by
      rw [Pi.single_eq_of_ne (show i ≠ (⟨(i:ℕ)+1, hi⟩ : Fin m) from by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)]
    rw [if_pos h1, Pi.single_eq_same, hne]; ring
  · have hPi : (Pi.single i (1:ZMod p) : Fin m → ZMod p) j = 0 := by
      rw [Pi.single_eq_of_ne (show j ≠ i from fun h => h1 (congrArg Fin.val h))]
    by_cases h2 : (j:ℕ) = (i:ℕ)+1
    · have hj : j = ⟨(i:ℕ)+1, hi⟩ := Fin.ext h2
      subst j
      rw [if_neg h1, if_pos h2, Pi.single_eq_same, hPi]; ring
    · have hPi2 : (Pi.single (⟨(i:ℕ)+1, hi⟩ : Fin m) (1:ZMod p) : Fin m → ZMod p) j = 0 := by
        rw [Pi.single_eq_of_ne (show j ≠ (⟨(i:ℕ)+1, hi⟩ : Fin m) from by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)]
      rw [if_neg h1, if_neg h2, hPi, hPi2]; ring

private lemma ggQ2x_fork_rel (p m : ℕ) (hm : 2 ≤ m) (hm1 : m - 1 < m) :
    ggDSimple p m ⟨m-1, hm1⟩ =
      ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, hm1⟩ := by
  funext j
  have hjlt : (j:ℕ) < m := j.isLt
  rw [ggDSimple, if_neg (by show ¬ (m-1)+1 < m; omega)]
  simp only [ggQ2x_fvec, Pi.add_apply]
  by_cases h2 : (j:ℕ)+2 = m
  · have hlt : m - 2 < m := by omega
    have hj : j = ⟨m-2, hlt⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
    subst j
    have hne : (⟨m-2, hlt⟩ : Fin m) ≠ ⟨m-1, hm1⟩ := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    rw [if_pos (Or.inl h2), Pi.single_eq_same, Pi.single_eq_of_ne hne]
    ring
  · by_cases h1 : (j:ℕ)+1 = m
    · have hj : j = ⟨m-1, hm1⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
      subst j
      have hlt2 : m - 2 < m := by omega
      have hne : (⟨m-1, hm1⟩ : Fin m) ≠ ⟨m-2, hlt2⟩ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
      rw [if_pos (Or.inr h1), Pi.single_eq_same, Pi.single_eq_of_ne hne]
      ring
    · have hc : ¬ ((j:ℕ)+2 = m ∨ (j:ℕ)+1 = m) := by omega
      rw [if_neg hc]
      have hlt2 : m - 2 < m := by omega
      have h1' : j ≠ ⟨m-2, hlt2⟩ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
      have h2' : j ≠ ⟨m-1, hm1⟩ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
      rw [Pi.single_eq_of_ne h1', Pi.single_eq_of_ne h2']
      ring

private lemma ggQ2x_g_apply (p m : ℕ) (l : ℕ) (hl : l < m) :
    ggQ2x_g p m l = ggQ2x_fvec p m ⟨l, hl⟩ := by
  simp [ggQ2x_g, hl]

private lemma ggQ2x_h_apply (p m : ℕ) (l : ℕ) (hl : l < m) :
    ggQ2x_h p m l = ggDSimple p m ⟨l, hl⟩ := by
  simp [ggQ2x_h, hl]

private lemma ggQ2x_g_sub (p m : ℕ) (l : ℕ) (hl : l + 1 < m) :
    ggQ2x_g p m l - ggQ2x_g p m (l + 1) = ggQ2x_h p m l := by
  have hl' : l < m := by omega
  rw [ggQ2x_g_apply p m l hl', ggQ2x_g_apply p m (l + 1) hl, ggQ2x_h_apply p m l hl']
  exact (ggQ2x_chain_rel p m ⟨l, hl'⟩ hl).symm

private lemma ggQ2x_g_sub' (p m : ℕ) (l : ℕ) (hl : l + 1 < m) :
    ggQ2x_g p m (l + 1) - ggQ2x_g p m l = - ggQ2x_h p m l := by
  rw [← neg_sub, ggQ2x_g_sub p m l hl]

private lemma ggQ2x_telescope (p m : ℕ) (k : ℕ) (hk : k ≤ m - 2) (hkm : k < m) :
    ggQ2x_fvec p m ⟨k, hkm⟩ - ggQ2x_fvec p m ⟨m-2, by omega⟩ =
      ∑ l ∈ Finset.Ico k (m-2), ggQ2x_h p m l := by
  have h := Finset.sum_Ico_sub (f := ggQ2x_g p m) (m := k) (n := m-2) hk
  rw [Finset.sum_congr rfl (fun l hl => ggQ2x_g_sub' p m l (by
    have := (Finset.mem_Ico.mp hl).2; omega))] at h
  rw [Finset.sum_neg_distrib, ggQ2x_g_apply p m k hkm,
    ggQ2x_g_apply p m (m-2) (by omega), ← neg_sub] at h
  exact (neg_inj.mp h).symm

private lemma ggQ2x_h_mem (p m : ℕ) (l : ℕ) :
    ggQ2x_h p m l ∈ Submodule.span (ZMod p) (Set.range (ggDSimple p m)) := by
  by_cases h : l < m
  · rw [ggQ2x_h_apply p m l h]
    exact Submodule.subset_span ⟨⟨l, h⟩, rfl⟩
  · rw [show ggQ2x_h p m l = 0 from by simp [ggQ2x_h, h]]
    exact Submodule.zero_mem _

private lemma ggQ2x_fvec_mem (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hm : 4 ≤ m)
    (k : Fin m) :
    ggQ2x_fvec p m k ∈ Submodule.span (ZMod p) (Set.range (ggDSimple p m)) := by
  set S := Submodule.span (ZMod p) (Set.range (ggDSimple p m)) with hS
  have hm2 : 2 ≤ m := by omega
  have hm1 : m - 1 < m := by omega
  have hm2' : m - 2 < m := by omega
  have h2ne : (2:ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hchain2 : (⟨m-2, hm2'⟩ : Fin m).val + 1 < m := by simp; omega
  have hchain' : ggDSimple p m ⟨m-2, hm2'⟩ =
      ggQ2x_fvec p m ⟨m-2, hm2'⟩ - ggQ2x_fvec p m ⟨m-1, hm1⟩ := by
    rw [ggQ2x_chain_rel p m ⟨m-2, hm2'⟩ hchain2]
    rw [show Fin.mk ((⟨m-2, hm2'⟩ : Fin m).val + 1) hchain2 = ⟨m-1, hm1⟩ from by
      apply Fin.ext; simp only [Fin.val_mk]; omega]
  have hsum2 : ggDSimple p m ⟨m-2, hm2'⟩ + ggDSimple p m ⟨m-1, hm1⟩ =
      (2:ZMod p) • ggQ2x_fvec p m ⟨m-2, hm2'⟩ := by
    rw [hchain', ggQ2x_fork_rel p m hm2 hm1]; module
  have hsum1 : ggDSimple p m ⟨m-1, hm1⟩ - ggDSimple p m ⟨m-2, hm2'⟩ =
      (2:ZMod p) • ggQ2x_fvec p m ⟨m-1, hm1⟩ := by
    rw [hchain', ggQ2x_fork_rel p m hm2 hm1]; module
  have hf_m2 : ggQ2x_fvec p m ⟨m-2, hm2'⟩ ∈ S := by
    rw [show ggQ2x_fvec p m ⟨m-2, hm2'⟩ =
        (2:ZMod p)⁻¹ • (ggDSimple p m ⟨m-2, hm2'⟩ +
          ggDSimple p m ⟨m-1, hm1⟩) by
      rw [hsum2, smul_smul, inv_mul_cancel₀ h2ne, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.subset_span ⟨⟨m-2, hm2'⟩, rfl⟩)
      (Submodule.subset_span ⟨⟨m-1, hm1⟩, rfl⟩))
  have hf_m1 : ggQ2x_fvec p m ⟨m-1, hm1⟩ ∈ S := by
    rw [show ggQ2x_fvec p m ⟨m-1, hm1⟩ =
        (2:ZMod p)⁻¹ • (ggDSimple p m ⟨m-1, hm1⟩ -
          ggDSimple p m ⟨m-2, hm2'⟩) by
      rw [hsum1, smul_smul, inv_mul_cancel₀ h2ne, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span ⟨⟨m-1, hm1⟩, rfl⟩)
      (Submodule.subset_span ⟨⟨m-2, hm2'⟩, rfl⟩))
  by_cases hk1 : k = ⟨m-1, hm1⟩
  · rw [hk1]; exact hf_m1
  · by_cases hk2 : k = ⟨m-2, hm2'⟩
    · rw [hk2]; exact hf_m2
    · have hkval : (k:ℕ) ≤ m - 2 := by
        have h1 : (k:ℕ) ≠ m-1 := fun h => hk1 (Fin.ext h)
        have h2 : (k:ℕ) ≠ m-2 := fun h => hk2 (Fin.ext h)
        omega
      have hklt : (k:ℕ) < m := k.isLt
      have htele := ggQ2x_telescope p m (k:ℕ) hkval hklt
      have hsub : ggQ2x_fvec p m k - ggQ2x_fvec p m ⟨m-2, hm2'⟩ =
          ∑ l ∈ Finset.Ico (k:ℕ) (m-2), ggQ2x_h p m l := by
        convert htele using 2
      rw [show ggQ2x_fvec p m k = (ggQ2x_fvec p m k - ggQ2x_fvec p m ⟨m-2, hm2'⟩) +
          ggQ2x_fvec p m ⟨m-2, hm2'⟩ by abel]
      apply Submodule.add_mem
      · rw [hsub]
        exact Submodule.sum_mem _ (fun l _ => ggQ2x_h_mem p m l)
      · exact hf_m2

private lemma ggQ2x_span_top (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hm : 4 ≤ m) :
    ⊤ ≤ Submodule.span (ZMod p) (Set.range (ggDSimple p m)) := by
  rw [← (Pi.basisFun (ZMod p) (Fin m)).span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  rw [Pi.basisFun_apply]
  exact ggQ2x_fvec_mem p m hp2 hm k

private lemma ggQ2x_linearIndependent (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hm : 4 ≤ m) :
    LinearIndependent (ZMod p) (ggDSimple p m) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank (ggQ2x_span_top p m hp2 hm)
  simp [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]

private lemma ggQ2x_cartan_D {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (e : Fin m ≃ D.ι) (he : D.coxeter = (ggCoxeterMatrixD m).reindex e) (i j : Fin m) :
    D.cartan (e i) (e j) = CartanMatrix.D m i j := by
  by_cases hij : i = j
  · subst hij
    rw [D.isCartan.1 (e i)]; simp
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hcox : D.coxeter (e i) (e j) = ggCoxeterMatrixD m i j := by
      rw [he, CoxeterMatrix.reindex_apply]; simp
    have hlabel : ggCoxeterMatrixD m i j = 2 ∨ ggCoxeterMatrixD m i j = 3 := by
      by_cases h : CartanMatrix.D m i j = 0
      · exact Or.inl (by rw [ggCoxeterMatrixD_apply]; simp [hij, h])
      · exact Or.inr (by rw [ggCoxeterMatrixD_apply]; simp [hij, h])
    rcases hlabel with h2 | h3
    · have hD0 : CartanMatrix.D m i j = 0 := by
        by_contra h0
        rw [ggCoxeterMatrixD_apply, if_neg hij] at h2
        simp [h0] at h2
      rw [hD0]
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
    · have hDne : CartanMatrix.D m i j ≠ 0 := by
        intro h0; rw [ggCoxeterMatrixD_apply, if_neg hij, h0] at h3; simp at h3
      have hDneg : CartanMatrix.D m i j = -1 := by
        rcases (CartanMatrix.isSimplyLaced_D m) hij with h | h
        · exact absurd h hDne
        · exact h
      rw [hDneg]
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [hcox] at hm; omega
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega

theorem ggQ2_D_coordinates {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (D : GGQ2Lin p) (hbas : D.Basis)
    {m : ℕ} (hm : 4 ≤ m) (e : Fin m ≃ D.ι)
    (he : D.coxeter = (ggCoxeterMatrixD m).reindex e) :
    ∃ τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p),
      (∀ i, τ (D.coroot (e i)) = ggDSimple p m i) ∧
      ∀ i v, D.root (e i) v = ∑ j, ggDSimple p m i j * τ v j := by
  have hu := ggQ2x_linearIndependent p m hp2 hm
  letI : Decidable (Nonempty (Fin m)) := Classical.propDecidable _
  let bu : Basis (Fin m) (ZMod p) (Fin m → ZMod p) := basisOfPiSpaceOfLinearIndependent hu
  have hbu : ∀ i, bu i = ggDSimple p m i := fun i => by
    dsimp only [bu]
    exact congrFun (coe_basisOfPiSpaceOfLinearIndependent hu) i
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hli : LinearIndependent (ZMod p) (fun i : Fin m => D.coroot (e i)) :=
    hbas.1.comp e e.injective
  let b : Basis (Fin m) (ZMod p) D.V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by
      rw [Fintype.card_congr e]; exact hbas.2)
  have hb : ∀ i, b i = D.coroot (e i) := fun i => by
    dsimp only [b]
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli _) i
  let τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p) := b.equiv bu (Equiv.refl (Fin m))
  have hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple p m i := fun i => by
    rw [← hb i]
    rw [show (b.equiv bu (Equiv.refl (Fin m))) (b i) = bu i from by
      simp [Module.Basis.equiv_apply]]
    exact hbu i
  refine ⟨τ, hτ, ?_⟩
  intro i v
  let φ : D.V →ₗ[ZMod p] ZMod p :=
    ∑ j : Fin m, ggDSimple p m i j •
      (LinearMap.proj (R := ZMod p) (φ := fun _ : Fin m => ZMod p) j).comp
        (τ : D.V →ₗ[ZMod p] (Fin m → ZMod p))
  have hφ : D.root (e i) = φ := by
    apply b.ext
    intro j
    simp only [φ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul, LinearEquiv.coe_coe]
    rw [hb j, D.pairing, ggQ2x_cartan_D D e he i j, hτ j]
    exact (ggQ2x_simple_dot p m hm i j).symm
  rw [hφ]
  simp only [φ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, smul_eq_mul, LinearEquiv.coe_coe]

private noncomputable def ggQ2x_dotLin (p m : ℕ) (u : Fin m → ZMod p) :
    (Fin m → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun v := ∑ j, u j * v j
  map_add' a b := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by simp only [RingHom.id_apply]; ring)

private lemma ggQ2x_dotLin_apply (p m : ℕ) (u v : Fin m → ZMod p) :
    ggQ2x_dotLin p m u v = ∑ j, u j * v j := rfl

private lemma ggQ2x_u_self (p m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    ggQ2x_dotLin p m (ggDSimple p m i) (ggDSimple p m i) = 2 := by
  rw [ggQ2x_dotLin_apply, ggQ2x_simple_dot p m hm i i]
  simp

private noncomputable def ggQ2x_r (p m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p) :=
  Module.reflection (x := ggDSimple p m i) (ggQ2x_u_self p m hm i)

private lemma ggQ2x_r_apply (p m : ℕ) (hm : 4 ≤ m) (i : Fin m) (v : Fin m → ZMod p) :
    ggQ2x_r p m hm i v = v - (ggQ2x_dotLin p m (ggDSimple p m i) v) • ggDSimple p m i :=
  Module.reflection_apply v (ggQ2x_u_self p m hm i)

private noncomputable def ggQ2x_sgn (p m : ℕ) (j : Fin m) : ZMod p :=
  if (j:ℕ) = 0 ∨ (j:ℕ) = m-1 then (-1:ZMod p) else 1

private noncomputable def ggQ2x_H (p m : ℕ) :
    (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p) where
  toFun v := fun j => ggQ2x_sgn p m j * v j
  invFun v := fun j => ggQ2x_sgn p m j * v j
  left_inv v := by
    funext j
    by_cases h : (j:ℕ) = 0 ∨ (j:ℕ) = m-1
    · simp only [ggQ2x_sgn, if_pos h]; ring
    · simp only [ggQ2x_sgn, if_neg h]; ring
  right_inv v := by
    funext j
    by_cases h : (j:ℕ) = 0 ∨ (j:ℕ) = m-1
    · simp only [ggQ2x_sgn, if_pos h]; ring
    · simp only [ggQ2x_sgn, if_neg h]; ring
  map_add' u v := by funext j; simp only [Pi.add_apply]; ring
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private lemma ggQ2x_H_apply (p m : ℕ) (v : Fin m → ZMod p) (j : Fin m) :
    ggQ2x_H p m v j = ggQ2x_sgn p m j * v j := rfl

private lemma ggQ2x_H_u_fix (p m : ℕ) (i : Fin m) (hi1 : 1 ≤ (i:ℕ)) (hi3 : (i:ℕ)+3 ≤ m) :
    ggQ2x_H p m (ggDSimple p m i) = ggDSimple p m i := by
  funext j
  simp only [ggQ2x_H_apply, ggQ2x_sgn, ggDSimple]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2x_H_u_m2 (p m : ℕ) (hm : 4 ≤ m) :
    ggQ2x_H p m (ggDSimple p m ⟨m-2, by omega⟩) =
      ggDSimple p m ⟨m-1, by omega⟩ := by
  funext j
  simp only [ggQ2x_H_apply, ggQ2x_sgn, ggDSimple]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private lemma ggQ2x_H_u_m1 (p m : ℕ) (hm : 4 ≤ m) :
    ggQ2x_H p m (ggDSimple p m ⟨m-1, by omega⟩) =
      ggDSimple p m ⟨m-2, by omega⟩ := by
  funext j
  simp only [ggQ2x_H_apply, ggQ2x_sgn, ggDSimple]
  split_ifs <;> all_goals (first | (exfalso; omega) | norm_num | ring | simp)

private noncomputable def ggQ2x_Q (p m : ℕ) :
    Equiv.Perm (Fin m) →* ((Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) where
  toFun σ := LinearEquiv.funCongrLeft (ZMod p) (ZMod p) σ.symm
  map_one' := by ext v j; rfl
  map_mul' σ τ := by ext v j; rfl

private lemma ggQ2x_Q_apply (p m : ℕ) (σ : Equiv.Perm (Fin m)) (v : Fin m → ZMod p)
    (j : Fin m) : ggQ2x_Q p m σ v j = v (σ.symm j) := rfl

private lemma ggQ2x_r_eq_swap (p m : ℕ) (hm : 4 ≤ m) (i : Fin m) (hi : (i:ℕ)+1 < m) :
    ggQ2x_r p m hm i = ggQ2x_Q p m (Equiv.swap i ⟨(i:ℕ)+1, hi⟩) := by
  ext v j
  rw [ggQ2x_r_apply, ggQ2x_Q_apply, ggQ2x_dotLin_apply,
    ggQ2x_sum_ggDSimple p m i hi]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ggQ2x_eval_chain p m i hi]
  by_cases h1 : (j:ℕ) = (i:ℕ)
  · have hj : j = i := Fin.ext h1
    subst j
    have hne : ¬ (i:ℕ) = (i:ℕ)+1 := by omega
    rw [if_pos rfl, if_neg hne]
    rw [show (Equiv.swap i (⟨(i:ℕ)+1, hi⟩ : Fin m)).symm i = ⟨(i:ℕ)+1, hi⟩ from by
      rw [Equiv.symm_swap, Equiv.swap_apply_left]]
    simp
  · by_cases h2 : (j:ℕ) = (i:ℕ)+1
    · have hj : j = ⟨(i:ℕ)+1, hi⟩ := Fin.ext h2
      subst j
      have hne : ¬ (i:ℕ)+1 = (i:ℕ) := by omega
      have hne2 : ¬ (i:ℕ)+1 = (i:ℕ)+1+1 := by omega
      rw [if_neg (by omega : ¬ ((⟨(i:ℕ)+1, hi⟩ : Fin m).val = (i:ℕ))),
        if_pos rfl]
      rw [show (Equiv.swap i (⟨(i:ℕ)+1, hi⟩ : Fin m)).symm ⟨(i:ℕ)+1, hi⟩ = i from by
        rw [Equiv.symm_swap, Equiv.swap_apply_right]]
      simp
    · rw [if_neg (by exact fun h => h1 h), if_neg (by exact fun h => h2 h)]
      rw [show (Equiv.swap i (⟨(i:ℕ)+1, hi⟩ : Fin m)).symm j = j from by
        rw [Equiv.symm_swap]
        exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))]
      simp

private noncomputable def ggQ2x_Wc (p m : ℕ) (hm : 4 ≤ m) :
    Subgroup ((Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) :=
  Subgroup.closure (Set.range (ggQ2x_r p m hm))

private lemma ggQ2x_Q_mem_Wc (p m : ℕ) (hm : 4 ≤ m) (σ : Equiv.Perm (Fin m)) :
    ggQ2x_Q p m σ ∈ ggQ2x_Wc p m hm := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hle : Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) ≤
      (ggQ2x_Wc p (n+1) hm).comap (ggQ2x_Q p (n+1)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hi : (i.castSucc : Fin (n+1)).val + 1 < n + 1 := by
      simp only [Fin.val_castSucc]; omega
    change ggQ2x_Q p (n+1) (Equiv.swap i.castSucc i.succ) ∈ ggQ2x_Wc p (n+1) hm
    have hidx : i.succ = (⟨(i.castSucc : ℕ) + 1, hi⟩ : Fin (n+1)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk, Fin.val_castSucc]
    rw [hidx, ← ggQ2x_r_eq_swap p (n+1) hm i.castSucc hi]
    exact Subgroup.subset_closure ⟨i.castSucc, rfl⟩
  have htop : Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)
  have hσ : σ ∈ Subgroup.closure
      (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
    rw [htop]; exact Subgroup.mem_top σ
  exact hle hσ

private lemma ggQ2x_dotLin_fvec_left (p m : ℕ) (a : Fin m) (v : Fin m → ZMod p) :
    ggQ2x_dotLin p m (ggQ2x_fvec p m a) v = v a := by
  rw [ggQ2x_dotLin_apply, Finset.sum_eq_single a]
  · simp [ggQ2x_fvec]
  · intro b _ hb; rw [ggQ2x_fvec, Pi.single_eq_of_ne hb]; ring
  · intro h; exact absurd (Finset.mem_univ a) h

private lemma ggQ2x_dotLin_add_left (p m : ℕ) (u w v : Fin m → ZMod p) :
    ggQ2x_dotLin p m (u + w) v = ggQ2x_dotLin p m u v + ggQ2x_dotLin p m w v := by
  simp only [ggQ2x_dotLin_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => by simp only [Pi.add_apply]; ring)

private lemma ggQ2x_dotLin_sub_left (p m : ℕ) (u w v : Fin m → ZMod p) :
    ggQ2x_dotLin p m (u - w) v = ggQ2x_dotLin p m u v - ggQ2x_dotLin p m w v := by
  simp only [ggQ2x_dotLin_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun l _ => by simp only [Pi.sub_apply]; ring)

private lemma ggQ2x_dotLin_fvec_fvec (p m : ℕ) (a b : Fin m) :
    ggQ2x_dotLin p m (ggQ2x_fvec p m a) (ggQ2x_fvec p m b) =
      if a = b then (1:ZMod p) else 0 := by
  rw [ggQ2x_dotLin_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · simp [ggQ2x_fvec]
    · intro c _ hc; rw [ggQ2x_fvec, Pi.single_eq_of_ne hc]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh
  · rw [if_neg h, Finset.sum_eq_single a]
    · rw [ggQ2x_fvec, ggQ2x_fvec, Pi.single_eq_same, Pi.single_eq_of_ne h]
      ring
    · intro c _ hc; rw [ggQ2x_fvec, Pi.single_eq_of_ne hc]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh

private lemma ggQ2x_dotLin_fvec_sub (p m : ℕ) (a b : Fin m) (v : Fin m → ZMod p) :
    ggQ2x_dotLin p m (ggQ2x_fvec p m a - ggQ2x_fvec p m b) v = v a - v b := by
  rw [ggQ2x_dotLin_sub_left, ggQ2x_dotLin_fvec_left, ggQ2x_dotLin_fvec_left]

private lemma ggQ2x_dotLin_fvec_add (p m : ℕ) (a b : Fin m) (v : Fin m → ZMod p) :
    ggQ2x_dotLin p m (ggQ2x_fvec p m a + ggQ2x_fvec p m b) v = v a + v b := by
  rw [ggQ2x_dotLin_add_left, ggQ2x_dotLin_fvec_left, ggQ2x_dotLin_fvec_left]

private noncomputable def ggQ2x_s (p m : ℕ) (c : Fin m → ZMod p)
    (hc : ggQ2x_dotLin p m c c = 2) :
    (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p) :=
  Module.reflection (x := c) hc

private lemma ggQ2x_s_apply (p m : ℕ) (c : Fin m → ZMod p)
    (hc : ggQ2x_dotLin p m c c = 2) (v : Fin m → ZMod p) :
    ggQ2x_s p m c hc v = v - (ggQ2x_dotLin p m c v) • c :=
  Module.reflection_apply v hc

private lemma ggQ2x_conj_reflection (p m : ℕ)
    (P : (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p))
    (c : Fin m → ZMod p) (hc : ggQ2x_dotLin p m c c = 2)
    (hP : ∀ u v, ggQ2x_dotLin p m (P u) (P v) = ggQ2x_dotLin p m u v) :
    P * ggQ2x_s p m c hc * P.symm = ggQ2x_s p m (P c) (by rw [hP c c, hc]) := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2x_s_apply, ggQ2x_s_apply,
    map_sub, map_smul, LinearEquiv.apply_symm_apply]
  rw [← hP c (P.symm v), LinearEquiv.apply_symm_apply]

private lemma ggQ2x_Q_fvec (p m : ℕ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    ggQ2x_Q p m σ (ggQ2x_fvec p m k) = ggQ2x_fvec p m (σ k) := by
  funext j
  rw [ggQ2x_Q_apply, ggQ2x_fvec, ggQ2x_fvec]
  by_cases h : j = σ k
  · subst h; simp
  · have h' : σ.symm j ≠ k := by
      intro hh; apply h; rw [← hh]; simp
    rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

private lemma ggQ2x_Q_isom (p m : ℕ) (σ : Equiv.Perm (Fin m)) (u v : Fin m → ZMod p) :
    ggQ2x_dotLin p m (ggQ2x_Q p m σ u) (ggQ2x_Q p m σ v) = ggQ2x_dotLin p m u v := by
  simp only [ggQ2x_dotLin_apply, ggQ2x_Q_apply]
  exact Equiv.sum_comp σ.symm (fun j => u j * v j)

private lemma ggQ2x_dot_sub_self (p m : ℕ) (a b : Fin m) (hab : a ≠ b) :
    ggQ2x_dotLin p m (ggQ2x_fvec p m a - ggQ2x_fvec p m b)
      (ggQ2x_fvec p m a - ggQ2x_fvec p m b) = 2 := by
  rw [map_sub, ggQ2x_dotLin_sub_left, ggQ2x_dotLin_sub_left]
  simp only [ggQ2x_dotLin_fvec_fvec, if_true, if_false]
  rw [if_neg hab, if_neg (Ne.symm hab)]
  ring

private lemma ggQ2x_dot_add_self (p m : ℕ) (a b : Fin m) (hab : a ≠ b) :
    ggQ2x_dotLin p m (ggQ2x_fvec p m a + ggQ2x_fvec p m b)
      (ggQ2x_fvec p m a + ggQ2x_fvec p m b) = 2 := by
  rw [map_add, ggQ2x_dotLin_add_left, ggQ2x_dotLin_add_left]
  simp only [ggQ2x_dotLin_fvec_fvec, if_true, if_false]
  rw [if_neg hab, if_neg (Ne.symm hab)]
  ring

private lemma ggQ2x_dot_opp (p m : ℕ) (hm : 2 ≤ m) :
    ggQ2x_dotLin p m (ggQ2x_fvec p m ⟨0, by omega⟩ - ggQ2x_fvec p m ⟨m-1, by omega⟩)
      (ggQ2x_fvec p m ⟨0, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩) = 0 := by
  have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨m-1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [ggQ2x_dotLin_sub_left, map_add, map_add, ggQ2x_dotLin_fvec_fvec,
    ggQ2x_dotLin_fvec_fvec, ggQ2x_dotLin_fvec_fvec, ggQ2x_dotLin_fvec_fvec]
  simp only [if_true, if_false]
  rw [if_neg hne, if_neg (Ne.symm hne)]
  ring

private lemma ggQ2x_H_eq_reflections (p m : ℕ) (hm : 5 ≤ m) :
    ggQ2x_H p m =
      ggQ2x_s p m (ggQ2x_fvec p m ⟨0, by omega⟩ - ggQ2x_fvec p m ⟨m-1, by omega⟩)
        (ggQ2x_dot_sub_self p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) *
      ggQ2x_s p m (ggQ2x_fvec p m ⟨0, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
        (ggQ2x_dot_add_self p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) := by
  have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨m-1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  ext v j
  rw [ggQ2x_H_apply, LinearEquiv.mul_apply, ggQ2x_s_apply, ggQ2x_s_apply,
    ggQ2x_dotLin_fvec_add]
  have hd : ggQ2x_dotLin p m
      (ggQ2x_fvec p m ⟨0, by omega⟩ - ggQ2x_fvec p m ⟨m-1, by omega⟩)
      (v - (v ⟨0, by omega⟩ + v ⟨m-1, by omega⟩) •
        (ggQ2x_fvec p m ⟨0, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)) =
      v ⟨0, by omega⟩ - v ⟨m-1, by omega⟩ := by
    rw [map_sub, map_smul, ggQ2x_dotLin_fvec_sub, ggQ2x_dot_opp p m (by omega)]
    ring
  rw [hd]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ggQ2x_fvec, Pi.add_apply,
    Pi.single_eq_same, Pi.sub_apply]
  by_cases h0 : j = ⟨0, by omega⟩
  · subst h0
    have h' : ¬ (⟨0, by omega⟩ : Fin m) = ⟨m-1, by omega⟩ := hne
    simp [Pi.single_eq_of_ne (Ne.symm h'), h', ggQ2x_sgn]
    ring
  · by_cases h1 : j = ⟨m-1, by omega⟩
    · subst h1
      simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne (Ne.symm hne), ggQ2x_sgn]
      ring
    · have hj0 : (j:ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      have hj1 : (j:ℕ) ≠ m-1 := fun h => h1 (Fin.ext h)
      simp [Pi.single_eq_of_ne (by exact fun h => h0 h),
        Pi.single_eq_of_ne (by exact fun h => h1 h), ggQ2x_sgn, hj0, hj1]

private lemma ggQ2x_s_sub_eq_Q (p m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    ggQ2x_s p m (ggQ2x_fvec p m i - ggQ2x_fvec p m j)
      (ggQ2x_dot_sub_self p m i j hij) = ggQ2x_Q p m (Equiv.swap i j) := by
  ext v k
  rw [ggQ2x_s_apply, ggQ2x_dotLin_fvec_sub, ggQ2x_Q_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hki : k = i
  · subst k
    have hswap : (Equiv.swap i j).symm i = j := by rw [Equiv.symm_swap, Equiv.swap_apply_left]
    rw [hswap]
    rw [ggQ2x_fvec, ggQ2x_fvec, Pi.single_eq_same, Pi.single_eq_of_ne hij]
    ring
  · by_cases hkj : k = j
    · subst k
      have hswap : (Equiv.swap i j).symm j = i := by rw [Equiv.symm_swap, Equiv.swap_apply_right]
      rw [hswap]
      rw [ggQ2x_fvec, ggQ2x_fvec, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
      ring
    · have hswap : (Equiv.swap i j).symm k = k := by
        rw [Equiv.symm_swap]
        exact Equiv.swap_apply_of_ne_of_ne hki hkj
      rw [hswap]
      rw [ggQ2x_fvec, ggQ2x_fvec, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
      ring

private lemma ggQ2x_s_sub_zero_mem_Wc (p m : ℕ) (hm : 5 ≤ m) :
    ggQ2x_s p m (ggQ2x_fvec p m ⟨0, by omega⟩ - ggQ2x_fvec p m ⟨m-1, by omega⟩)
      (ggQ2x_dot_sub_self p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) ∈
      ggQ2x_Wc p m (by omega) := by
  have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨m-1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [ggQ2x_s_sub_eq_Q p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ hne]
  exact ggQ2x_Q_mem_Wc p m (by omega) _

private lemma ggQ2x_r_last_eq (p m : ℕ) (hm : 5 ≤ m) :
    ggQ2x_r p m (by omega) ⟨m-1, by omega⟩ =
      ggQ2x_s p m (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
        (ggQ2x_dot_add_self p m ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) := by
  ext v
  rw [ggQ2x_r_apply, ggQ2x_s_apply, ggQ2x_fork_rel p m (by omega) (by omega)]

private lemma ggQ2x_s_add_zero_mem_Wc (p m : ℕ) (hm : 5 ≤ m) :
    ggQ2x_s p m (ggQ2x_fvec p m ⟨0, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
      (ggQ2x_dot_add_self p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) ∈
      ggQ2x_Wc p m (by omega) := by
  let σ : Equiv.Perm (Fin m) := Equiv.swap ⟨0, by omega⟩ ⟨m-2, by omega⟩
  let P : (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p) := ggQ2x_Q p m σ
  have hPmem : P ∈ ggQ2x_Wc p m (by omega) := ggQ2x_Q_mem_Wc p m (by omega) σ
  have hrmem : ggQ2x_r p m (by omega) ⟨m-1, by omega⟩ ∈ ggQ2x_Wc p m (by omega) :=
    Subgroup.subset_closure ⟨⟨m-1, by omega⟩, rfl⟩
  have hs_mem : ggQ2x_s p m
      (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
      (ggQ2x_dot_add_self p m ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) ∈
      ggQ2x_Wc p m (by omega) := by
    rw [← ggQ2x_r_last_eq p m hm]; exact hrmem
  have hconj := ggQ2x_conj_reflection p m P
    (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
    (ggQ2x_dot_add_self p m ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega))
    (ggQ2x_Q_isom p m σ)
  have hσm2 : σ ⟨m-2, by omega⟩ = ⟨0, by omega⟩ := by
    show Equiv.swap (⟨0, by omega⟩ : Fin m) (⟨m-2, by omega⟩ : Fin m)
      (⟨m-2, by omega⟩ : Fin m) = (⟨0, by omega⟩ : Fin m)
    rw [Equiv.swap_apply_right]
  have hσm1 : σ ⟨m-1, by omega⟩ = ⟨m-1, by omega⟩ := by
    show Equiv.swap (⟨0, by omega⟩ : Fin m) (⟨m-2, by omega⟩ : Fin m)
      (⟨m-1, by omega⟩ : Fin m) = (⟨m-1, by omega⟩ : Fin m)
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro h; have := congrArg Fin.val h; simp at this; omega
  have hPc : P (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩) =
      ggQ2x_fvec p m ⟨0, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩ := by
    show ggQ2x_Q p m σ (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩) = _
    rw [map_add, ggQ2x_Q_fvec, ggQ2x_Q_fvec, hσm2, hσm1]
  have hmem : P * ggQ2x_s p m
        (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
        (ggQ2x_dot_add_self p m ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) *
      P.symm ∈ ggQ2x_Wc p m (by omega) :=
    mul_mem (mul_mem hPmem hs_mem) (inv_mem hPmem)
  have hvec : ∀ v, ggQ2x_s p m
        (ggQ2x_fvec p m ⟨0, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
        (ggQ2x_dot_add_self p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) v =
      ggQ2x_s p m (P (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩))
        (by rw [ggQ2x_Q_isom p m σ
          (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
          (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩),
          ggQ2x_dot_add_self p m ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)]) v := by
    intro v
    rw [ggQ2x_s_apply, ggQ2x_s_apply, hPc]
  have heq : ggQ2x_s p m (ggQ2x_fvec p m ⟨0, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
        (ggQ2x_dot_add_self p m ⟨0, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) =
      P * ggQ2x_s p m (ggQ2x_fvec p m ⟨m-2, by omega⟩ + ggQ2x_fvec p m ⟨m-1, by omega⟩)
        (ggQ2x_dot_add_self p m ⟨m-2, by omega⟩ ⟨m-1, by omega⟩ (by simp; omega)) * P.symm :=
    (LinearEquiv.ext hvec).trans hconj.symm
  rw [heq]
  exact hmem

private lemma ggQ2x_H_mem_Wc (p m : ℕ) (hm : 5 ≤ m) :
    ggQ2x_H p m ∈ ggQ2x_Wc p m (by omega) := by
  rw [ggQ2x_H_eq_reflections p m hm]
  exact mul_mem (ggQ2x_s_sub_zero_mem_Wc p m hm) (ggQ2x_s_add_zero_mem_Wc p m hm)

private noncomputable def ggQ2x_conj {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p)) :
    (D.V ≃ₗ[ZMod p] D.V) ≃* ((Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) where
  toFun g := τ.symm.trans (g.trans τ)
  invFun k := τ.trans (k.trans τ.symm)
  left_inv g := by ext x; simp [LinearEquiv.trans_apply]
  right_inv k := by ext y; simp [LinearEquiv.trans_apply]
  map_mul' g h := by ext y; simp [LinearEquiv.mul_apply, LinearEquiv.trans_apply]

private lemma ggQ2x_conj_simpleRefl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (hm : 4 ≤ m) (e : Fin m ≃ D.ι) (τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p))
    (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple p m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple p m i j * τ v j)
    (i : Fin m) :
    ggQ2x_conj D τ (D.simpleRefl (e i)) = ggQ2x_r p m hm i := by
  apply LinearEquiv.ext
  intro y
  change τ (D.simpleRefl (e i) (τ.symm y)) = ggQ2x_r p m hm i y
  rw [ggQ2x_r_apply, ggQ2x_dotLin_apply]
  have hsr : D.simpleRefl (e i) (τ.symm y) =
      τ.symm y - (D.root (e i) (τ.symm y)) • D.coroot (e i) := by
    rw [show D.simpleRefl (e i) = Module.reflection (D.root_coroot_self (e i)) from rfl,
      Module.reflection_apply]
  rw [hsr, map_sub, map_smul, LinearEquiv.apply_symm_apply, hτ i, hroot i (τ.symm y),
    LinearEquiv.apply_symm_apply]
  rfl

private lemma ggQ2x_weylMap {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {m : ℕ}
    (hm : 4 ≤ m) (e : Fin m ≃ D.ι) (τ : D.V ≃ₗ[ZMod p] (Fin m → ZMod p))
    (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple p m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple p m i j * τ v j) :
    (D.weyl).map (ggQ2x_conj D τ).toMonoidHom = ggQ2x_Wc p m hm := by
  rw [GGQ2Lin.weyl, GGQ2Lin.parab, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, -, rfl⟩, rfl⟩
    obtain ⟨i, rfl⟩ := e.surjective k
    exact ⟨i, (ggQ2x_conj_simpleRefl D hm e τ hτ hroot i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨D.simpleRefl (e i), ⟨e i, Set.mem_univ _, rfl⟩,
      ggQ2x_conj_simpleRefl D hm e τ hτ hroot i⟩

private lemma ggQ2x_tau_x_zero (p m : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hm : 5 ≤ m)
    (w : Fin m → ZMod p)
    (hw : ∀ i : Fin m, (i:ℕ) ≠ 0 → ∑ j, ggDSimple p m i j * w j = 0) :
    ∀ j : Fin m, 1 ≤ (j:ℕ) → (j:ℕ) ≤ m-1 → w j = 0 := by
  have hchain : ∀ (i : Fin m) (hi : (i:ℕ)+1 < m), (i:ℕ) ≠ 0 → w i = w ⟨(i:ℕ)+1, hi⟩ := by
    intro i hi hi0
    have h := hw i hi0
    rw [ggQ2x_sum_ggDSimple p m i hi] at h
    exact sub_eq_zero.mp h
  have hfork : ∀ (i : Fin m) (hi : ¬ (i:ℕ)+1 < m),
      w ⟨m-2, by omega⟩ + w ⟨m-1, by omega⟩ = 0 := by
    intro i hi
    have h := hw i (by omega)
    rw [ggQ2x_sum_ggDSimple_fork p m (by omega) i hi] at h
    exact h
  have hm2 : m - 2 < m := by omega
  have hm1 : m - 1 < m := by omega
  have hi2 : (⟨m-2, hm2⟩ : Fin m).val + 1 < m := by simp only [Fin.val_mk]; omega
  have hi20 : (⟨m-2, hm2⟩ : Fin m).val ≠ 0 := by simp only [Fin.val_mk]; omega
  have hstep : w ⟨m-2, hm2⟩ = w ⟨m-1, hm1⟩ := by
    have h := hchain ⟨m-2, hm2⟩ hi2 hi20
    rwa [show (⟨(⟨m-2, hm2⟩ : Fin m).val + 1, hi2⟩ : Fin m) = ⟨m-1, hm1⟩ from by
      apply Fin.ext; simp only [Fin.val_mk]; omega] at h
  have hfr : w ⟨m-2, hm2⟩ + w ⟨m-1, hm1⟩ = 0 := hfork ⟨m-1, hm1⟩ (by simp; omega)
  have hw2 : w ⟨m-2, hm2⟩ = 0 := by
    have h2 : (2:ZMod p) * w ⟨m-2, hm2⟩ = 0 := by
      have : (2:ZMod p) * w ⟨m-2, hm2⟩ = w ⟨m-2, hm2⟩ + w ⟨m-1, hm1⟩ := by
        rw [← hstep]; ring
      rw [this, hfr]
    exact (mul_eq_zero.mp h2).resolve_left (zmod_two_ne_zero hp2)
  have key : ∀ n, ∀ j : Fin m, 1 ≤ (j:ℕ) → (j:ℕ) + n = m-2 → w j = w ⟨m-2, hm2⟩ := by
    intro n
    induction n with
    | zero =>
      intro j hj hjn
      have : (j:ℕ) = m-2 := by omega
      rw [show j = ⟨m-2, hm2⟩ from Fin.ext this]
    | succ n ih =>
      intro j hj hjn
      have hjm : (j:ℕ) < m-2 := by omega
      have hj1m : (j:ℕ)+1 < m := by omega
      have hnext : (j:ℕ)+1 + n = m-2 := by omega
      rw [hchain j hj1m (by omega)]
      exact ih ⟨(j:ℕ)+1, hj1m⟩ (by simp only [Fin.val_mk]; omega) hnext
  intro j hj1 hjm
  by_cases hj : (j:ℕ) ≤ m-2
  · rw [key (m-2 - (j:ℕ)) j hj1 (by omega), hw2]
  · have hjm1 : (j:ℕ) = m-1 := by omega
    rw [show j = ⟨m-1, hm1⟩ from Fin.ext hjm1, ← hstep, hw2]

theorem ggQ2_D_swap_element {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (D : GGQ2Lin p) (hbas : D.Basis)
    {m : ℕ} (hm : 5 ≤ m) (e : Fin m ≃ D.ι)
    (he : D.coxeter = (ggCoxeterMatrixD m).reindex e) (ha : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {x}) :
    ∃ h ∈ D.weyl, h x = -x ∧
      (∀ i : Fin m, 1 ≤ (i : ℕ) → (i : ℕ) + 3 ≤ m → h (D.coroot (e i)) = D.coroot (e i)) ∧
      h (D.coroot (e ⟨m - 2, by omega⟩)) = D.coroot (e ⟨m - 1, by omega⟩) ∧
      h (D.coroot (e ⟨m - 1, by omega⟩)) = D.coroot (e ⟨m - 2, by omega⟩) := by
  obtain ⟨τ, hτ, hroot⟩ := ggQ2_D_coordinates hp2 D hbas (by omega) e he
  have hHmem : ggQ2x_H p m ∈ ggQ2x_Wc p m (by omega) := ggQ2x_H_mem_Wc p m hm
  have hT := ggQ2x_weylMap D (by omega) e τ hτ hroot
  have hmap : ggQ2x_H p m ∈ (D.weyl).map (ggQ2x_conj D τ).toMonoidHom := by
    rw [hT]; exact hHmem
  obtain ⟨h, hh, hhH⟩ := Subgroup.mem_map.mp hmap
  have hcoe : ∀ y, τ (h (τ.symm y)) = ggQ2x_H p m y := by
    intro y
    have hpt := congrArg (fun (f : (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) => f y) hhH
    change ((ggQ2x_conj D τ) h) y = (ggQ2x_H p m) y at hpt
    change τ (h (τ.symm y)) = (ggQ2x_H p m) y
    exact hpt
  have hcor : ∀ i, τ (h (D.coroot (e i))) = ggQ2x_H p m (ggDSimple p m i) := by
    intro i
    have := hcoe (τ (D.coroot (e i)))
    rwa [LinearEquiv.symm_apply_apply, hτ i] at this
  have hxfix : ∀ i : Fin m, (i:ℕ) ≠ 0 → D.simpleRefl (e i) x = x := by
    intro i hi
    have hi0 : i ≠ ⟨0, by omega⟩ := by intro h; exact hi (by rw [h])
    have hmem1 : e i ≠ D.a := by rw [ha]; exact fun h => hi0 (e.injective h)
    have hmem : D.simpleRefl (e i) ∈ D.parab {k | k ≠ D.a} :=
      Subgroup.subset_closure ⟨e i, hmem1, rfl⟩
    exact ((hx x).mpr (Submodule.subset_span (Set.mem_singleton x)))
      (D.simpleRefl (e i)) hmem
  have hw : ∀ i : Fin m, (i:ℕ) ≠ 0 → ∑ j, ggDSimple p m i j * τ x j = 0 := by
    intro i hi
    have hfix := hxfix i hi
    have hroot0 : D.root (e i) x = 0 := by
      rw [show D.simpleRefl (e i) = Module.reflection (D.root_coroot_self (e i)) from rfl,
        Module.reflection_apply] at hfix
      exact (smul_eq_zero.mp (sub_eq_self.mp hfix)).resolve_right (hbas.1.ne_zero (e i))
    rw [hroot i x] at hroot0
    exact hroot0
  have hz := ggQ2x_tau_x_zero p m hp2 hm (τ x) hw
  have hHτx : ggQ2x_H p m (τ x) = - τ x := by
    funext j
    rw [ggQ2x_H_apply, Pi.neg_apply]
    by_cases hj0 : (j:ℕ) = 0
    · rw [ggQ2x_sgn, if_pos (Or.inl hj0)]
      exact neg_one_mul _
    · by_cases hjm : (j:ℕ) = m-1
      · rw [ggQ2x_sgn, if_pos (Or.inr hjm)]
        exact neg_one_mul _
      · have hj1 : 1 ≤ (j:ℕ) := by omega
        have hjm' : (j:ℕ) ≤ m-1 := by omega
        have hzj : (τ x) j = 0 := hz j hj1 hjm'
        have hsgn : ggQ2x_sgn p m j = 1 := by
          rw [ggQ2x_sgn, if_neg]; simp [hj0, hjm]
        rw [hsgn, hzj]
        exact (one_mul 0).trans neg_zero.symm
  have hxh : h x = -x := by
    apply τ.injective
    have := hcoe (τ x)
    rw [LinearEquiv.symm_apply_apply, hHτx] at this
    rw [this, map_neg]
  refine ⟨h, hh, hxh, ?_, ?_, ?_⟩
  · intro i hi1 hi3
    apply τ.injective
    rw [hcor i, ggQ2x_H_u_fix p m i hi1 hi3, hτ i]
  · apply τ.injective
    rw [hcor ⟨m-2, by omega⟩, ggQ2x_H_u_m2 p m (by omega), hτ ⟨m-1, by omega⟩]
  · apply τ.injective
    rw [hcor ⟨m-1, by omega⟩, ggQ2x_H_u_m1 p m (by omega), hτ ⟨m-2, by omega⟩]

end CFSG.StandardType

end
