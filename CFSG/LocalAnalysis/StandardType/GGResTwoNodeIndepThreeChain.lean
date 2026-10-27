module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverPair
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepThreeLin
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepThreeRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l6p3_f (a b : ℕ) : ZMod 3 :=
  if a = b then 2 else if a + 1 = b ∨ b + 1 = a then -1 else 0

private lemma l6p3_A_eq_f {m : ℕ} (l l' : Fin m) :
    (CartanMatrix.A m l l' : ZMod 3) = l6p3_f l.val l'.val := by
  simp only [CartanMatrix.A, Matrix.of_apply, l6p3_f, Fin.ext_iff]
  split_ifs <;> simp

private lemma l6p3_f_row {a k : ℕ} (ha : a < k) :
    l6p3_f a k = if a = k - 1 then -1 else 0 := by
  unfold l6p3_f
  rw [if_neg (by omega : ¬ a = k)]
  by_cases h : a = k - 1
  · rw [if_pos (Or.inl (by omega : a + 1 = k)), if_pos h]
  · rw [if_neg (by omega : ¬ (a + 1 = k ∨ k + 1 = a)), if_neg h]

private lemma l6p3_f_col {k b : ℕ} (hb : b < k) :
    l6p3_f k b = if b = k - 1 then -1 else 0 := by
  unfold l6p3_f
  rw [if_neg (by omega : ¬ k = b)]
  by_cases h : b = k - 1
  · rw [if_pos (Or.inr (by omega : b + 1 = k)), if_pos h]
  · rw [if_neg (by omega : ¬ (k + 1 = b ∨ b + 1 = k)), if_neg h]

private lemma l6p3_sum_row (i k : ℕ) (hik : i < k) :
    (∑ a ∈ Finset.Ico i k, l6p3_f a k) = -1 := by
  have hmem : k - 1 ∈ Finset.Ico i k := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  trans l6p3_f (k - 1) k
  · refine Finset.sum_eq_single (k - 1) ?_ ?_
    · intro b hb hne
      rw [l6p3_f_row (Finset.mem_Ico.mp hb).2, if_neg hne]
    · intro hnot
      exact absurd hmem hnot
  · rw [l6p3_f_row (by omega : k - 1 < k), if_pos rfl]

private lemma l6p3_sum_col (i k : ℕ) (hik : i < k) :
    (∑ b ∈ Finset.Ico i k, l6p3_f k b) = -1 := by
  have hmem : k - 1 ∈ Finset.Ico i k := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  trans l6p3_f k (k - 1)
  · refine Finset.sum_eq_single (k - 1) ?_ ?_
    · intro b hb hne
      rw [l6p3_f_col (Finset.mem_Ico.mp hb).2, if_neg hne]
    · intro hnot
      exact absurd hmem hnot
  · rw [l6p3_f_col (by omega : k - 1 < k), if_pos rfl]

private lemma l6p3_interval_step (i j : ℕ) (hij : i < j) :
    (∑ a ∈ Finset.Ico i (j + 1), ∑ b ∈ Finset.Ico i (j + 1), l6p3_f a b)
      = (∑ a ∈ Finset.Ico i j, ∑ b ∈ Finset.Ico i j, l6p3_f a b) := by
  have hij' : i ≤ j := by omega
  have hinner : ∀ a, (∑ b ∈ Finset.Ico i (j + 1), l6p3_f a b)
      = (∑ b ∈ Finset.Ico i j, l6p3_f a b) + l6p3_f a j := fun a =>
    Finset.sum_Ico_succ_top hij' (fun b => l6p3_f a b)
  rw [Finset.sum_Ico_succ_top hij'
    (fun a => ∑ b ∈ Finset.Ico i (j + 1), l6p3_f a b)]
  simp_rw [hinner]
  rw [Finset.sum_add_distrib]
  rw [l6p3_sum_row i j hij, l6p3_sum_col i j hij]
  have hjj : l6p3_f j j = 2 := by unfold l6p3_f; simp
  rw [hjj]
  ring

private lemma l6p3_interval (i j : ℕ) (hij : i < j) :
    (∑ a ∈ Finset.Ico i j, ∑ b ∈ Finset.Ico i j, l6p3_f a b) = 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, j = i + 1 + n := ⟨j - (i + 1), by omega⟩
  clear hij
  induction n with
  | zero =>
      simp only [Nat.add_zero]
      rw [Finset.sum_Ico_succ_top (le_refl i)
        (fun a => ∑ b ∈ Finset.Ico i (i + 1), l6p3_f a b)]
      simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
      rw [Finset.sum_Ico_succ_top (le_refl i) (fun b => l6p3_f i b)]
      simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
      unfold l6p3_f; simp
  | succ n ih =>
      rw [show i + 1 + (n + 1) = (i + 1 + n) + 1 by omega]
      rw [l6p3_interval_step i (i + 1 + n) (by omega)]
      exact ih

private lemma l6p3_sum_filter_Ico {m : ℕ} (i j : ℕ) (hjm : j ≤ m) (g : ℕ → ZMod 3) :
    (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), g l.val)
      = ∑ k ∈ Finset.Ico i j, g k := by
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun k => if i ≤ k ∧ k < j then g k else 0) m]
  have hf : ∀ k, (if i ≤ k ∧ k < j then g k else 0)
      = if k ∈ Finset.Ico i j then g k else 0 := by
    intro k; simp only [Finset.mem_Ico]
  simp_rw [hf]
  rw [← Finset.sum_filter]
  have hset : (Finset.range m).filter (fun k => k ∈ Finset.Ico i j) = Finset.Ico i j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset]

private theorem l6p3_CLL {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod 3))
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (r : Fin m → (V ≃ₗ[ZMod 3] V)) (hr : ∀ l w, r l w = w - αv l w • hv l) (hrA : ∀ l, r l ∈ A)
    (t : V ≃ₗ[ZMod 3] V) (htA : t ∈ A) (ht : V) (αt : Module.Dual (ZMod 3) V)
    (htl : ∀ w, t w = w - αt w • ht) (hαt : αt ht = 2) :
    ∀ i j : ℕ, i < j → j ≤ m →
      ((∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), αv l) ht = 0 ↔
        αt (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), hv l) = 0) := by
  intro i j hij hjm
  obtain ⟨sr, hsr_closure, hsr_form⟩ := ggChain_rootRefl_mem hv αv hpair r hr i j hij hjm
  have hsrA : sr ∈ A := by
    have hle : Subgroup.closure (Set.range r) ≤ A :=
      (Subgroup.closure_le A).mpr (by rintro x ⟨l, rfl⟩; exact hrA l)
    exact hle hsr_closure
  have hαs : (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j), αv l)
        (∑ l' ∈ Finset.univ.filter (fun l' : Fin m => i ≤ l'.val ∧ l'.val < j), hv l') = 2 := by
    rw [LinearMap.sum_apply]
    simp_rw [map_sum]
    simp_rw [hpair]
    simp_rw [l6p3_A_eq_f]
    have h1 : (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j),
          ∑ l' ∈ Finset.univ.filter (fun l' : Fin m => i ≤ l'.val ∧ l'.val < j),
            l6p3_f l.val l'.val)
        = ∑ a ∈ Finset.Ico i j, ∑ b ∈ Finset.Ico i j, l6p3_f a b := by
      have hstep : (∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j),
            ∑ l' ∈ Finset.univ.filter (fun l' : Fin m => i ≤ l'.val ∧ l'.val < j),
              l6p3_f l.val l'.val)
          = ∑ l ∈ Finset.univ.filter (fun l : Fin m => i ≤ l.val ∧ l.val < j),
              (fun a => ∑ b ∈ Finset.Ico i j, l6p3_f a b) l.val := by
        refine Finset.sum_congr rfl ?_
        intro l _
        exact l6p3_sum_filter_Ico i j hjm (fun b => l6p3_f l.val b)
      rw [hstep, l6p3_sum_filter_Ico i j hjm (fun a => ∑ b ∈ Finset.Ico i j, l6p3_f a b)]
    rw [h1, l6p3_interval i j hij]
  constructor
  · intro h0
    exact ggDepA_pair_zero_symm (p := 3) (by norm_num) A hnt hsrA htA hsr_form htl hαs hαt h0
  · intro h0
    exact ggDepA_pair_zero_symm (p := 3) (by norm_num) A hnt htA hsrA htl hsr_form hαt hαs h0

theorem ggIndep_p3_fixes_x {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod 3) V) (c : Fin m → ZMod 3)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod 3))
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (r : Fin m → (V ≃ₗ[ZMod 3] V)) (hr : ∀ l w, r l w = w - αv l w • hv l) (hrA : ∀ l, r l ∈ A)
    (t : V ≃ₗ[ZMod 3] V) (htA : t ∈ A) (ht : V) (αt : Module.Dual (ZMod 3) V)
    (hcα : (∑ i, c i • αv i) ht = 0)
    (htl : ∀ w, t w = w - αt w • ht) (hαt : αt ht = 2) : αt (∑ i, c i • hv i) = 0 :=
  ggIndep_p3_refl_fixes_x hv αv c hpair ht αt hcα
    (l6p3_CLL hv αv hpair A hnt r hr hrA t htA ht αt htl hαt)

theorem ggIndep_p3_affine {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (hv : Fin m → V) (αv : Fin m → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, αv i (hv j) = (CartanMatrix.A m i j : ZMod 3))
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (r : Fin m → (V ≃ₗ[ZMod 3] V)) (hr : ∀ l w, r l w = w - αv l w • hv l) (hrA : ∀ l, r l ∈ A)
    (t : V ≃ₗ[ZMod 3] V) (htA : t ∈ A) (ht : V) (αt : Module.Dual (ZMod 3) V)
    (htl : ∀ w, t w = w - αt w • ht) (hαt : αt ht = 2) :
    ∃ κ : ZMod 3, ∀ l, αt (hv l) = κ * αv l ht :=
  ggIndep_p3_refl_affine hv αv ht αt (l6p3_CLL hv αv hpair A hnt r hr hrA t htA ht αt htl hαt)

end CFSG.StandardType

end
