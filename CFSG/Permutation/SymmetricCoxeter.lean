module

public import Mathlib.GroupTheory.Perm.Sign
public import CFSG.Permutation.Embedding
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Permutation.SymmetricCoxeter

open Equiv Equiv.Perm

structure IsCoxeterA {Γ : Type*} [Group Γ] (n : ℕ) (g : ℕ → Γ) : Prop where
  sq : ∀ i < n, g i * g i = 1
  braid : ∀ i, i + 1 < n → g i * g (i + 1) * g i = g (i + 1) * g i * g (i + 1)
  comm : ∀ i j, i + 2 ≤ j → j < n → g i * g j = g j * g i

variable {Γ : Type*} [Group Γ]

theorem IsCoxeterA.shift {n : ℕ} {g : ℕ → Γ} (h : IsCoxeterA (n + 1) g) :
    IsCoxeterA n (fun i => g (i + 1)) :=
  ⟨fun i hi => h.sq (i + 1) (by omega), fun i hi => h.braid (i + 1) (by omega),
    fun i j hij hj => h.comm (i + 1) (j + 1) (by omega) (by omega)⟩

theorem IsCoxeterA.map {K : Type*} [Group K] (f : Γ →* K) {n : ℕ} {g : ℕ → Γ}
    (hg : IsCoxeterA n g) : IsCoxeterA n (fun i => f (g i)) :=
  ⟨fun i hi => by rw [← map_mul, hg.sq i hi, map_one],
    fun i hi => by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hg.braid i hi],
    fun i j hij hj => by rw [← map_mul, ← map_mul, hg.comm i j hij hj]⟩

@[expose] def snoc {β : Type*} (n : ℕ) (x : ℕ → β) (y : β) : ℕ → β :=
  fun i => if i < n then x i else y

theorem snoc_of_lt {β : Type*} {n : ℕ} {x : ℕ → β} {y : β} {i : ℕ} (h : i < n) :
    snoc n x y i = x i := by
  simp [snoc, h]

theorem snoc_self {β : Type*} {n : ℕ} {x : ℕ → β} {y : β} : snoc n x y n = y := by
  simp [snoc]

theorem IsCoxeterA.snoc {n : ℕ} {x : ℕ → Γ} (hx : IsCoxeterA n x) {y : Γ} (hy : y * y = 1)
    (hbraid : 1 ≤ n → x (n - 1) * y * x (n - 1) = y * x (n - 1) * y)
    (hcomm : ∀ i, i + 2 ≤ n → x i * y = y * x i) : IsCoxeterA (n + 1) (snoc n x y) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
  · by_cases h : i < n
    · rw [snoc_of_lt h]
      exact hx.sq i h
    · obtain rfl : i = n := by omega
      rw [snoc_self]
      exact hy
  · by_cases h : i + 1 < n
    · rw [snoc_of_lt h, snoc_of_lt (by omega : i < n)]
      exact hx.braid i h
    · obtain rfl : i = n - 1 := by omega
      have hn : 1 ≤ n := by omega
      rw [snoc_of_lt (by omega : n - 1 < n), show n - 1 + 1 = n by omega, snoc_self]
      exact hbraid hn
  · by_cases h : j < n
    · rw [snoc_of_lt h, snoc_of_lt (by omega : i < n)]
      exact hx.comm i j hij h
    · obtain rfl : j = n := by omega
      rw [snoc_of_lt (by omega : i < j), snoc_self]
      exact hcomm i hij

@[expose] def cosetRep (g : ℕ → Γ) : ℕ → Γ
  | 0 => 1
  | k + 1 => cosetRep g k * g k

section Rep

variable {n : ℕ} {g : ℕ → Γ}

theorem cosetRep_succ_mul (h : IsCoxeterA n g) {k : ℕ} (hk : k < n) :
    cosetRep g (k + 1) * g k = cosetRep g k := by
  rw [cosetRep, mul_assoc, h.sq k hk, mul_one]

theorem cosetRep_mul_comm (h : IsCoxeterA n g) {k j : ℕ} (hkj : k + 1 ≤ j) (hj : j < n) :
    cosetRep g k * g j = g j * cosetRep g k := by
  induction k with
  | zero => rw [cosetRep, one_mul, mul_one]
  | succ k ih =>
    calc cosetRep g (k + 1) * g j = cosetRep g k * (g k * g j) := by rw [cosetRep, mul_assoc]
      _ = cosetRep g k * (g j * g k) := by rw [h.comm k j (by omega) hj]
      _ = (cosetRep g k * g j) * g k := by rw [mul_assoc]
      _ = (g j * cosetRep g k) * g k := by rw [ih (by omega)]
      _ = g j * cosetRep g (k + 1) := by rw [cosetRep, mul_assoc]

theorem cosetRep_mul_shift (h : IsCoxeterA n g) {k i : ℕ} (hik : i + 2 ≤ k) (hk : k ≤ n) :
    cosetRep g k * g i = g (i + 1) * cosetRep g k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk2 : i + 2 = k + 1
    · obtain rfl : k = i + 1 := by omega
      have hc := cosetRep_mul_comm h (k := i) (j := i + 1) (le_refl _) (by omega)
      calc cosetRep g (i + 1 + 1) * g i
          = cosetRep g i * (g i * g (i + 1) * g i) := by
            simp only [cosetRep, mul_assoc]
        _ = cosetRep g i * (g (i + 1) * g i * g (i + 1)) := by rw [h.braid i (by omega)]
        _ = (cosetRep g i * g (i + 1)) * g i * g (i + 1) := by simp only [mul_assoc]
        _ = (g (i + 1) * cosetRep g i) * g i * g (i + 1) := by rw [hc]
        _ = g (i + 1) * cosetRep g (i + 1 + 1) := by simp only [cosetRep, mul_assoc]
    · have hik' : i + 2 ≤ k := by omega
      calc cosetRep g (k + 1) * g i = cosetRep g k * (g k * g i) := by rw [cosetRep, mul_assoc]
        _ = cosetRep g k * (g i * g k) := by rw [h.comm i k hik' (by omega)]
        _ = (cosetRep g k * g i) * g k := by rw [mul_assoc]
        _ = (g (i + 1) * cosetRep g k) * g k := by rw [ih hik' (by omega)]
        _ = g (i + 1) * cosetRep g (k + 1) := by rw [cosetRep, mul_assoc]

end Rep

theorem finite_closure_and_card_le : ∀ (n : ℕ) (g : ℕ → Γ), IsCoxeterA n g →
    Finite (Subgroup.closure (g '' Set.Iio n)) ∧
      Nat.card (Subgroup.closure (g '' Set.Iio n)) ≤ (n + 1).factorial := by
  intro n
  induction n with
  | zero =>
    intro g _
    have h0 : g '' Set.Iio 0 = ∅ := by ext; simp
    rw [h0, Subgroup.closure_empty]
    exact ⟨inferInstance, by simp⟩
  | succ n ih =>
    intro g hg
    obtain ⟨hfin, hcard⟩ := ih (fun i => g (i + 1)) hg.shift
    set H' := Subgroup.closure ((fun i => g (i + 1)) '' Set.Iio n) with hH'
    set Hn := Subgroup.closure (g '' Set.Iio (n + 1)) with hHn
    have hle : H' ≤ Hn := Subgroup.closure_mono (by
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨i + 1, by simpa using hi, rfl⟩)
    have hgi : ∀ i, i < n + 1 → g i ∈ Hn := fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩
    have hrep : ∀ k, k ≤ n + 1 → cosetRep g k ∈ Hn := by
      intro k
      induction k with
      | zero => intro _; exact Subgroup.one_mem _
      | succ k ihk => intro hk; exact Subgroup.mul_mem _ (ihk (by omega)) (hgi k (by omega))
    have hg' : ∀ i, 1 ≤ i → i < n + 1 → g i ∈ H' := by
      intro i h1 h2
      refine Subgroup.subset_closure ⟨i - 1, by simpa using (by omega : i - 1 < n), ?_⟩
      simp only [Nat.sub_add_cancel h1]
    have hstep : ∀ i, i < n + 1 → ∀ k, k ≤ n + 1 → ∀ h ∈ H',
        ∃ k', k' ≤ n + 1 ∧ ∃ h' ∈ H', h * cosetRep g k * g i = h' * cosetRep g k' := by
      intro i hi k hk h hh
      rcases (by omega : i + 2 ≤ k ∨ i + 1 = k ∨ i = k ∨ k + 1 ≤ i) with hik | hik | hik | hik
      · refine ⟨k, hk, h * g (i + 1), H'.mul_mem hh (hg' (i + 1) (by omega) (by omega)), ?_⟩
        rw [mul_assoc, cosetRep_mul_shift hg hik hk, ← mul_assoc]
      · subst hik
        exact ⟨i, by omega, h, hh, by rw [mul_assoc, cosetRep_succ_mul hg hi]⟩
      · subst hik
        exact ⟨i + 1, by omega, h, hh, by rw [mul_assoc]; rfl⟩
      · refine ⟨k, hk, h * g i, H'.mul_mem hh (hg' i (by omega) hi), ?_⟩
        rw [mul_assoc, cosetRep_mul_comm hg hik hi, ← mul_assoc]
    have hcov : ∀ x ∈ Hn, ∃ k, k ≤ n + 1 ∧ ∃ h ∈ H', x = h * cosetRep g k := by
      intro x hx
      induction hx using Subgroup.closure_induction_right with
      | one => exact ⟨0, by omega, 1, H'.one_mem, by simp [cosetRep]⟩
      | mul_right x hx y hy ih =>
        obtain ⟨k, hk, h, hh, rfl⟩ := ih
        obtain ⟨i, hi, rfl⟩ := hy
        exact hstep i (by simpa using hi) k hk h hh
      | mul_inv_cancel x hx y hy ih =>
        obtain ⟨k, hk, h, hh, rfl⟩ := ih
        obtain ⟨i, hi, rfl⟩ := hy
        have hi' : i < n + 1 := by simpa using hi
        rw [inv_eq_of_mul_eq_one_right (hg.sq i hi')]
        exact hstep i hi' k hk h hh
    have : Finite H' := hfin
    let f : Fin (n + 2) × H' → Hn := fun p =>
      ⟨p.2 * cosetRep g p.1, Subgroup.mul_mem _ (hle p.2.2) (hrep p.1 (by omega))⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk, h, hh, rfl⟩ := hcov x hx
      exact ⟨(⟨k, by omega⟩, ⟨h, hh⟩), rfl⟩
    refine ⟨Finite.of_surjective f hf, ?_⟩
    have hc := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (n + 2)), Fintype.card_fin] at hc
    calc Nat.card Hn ≤ (n + 2) * Nat.card H' := hc
      _ ≤ (n + 2) * (n + 1).factorial := Nat.mul_le_mul_left _ hcard
      _ = (n + 1 + 1).factorial := (Nat.factorial_succ (n + 1)).symm

section Swap

variable {α : Type*} [DecidableEq α]

theorem swap_braid {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    swap a b * swap b c * swap a b = swap b c * swap a b * swap b c := by
  have hL := swap_mul_swap_mul_swap (x := c) (y := b) (z := a) hbc.symm hac.symm
  have hR := swap_mul_swap_mul_swap (x := a) (y := b) (z := c) hab hac
  rw [swap_comm b a, swap_comm c b] at hL
  rw [hL, hR, swap_comm c a]

theorem swap_mul_swap_comm {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  have h := swap_apply_apply (swap a b) c d
  rw [swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_of_ne_of_ne had.symm hbd.symm,
    swap_inv] at h
  conv_rhs => rw [h]
  exact (mul_swap_mul_self _ _ _).symm

end Swap

@[expose] def adjSwap (n i : ℕ) : Perm (Fin (n + 1)) :=
  if h : i < n then swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩ else 1

theorem adjSwap_of_lt {n i : ℕ} (h : i < n) :
    adjSwap n i = swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
  simp [adjSwap, h]

theorem viaEmbeddingHom_castSuccEmb_adjSwap (n i : ℕ) (h : i < n) :
    viaEmbeddingHom (Fin.castSuccEmb : Fin (n + 1) ↪ Fin (n + 2)) (adjSwap n i) =
      adjSwap (n + 1) i := by
  rw [adjSwap_of_lt h, adjSwap_of_lt (by omega), viaEmbeddingHom_swap]
  rfl

theorem viaEmbeddingHom_succEmb_adjSwap (n i : ℕ) (h : i < n) :
    viaEmbeddingHom (Fin.succEmb (n + 1)) (adjSwap n i) = adjSwap (n + 1) (i + 1) := by
  rw [adjSwap_of_lt h, adjSwap_of_lt (by omega), viaEmbeddingHom_swap]
  rfl

theorem isCoxeterA_adjSwap (n : ℕ) : IsCoxeterA n (adjSwap n) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
  · rw [adjSwap_of_lt hi, swap_mul_self]
  · rw [adjSwap_of_lt (by omega : i < n), adjSwap_of_lt hi]
    exact swap_braid (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff])
  · rw [adjSwap_of_lt (by omega : i < n), adjSwap_of_lt hj]
    exact swap_mul_swap_comm (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

theorem closure_adjSwap (n : ℕ) : Subgroup.closure (adjSwap n '' Set.Iio n) = ⊤ := by
  have h : adjSwap n '' Set.Iio n = Set.range fun i : Fin n => swap i.castSucc i.succ := by
    ext σ
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i < n := hi
      exact ⟨⟨i, hi'⟩, by rw [adjSwap_of_lt hi']; rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, by rw [adjSwap_of_lt i.2]; rfl⟩
  rw [h]
  exact Subgroup.closure_eq_top_of_mclosure_eq_top (mclosure_swap_castSucc_succ n)

theorem exists_hom_perm {H : Type*} [Group H] (n : ℕ) (x : ℕ → H) (hx : IsCoxeterA n x) :
    ∃ ψ : Perm (Fin (n + 1)) →* H, ∀ i, i < n → ψ (adjSwap n i) = x i := by
  let γ : ℕ → Perm (Fin (n + 1)) × H := fun i => (adjSwap n i, x i)
  have hγ : IsCoxeterA n γ := by
    obtain ⟨h1, h2, h3⟩ := isCoxeterA_adjSwap n
    exact ⟨fun i hi => Prod.ext (h1 i hi) (hx.sq i hi),
      fun i hi => Prod.ext (h2 i hi) (hx.braid i hi),
      fun i j hij hj => Prod.ext (h3 i j hij hj) (hx.comm i j hij hj)⟩
  obtain ⟨hfin, hcard⟩ := finite_closure_and_card_le n γ hγ
  set K := Subgroup.closure (γ '' Set.Iio n) with hK
  let p : K →* Perm (Fin (n + 1)) := (MonoidHom.fst _ _).comp K.subtype
  have hp : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_adjSwap n, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨⟨γ i, Subgroup.subset_closure ⟨i, hi, rfl⟩⟩, rfl⟩
  have : Finite K := hfin
  have hbij : Function.Bijective p := by
    refine hp.bijective_of_nat_card_le ?_
    rw [Nat.card_eq_fintype_card (α := Perm (Fin (n + 1))), Fintype.card_perm, Fintype.card_fin]
    exact hcard
  let E : K ≃* Perm (Fin (n + 1)) := MulEquiv.ofBijective p hbij
  refine ⟨(MonoidHom.snd _ _).comp (K.subtype.comp E.symm.toMonoidHom), fun i hi => ?_⟩
  have hE : E.symm (adjSwap n i) = ⟨γ i, Subgroup.subset_closure ⟨i, hi, rfl⟩⟩ :=
    E.symm_apply_eq.2 rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hE]
  rfl

theorem exists_hom_perm_of_overlap {H : Type*} [Group H] (m : ℕ)
    (f g : Perm (Fin (m + 3)) →* H)
    (hOverlap : f.comp (viaEmbeddingHom (Fin.succEmb (m + 2))) =
      g.comp (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 2) ↪ Fin (m + 3))))
    (hCross : Commute (f (adjSwap (m + 2) 0)) (g (adjSwap (m + 2) (m + 1)))) :
    ∃ F : Perm (Fin (m + 4)) →* H,
      F.comp (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4))) = f ∧
      F.comp (viaEmbeddingHom (Fin.succEmb (m + 3))) = g := by
  have hov : ∀ i < m + 1, f (adjSwap (m + 2) (i + 1)) = g (adjSwap (m + 2) i) := by
    intro i hi
    have h := congrArg (fun φ : Perm (Fin (m + 2)) →* H => φ (adjSwap (m + 1) i)) hOverlap
    simp only [MonoidHom.comp_apply] at h
    rwa [viaEmbeddingHom_succEmb_adjSwap (m + 1) i hi,
      viaEmbeddingHom_castSuccEmb_adjSwap (m + 1) i hi] at h
  set y : H := g (adjSwap (m + 2) (m + 1)) with hy
  let S : ℕ → H := snoc (m + 2) (fun i => f (adjSwap (m + 2) i)) y
  have hS : ∀ i < m + 2, S i = f (adjSwap (m + 2) i) := fun i hi => snoc_of_lt hi
  have hSn : S (m + 2) = y := snoc_self
  have hsq : y * y = 1 := by
    have h := (isCoxeterA_adjSwap (m + 2)).sq (m + 1) (by omega)
    rw [hy, ← map_mul, h, map_one]
  have hbraid : 1 ≤ m + 2 →
      f (adjSwap (m + 2) (m + 2 - 1)) * y * f (adjSwap (m + 2) (m + 2 - 1)) =
        y * f (adjSwap (m + 2) (m + 2 - 1)) * y := by
    intro _
    rw [show m + 2 - 1 = m + 1 by omega, hov m (by omega), hy]
    have hb := (isCoxeterA_adjSwap (m + 2)).braid m (by omega)
    calc g (adjSwap (m + 2) m) * g (adjSwap (m + 2) (m + 1)) * g (adjSwap (m + 2) m)
        = g (adjSwap (m + 2) m * adjSwap (m + 2) (m + 1) * adjSwap (m + 2) m) := by
          rw [map_mul, map_mul]
      _ = g (adjSwap (m + 2) (m + 1) * adjSwap (m + 2) m * adjSwap (m + 2) (m + 1)) := by
          rw [hb]
      _ = g (adjSwap (m + 2) (m + 1)) * g (adjSwap (m + 2) m) *
          g (adjSwap (m + 2) (m + 1)) := by
          rw [map_mul, map_mul]
  have hcomm : ∀ i, i + 2 ≤ m + 2 →
      f (adjSwap (m + 2) i) * y = y * f (adjSwap (m + 2) i) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hy]
      exact hCross
    · rw [show i = (i - 1) + 1 by omega, hov (i - 1) (by omega), hy]
      have hc := (isCoxeterA_adjSwap (m + 2)).comm (i - 1) (m + 1) (by omega) (by omega)
      rw [← map_mul, ← map_mul, hc]
  have hxcox : IsCoxeterA (m + 2) (fun i => f (adjSwap (m + 2) i)) :=
    IsCoxeterA.map f (isCoxeterA_adjSwap (m + 2))
  have hxsnoc : IsCoxeterA (m + 3) S := IsCoxeterA.snoc hxcox hsq hbraid hcomm
  obtain ⟨F, hF⟩ := exists_hom_perm (m + 3) S hxsnoc
  refine ⟨F, ?_, ?_⟩
  · refine MonoidHom.eq_of_eqOn_dense (s := adjSwap (m + 2) '' Set.Iio (m + 2))
      (closure_adjSwap (m + 2)) ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < m + 2 := hi
    simp only [MonoidHom.comp_apply]
    rw [viaEmbeddingHom_castSuccEmb_adjSwap (m + 2) i hi', hF i (by omega)]
    exact hS i hi'
  · refine MonoidHom.eq_of_eqOn_dense (s := adjSwap (m + 2) '' Set.Iio (m + 2))
      (closure_adjSwap (m + 2)) ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < m + 2 := hi
    simp only [MonoidHom.comp_apply]
    rw [viaEmbeddingHom_succEmb_adjSwap (m + 2) i hi', hF (i + 1) (by omega)]
    by_cases h : i + 1 < m + 2
    · rw [hS (i + 1) h]
      exact hov i (by omega)
    · have h2 : S (m + 2) = g (adjSwap (m + 2) (m + 1)) := by rw [hSn, hy]
      obtain rfl : i = m + 1 := by omega
      exact h2

theorem eq_of_comp_viaEmbeddingHom_eq {H : Type*} [Group H] (m : ℕ)
    {F F' : Perm (Fin (m + 4)) →* H}
    (hF : F.comp (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4))) =
      F'.comp (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4))))
    (hG : F.comp (viaEmbeddingHom (Fin.succEmb (m + 3))) =
      F'.comp (viaEmbeddingHom (Fin.succEmb (m + 3)))) : F = F' := by
  refine MonoidHom.eq_of_eqOn_dense (s := adjSwap (m + 3) '' Set.Iio (m + 3))
    (closure_adjSwap (m + 3)) ?_
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i < m + 3 := hi
  by_cases h : i < m + 2
  · have hi2 : i < m + 2 := h
    have hiff := congrArg (fun φ : Perm (Fin (m + 3)) →* H => φ (adjSwap (m + 2) i)) hF
    simp only [MonoidHom.comp_apply] at hiff
    rwa [viaEmbeddingHom_castSuccEmb_adjSwap (m + 2) i hi2] at hiff
  · obtain rfl : i = m + 2 := by omega
    have hiff := congrArg (fun φ : Perm (Fin (m + 3)) →* H => φ (adjSwap (m + 2) (m + 1))) hG
    simp only [MonoidHom.comp_apply] at hiff
    rwa [viaEmbeddingHom_succEmb_adjSwap (m + 2) (m + 1) (by omega)] at hiff

theorem range_eq_sup {H : Type*} [Group H] {m : ℕ}
    {f g : Perm (Fin (m + 3)) →* H} {F : Perm (Fin (m + 4)) →* H}
    (hF : F.comp (viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4))) = f)
    (hG : F.comp (viaEmbeddingHom (Fin.succEmb (m + 3))) = g) :
    F.range = f.range ⊔ g.range := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [MonoidHom.range_eq_map, ← closure_adjSwap (m + 3), MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨i, hi, rfl⟩ := hσ
    have hi' : i < m + 3 := hi
    by_cases h : i < m + 2
    · have h1 : F (adjSwap (m + 3) i) = f (adjSwap (m + 2) i) := by
        rw [← hF, MonoidHom.comp_apply, viaEmbeddingHom_castSuccEmb_adjSwap (m + 2) i h]
      rw [h1]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · obtain rfl : i = m + 2 := by omega
      have h2 : F (adjSwap (m + 3) (m + 2)) = g (adjSwap (m + 2) (m + 1)) := by
        rw [← hG, MonoidHom.comp_apply,
          viaEmbeddingHom_succEmb_adjSwap (m + 2) (m + 1) (by omega)]
      rw [h2]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩
  · rintro _ ⟨σ, rfl⟩
    refine ⟨viaEmbeddingHom (Fin.castSuccEmb : Fin (m + 3) ↪ Fin (m + 4)) σ, ?_⟩
    rw [← hF, MonoidHom.comp_apply]
  · rintro _ ⟨σ, rfl⟩
    refine ⟨viaEmbeddingHom (Fin.succEmb (m + 3)) σ, ?_⟩
    rw [← hG, MonoidHom.comp_apply]

end CFSG.Permutation.SymmetricCoxeter
