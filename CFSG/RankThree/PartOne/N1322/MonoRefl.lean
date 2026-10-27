module

public import CFSG.RankThree.PartOne.N1322.CoreDefs
import Mathlib.Tactic.LinearCombination
public import CFSG.RankThree.PartOne.N1322.Mono

public section

namespace CFSG.RankThree.PartOne.N1322

open Matrix Equiv

variable {K : Type*} [Field K]

@[expose] def permGraph (K : Type*) [Field K] : Subgroup (GL (Fin 3) K × Perm (Fin 3)) where
  carrier := {x | ∃ a : Fin 3 → Kˣ, x.1 = mono x.2 a}
  mul_mem' := by
    rintro ⟨g, σ⟩ ⟨g', τ⟩ ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : g = mono σ a := ha
    have hb' : g' = mono τ b := hb
    refine ⟨fun j => a (τ j) * b j, ?_⟩
    show g * g' = mono (σ * τ) (fun j => a (τ j) * b j)
    rw [ha', hb', mono_mul]
  one_mem' := ⟨fun _ => 1, by simp [mono_one]⟩
  inv_mem' := by
    rintro ⟨g, σ⟩ ⟨a, ha⟩
    have ha' : g = mono σ a := ha
    refine ⟨fun j => (a (σ⁻¹ j))⁻¹, ?_⟩
    show g⁻¹ = mono σ⁻¹ (fun j => (a (σ⁻¹ j))⁻¹)
    rw [ha', mono_inv]

@[expose] def HasPerm (g : GL (Fin 3) K) (σ : Perm (Fin 3)) : Prop :=
  ∃ a : Fin 3 → Kˣ, g = mono σ a

theorem hasPerm_mono (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) : HasPerm (mono σ a : GL (Fin 3) K) σ :=
  ⟨a, rfl⟩

theorem HasPerm.mul {g g' : GL (Fin 3) K} {σ τ : Perm (Fin 3)} (h : HasPerm g σ)
    (h' : HasPerm g' τ) : HasPerm (g * g') (σ * τ) :=
  (permGraph K).mul_mem (x := (g, σ)) (y := (g', τ)) h h'

theorem HasPerm.inv {g : GL (Fin 3) K} {σ : Perm (Fin 3)} (h : HasPerm g σ) :
    HasPerm g⁻¹ σ⁻¹ :=
  (permGraph K).inv_mem (x := (g, σ)) h

theorem HasPerm.zpow {g : GL (Fin 3) K} {σ : Perm (Fin 3)} (h : HasPerm g σ) (k : ℤ) :
    HasPerm (g ^ k) (σ ^ k) :=
  (permGraph K).zpow_mem (x := (g, σ)) h k

theorem HasPerm.unique {g : GL (Fin 3) K} {σ τ : Perm (Fin 3)} (h : HasPerm g σ)
    (h' : HasPerm g τ) : σ = τ := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact (mono_injective (ha.symm.trans hb)).1

theorem mono_conj_diag (d : Fin 3 → Kˣ) (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) :
    (mono 1 d : GL (Fin 3) K) * mono σ a * (mono 1 d)⁻¹ =
      mono σ (fun j => d (σ j) * a j * (d j)⁻¹) := by
  rw [mono_inv, mono_mul, mono_mul]
  exact congrArg₂ mono (by simp) (by funext j; simp)

theorem mono_conj_perm (τ σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) :
    (mono τ (fun _ => 1) : GL (Fin 3) K) * mono σ a * (mono τ (fun _ => 1))⁻¹ =
      mono (τ * σ * τ⁻¹) (fun j => a (τ⁻¹ j)) := by
  rw [mono_inv, mono_mul, mono_mul]
  exact congrArg₂ mono rfl (by funext j; simp)

theorem mono_mul_diag_mul_inv (σ : Perm (Fin 3)) (a b : Fin 3 → Kˣ) :
    (mono σ a : GL (Fin 3) K) * mono 1 b * (mono σ a)⁻¹ = mono 1 (fun j => b (σ⁻¹ j)) := by
  rw [mono_inv, mono_mul, mono_mul]
  exact congrArg₂ mono (by simp) (by funext j; simp)

@[expose] def epsU (i : Fin 3) : Fin 3 → Kˣ := fun j => if j = i then -1 else 1

@[expose] def eps (i : Fin 3) : GL (Fin 3) K := mono 1 (epsU i)

@[expose] def aU (i j : Fin 3) (r : Kˣ) : Fin 3 → Kˣ :=
  fun m => if m = i then r else if m = j then r⁻¹ else 1

@[expose] def aref (i j : Fin 3) (r : Kˣ) : GL (Fin 3) K := mono (swap i j) (aU i j r)

theorem eps_conj (σ : Perm (Fin 3)) (a : Fin 3 → Kˣ) (i : Fin 3) :
    (mono σ a : GL (Fin 3) K) * eps i * (mono σ a)⁻¹ = eps (σ i) := by
  rw [eps, mono_mul_diag_mul_inv]
  refine congrArg (mono 1) (funext fun j => ?_)
  show (if σ⁻¹ j = i then (-1 : Kˣ) else 1) = if j = σ i then -1 else 1
  simp only [Perm.inv_eq_iff_eq]

theorem trace_mono_of_fixed {σ : Perm (Fin 3)} {m : Fin 3} (hm : ∀ x, σ x = x ↔ x = m)
    (a : Fin 3 → Kˣ) : Matrix.trace ((mono σ a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = a m := by
  rw [Matrix.trace, Finset.sum_eq_single m]
  · simp [Matrix.diag, mono_val, monoMat_apply, (hm m).mpr rfl]
  · intro x _ hx
    have : σ x ≠ x := fun h => hx ((hm x).mp h)
    simp [Matrix.diag, mono_val, monoMat_apply, Ne.symm this]
  · simp

theorem trace_mono_one (a : Fin 3 → Kˣ) :
    Matrix.trace ((mono 1 a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = a 0 + a 1 + a 2 := by
  simp [Matrix.trace, Matrix.diag, mono_val, monoMat_apply, Fin.sum_univ_three]

theorem mono_sq_eq_one {σ : Perm (Fin 3)} {a : Fin 3 → Kˣ} (h : (mono σ a : GL (Fin 3) K) *
    mono σ a = 1) : σ * σ = 1 ∧ ∀ j, a (σ j) * a j = 1 := by
  rw [mono_mul, ← mono_one] at h
  have := mono_injective h
  refine ⟨this.1, fun j => ?_⟩
  have := congrFun this.2 j
  simpa using this

theorem perm_involution_cases : ∀ σ : Perm (Fin 3), σ * σ = 1 →
    σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 0 2 ∨ σ = swap 1 2 := by decide

theorem fin3_cases3 : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ m : Fin 3,
    m = i ∨ m = j ∨ m = k := by decide

theorem unit_sq_eq_one {a : Kˣ} (h : a * a = 1) : a = 1 ∨ a = -1 := by
  have h1 : ((a : K) - 1) * ((a : K) + 1) = 0 := by
    have : (a : K) * a = 1 := by simpa using congrArg Units.val h
    linear_combination this
  rcases mul_eq_zero.mp h1 with h2 | h2
  · left; exact Units.ext (by simpa [sub_eq_zero] using h2)
  · right; exact Units.ext (by simpa [add_eq_zero_iff_eq_neg] using h2)

theorem isRefl_swap {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hfix : ∀ x, swap i j x = x ↔ x = k) {a : Fin 3 → Kˣ}
    (h : IsRefl (mono (swap i j) a : GL (Fin 3) K)) : a = aU i j (a i) := by
  have hsq := mono_sq_eq_one h.sq
  have hk : (a k : K) = 1 := by
    have h1 := trace_mono_of_fixed (K := K) hfix a
    rw [h.trace_eq] at h1
    rw [← h1]; ring
  have hk' : a k = 1 := Units.ext hk
  have hij' : a j * a i = 1 := by
    have := hsq.2 i
    simpa using this
  funext m
  rcases fin3_cases3 i j k hij hik hjk m with rfl | rfl | rfl
  · simp [aU]
  · simp [aU, hij.symm]
    exact (eq_inv_of_mul_eq_one_left hij')
  · simp [aU, hik.symm, hjk.symm, hk']

theorem isRefl_diag (h2 : (2 : K) ≠ 0) {a : Fin 3 → Kˣ}
    (h : IsRefl (mono 1 a : GL (Fin 3) K)) : a = epsU 0 ∨ a = epsU 1 ∨ a = epsU 2 := by
  have hsq := mono_sq_eq_one h.sq
  have htr := trace_mono_one (K := K) a
  rw [h.trace_eq] at htr
  have hu : ∀ j, a j = 1 ∨ a j = -1 := fun j => unit_sq_eq_one (by simpa using hsq.2 j)
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hs : (a 0 : K) + a 1 + a 2 = 1 := by rw [← htr]; ring
  rcases hu 0 with h0 | h0 <;> rcases hu 1 with h1 | h1 <;> rcases hu 2 with h2' | h2'
  all_goals
    simp only [h0, h1, h2', Units.val_one, Units.val_neg] at hs
  · exact absurd (by linear_combination hs : (2 : K) = 0) h2
  · right; right
    funext m; fin_cases m <;> simp [epsU, h0, h1, h2']
  · right; left
    funext m; fin_cases m <;> simp [epsU, h0, h1, h2']
  · exact absurd (by linear_combination -hs : (2 : K) = 0) h2
  · left
    funext m; fin_cases m <;> simp [epsU, h0, h1, h2']
  · exact absurd (by linear_combination -hs : (2 : K) = 0) h2
  · exact absurd (by linear_combination -hs : (2 : K) = 0) h2
  · exact absurd (by linear_combination -hs : (4 : K) = 0) h4

end CFSG.RankThree.PartOne.N1322
