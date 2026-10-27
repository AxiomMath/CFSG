module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Ring.Int.Parity

import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup

variable {G : Type*} [Group G]

structure TrackData (P₁ P₂ H : Subgroup G) (x₁ x₂ : G) : Prop where
  x₁_mem : x₁ ∈ P₁
  x₁_not_mem : x₁ ∉ P₂
  x₂_mem : x₂ ∈ P₂
  x₂_not_mem : x₂ ∉ P₁
  x₁_norm : x₁ ∈ normalizer (H : Set G)
  x₂_norm : x₂ ∈ normalizer (H : Set G)
  reg₁ : ∀ y ∈ P₁, y ∈ normalizer (H : Set G) → y ∈ P₂ ∨ x₁⁻¹ * y ∈ P₂
  reg₂ : ∀ y ∈ P₂, y ∈ normalizer (H : Set G) → y ∈ P₁ ∨ x₂⁻¹ * y ∈ P₁

@[expose] def trackElt (x₁ x₂ : G) (i : ℤ) : G := (x₂ * x₁) ^ (i / 2)

@[expose] def trackPar (P₁ P₂ : Subgroup G) (i : ℤ) : Subgroup G := if Even i then P₁ else P₂

@[expose] def qv (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) (i : ℤ) : Subgroup G :=
  (trackPar Q₁ Q₂ i).map (MulAut.conj (trackElt x₁ x₂ i)).toMonoidHom

@[expose] def win (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) (a b : ℤ) : Subgroup G :=
  ⨅ i ∈ Finset.Icc a b, qv Q₁ Q₂ x₁ x₂ i

@[expose] noncomputable def dropS (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) (m : ℕ) : ℕ :=
  (qv Q₁ Q₂ x₁ x₂ 0).relIndex (win Q₁ Q₂ x₁ x₂ 1 m)

@[expose] noncomputable def dropL (Q₁ Q₂ : Subgroup G) (x₁ x₂ : G) (m : ℕ) : ℕ :=
  (qv Q₁ Q₂ x₁ x₂ 1).relIndex (win Q₁ Q₂ x₁ x₂ (1 - m) 0)

variable {P₁ P₂ H Q₁ Q₂ : Subgroup G} {x₁ x₂ : G}

theorem trackElt_add_two_mul (x₁ x₂ : G) (i k : ℤ) :
    trackElt x₁ x₂ (i + 2 * k) = (x₂ * x₁) ^ k * trackElt x₁ x₂ i := by
  rw [trackElt, trackElt, show (i + 2 * k) / 2 = k + i / 2 by omega, zpow_add]

theorem trackPar_add_two_mul (P₁ P₂ : Subgroup G) (i k : ℤ) :
    trackPar P₁ P₂ (i + 2 * k) = trackPar P₁ P₂ i := by
  simp only [trackPar, Int.even_add, even_two_mul, iff_true]

theorem trackPar_neg (P₁ P₂ : Subgroup G) (i : ℤ) : trackPar P₁ P₂ (-i) = trackPar P₁ P₂ i := by
  simp only [trackPar, even_neg]

theorem trackPar_le_normalizer (hQ₁ : P₁ ≤ normalizer (Q₁ : Set G))
    (hQ₂ : P₂ ≤ normalizer (Q₂ : Set G)) (i : ℤ) :
    trackPar P₁ P₂ i ≤ normalizer (trackPar Q₁ Q₂ i : Set G) := by
  unfold trackPar
  split_ifs
  · exact hQ₁
  · exact hQ₂

theorem mem_map_conj_iff {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_qv_iff {i : ℤ} {y : G} :
    y ∈ qv Q₁ Q₂ x₁ x₂ i ↔ (trackElt x₁ x₂ i)⁻¹ * y * trackElt x₁ x₂ i ∈ trackPar Q₁ Q₂ i :=
  mem_map_conj_iff

theorem mem_win_iff {a b : ℤ} {y : G} :
    y ∈ win Q₁ Q₂ x₁ x₂ a b ↔ ∀ i, a ≤ i → i ≤ b → y ∈ qv Q₁ Q₂ x₁ x₂ i := by
  simp only [win, mem_iInf, Finset.mem_Icc]
  exact ⟨fun h i h1 h2 => h i ⟨h1, h2⟩, fun h i hi => h i hi.1 hi.2⟩

theorem win_le_qv {a b i : ℤ} (h1 : a ≤ i) (h2 : i ≤ b) :
    win Q₁ Q₂ x₁ x₂ a b ≤ qv Q₁ Q₂ x₁ x₂ i :=
  fun _ hy => mem_win_iff.mp hy i h1 h2

theorem win_mono {a b a' b' : ℤ} (ha : a ≤ a') (hb : b' ≤ b) :
    win Q₁ Q₂ x₁ x₂ a b ≤ win Q₁ Q₂ x₁ x₂ a' b' :=
  fun _ hy => mem_win_iff.mpr fun i h1 h2 => mem_win_iff.mp hy i (by omega) (by omega)

theorem win_self (a : ℤ) : win Q₁ Q₂ x₁ x₂ a a = qv Q₁ Q₂ x₁ x₂ a := by
  ext y
  rw [mem_win_iff]
  refine ⟨fun h => h a le_rfl le_rfl, fun h i h1 h2 => ?_⟩
  obtain rfl : i = a := by omega
  exact h

theorem win_add_one_right {a b : ℤ} (h : a ≤ b + 1) :
    win Q₁ Q₂ x₁ x₂ a (b + 1) = win Q₁ Q₂ x₁ x₂ a b ⊓ qv Q₁ Q₂ x₁ x₂ (b + 1) := by
  ext y
  rw [mem_inf, mem_win_iff, mem_win_iff]
  refine ⟨fun hy => ⟨fun i h1 h2 => hy i h1 (by omega), hy _ h le_rfl⟩, ?_⟩
  rintro ⟨hy, hy'⟩ i h1 h2
  rcases (show i ≤ b ∨ i = b + 1 by omega) with h3 | rfl
  · exact hy i h1 h3
  · exact hy'

theorem win_sub_one_left {a b : ℤ} (h : a - 1 ≤ b) :
    win Q₁ Q₂ x₁ x₂ (a - 1) b = qv Q₁ Q₂ x₁ x₂ (a - 1) ⊓ win Q₁ Q₂ x₁ x₂ a b := by
  ext y
  rw [mem_inf, mem_win_iff, mem_win_iff]
  refine ⟨fun hy => ⟨hy _ le_rfl h, fun i h1 h2 => hy i (by omega) h2⟩, ?_⟩
  rintro ⟨hy', hy⟩ i h1 h2
  rcases (show a ≤ i ∨ i = a - 1 by omega) with h3 | rfl
  · exact hy i h3 h2
  · exact hy'

theorem map_qv_tau_pow (i k : ℤ) :
    (qv Q₁ Q₂ x₁ x₂ i).map (MulAut.conj ((x₂ * x₁) ^ k)).toMonoidHom =
      qv Q₁ Q₂ x₁ x₂ (i + 2 * k) := by
  ext y
  rw [mem_map_conj_iff, mem_qv_iff, mem_qv_iff, trackElt_add_two_mul, trackPar_add_two_mul]
  simp only [mul_inv_rev, mul_assoc]

theorem map_win_tau_pow (a b k : ℤ) :
    (win Q₁ Q₂ x₁ x₂ a b).map (MulAut.conj ((x₂ * x₁) ^ k)).toMonoidHom =
      win Q₁ Q₂ x₁ x₂ (a + 2 * k) (b + 2 * k) := by
  ext y
  rw [mem_map_conj_iff, mem_win_iff, mem_win_iff]
  constructor
  · intro h i h1 h2
    have := h (i - 2 * k) (by omega) (by omega)
    rw [← mem_map_conj_iff, map_qv_tau_pow, sub_add_cancel] at this
    exact this
  · intro h i h1 h2
    rw [← mem_map_conj_iff, map_qv_tau_pow]
    exact h _ (by omega) (by omega)

theorem relIndex_shift {j a b j' a' b' : ℤ} (k : ℤ) (hj : j' = j + 2 * k) (ha : a' = a + 2 * k)
    (hb : b' = b + 2 * k) :
    (qv Q₁ Q₂ x₁ x₂ j').relIndex (win Q₁ Q₂ x₁ x₂ a' b') =
      (qv Q₁ Q₂ x₁ x₂ j).relIndex (win Q₁ Q₂ x₁ x₂ a b) := by
  subst hj ha hb
  rw [← map_qv_tau_pow, ← map_win_tau_pow,
    relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]

theorem refl_induction {N : Subgroup G} {x₁ τ : G} (hx₁ : x₁ ∈ P₁) (hx₁' : x₁ ∉ P₂)
    (hx₂ : τ * x₁⁻¹ ∈ P₂) (hx₂' : τ * x₁⁻¹ ∉ P₁) (hx₁N : x₁ ∈ N) (hτN : τ ∈ N)
    (reg₁ : ∀ y ∈ P₁, y ∈ N → y ∈ P₂ ∨ x₁⁻¹ * y ∈ P₂)
    (reg₂ : ∀ y ∈ P₂, y ∈ N → y ∈ P₁ ∨ (τ * x₁⁻¹)⁻¹ * y ∈ P₁) (j : ℤ) :
    τ ^ j * x₁ * τ ^ j ∈ P₁ ∧ τ ^ (j + 1) * x₁ * τ ^ j ∈ P₂ := by
  have hx₂N : τ * x₁⁻¹ ∈ N := mul_mem hτN (inv_mem hx₁N)
  have hpN : ∀ k : ℤ, τ ^ k ∈ N := fun k => zpow_mem hτN k
  have hsq₁ : x₁ * x₁ ∈ P₂ := by
    rcases reg₁ x₁⁻¹ (inv_mem hx₁) (inv_mem hx₁N) with h | h
    · exact absurd (inv_mem_iff.mp h) hx₁'
    · have := inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
  have hsq₂ : τ * x₁⁻¹ * (τ * x₁⁻¹) ∈ P₁ := by
    rcases reg₂ (τ * x₁⁻¹)⁻¹ (inv_mem hx₂) (inv_mem hx₂N) with h | h
    · exact absurd (inv_mem_iff.mp h) hx₂'
    · have := inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
  have up : ∀ k : ℤ, τ ^ k * x₁ * τ ^ k ∈ P₁ → τ ^ (k + 1) * x₁ * τ ^ k ∈ P₂ →
      τ ^ (k + 1) * x₁ * τ ^ (k + 1) ∈ P₁ ∧ τ ^ (k + 1 + 1) * x₁ * τ ^ (k + 1) ∈ P₂ := by
    intro k h0 h1
    have hA : τ ^ (k + 1) * x₁ * τ ^ (k + 1) ∈ P₁ := by
      have hyN : τ ^ (k + 1) * x₁ * τ ^ k * (τ * x₁⁻¹) ∈ N :=
        mul_mem (mul_mem (mul_mem (hpN _) hx₁N) (hpN _)) hx₂N
      rcases reg₂ _ (mul_mem h1 hx₂) hyN with h | h
      · have := mul_mem h hx₁
        convert this using 1
        group
      · refine absurd ?_ hx₂'
        have := mul_mem (inv_mem (mul_mem hx₁ h0)) h
        convert this using 1
        group
    refine ⟨hA, ?_⟩
    have hzN : x₁ * (τ ^ (k + 1) * x₁ * τ ^ (k + 1)) ∈ N :=
      mul_mem hx₁N (mul_mem (mul_mem (hpN _) hx₁N) (hpN _))
    rcases reg₁ _ (mul_mem hx₁ hA) hzN with h | h
    · have := mul_mem hx₂ h
      convert this using 1
      group
    · refine absurd ?_ hx₁'
      rw [inv_mul_cancel_left] at h
      have := mul_mem (inv_mem hx₂) (mul_mem (inv_mem h1) h)
      convert this using 1
      group
  have down : ∀ k : ℤ, τ ^ k * x₁ * τ ^ k ∈ P₁ → τ ^ (k + 1) * x₁ * τ ^ k ∈ P₂ →
      τ ^ (k - 1) * x₁ * τ ^ (k - 1) ∈ P₁ ∧ τ ^ (k - 1 + 1) * x₁ * τ ^ (k - 1) ∈ P₂ := by
    intro k h0 h1
    have hu : x₁ * (τ ^ k * x₁ * τ ^ k) ∈ P₂ := by
      have := mul_mem (inv_mem hx₂) h1
      convert this using 1
      group
    have hB : τ ^ (k - 1 + 1) * x₁ * τ ^ (k - 1) ∈ P₂ := by
      have hyN : τ ^ k * x₁ * τ ^ k * x₁⁻¹ ∈ N :=
        mul_mem (mul_mem (mul_mem (hpN _) hx₁N) (hpN _)) (inv_mem hx₁N)
      rcases reg₁ _ (mul_mem h0 (inv_mem hx₁)) hyN with h | h
      · have := mul_mem h (inv_mem hx₂)
        convert this using 1
        group
      · refine absurd ?_ hx₁'
        have := inv_mem (mul_mem (mul_mem (inv_mem hu) hsq₁) h)
        convert this using 1
        group
    refine ⟨?_, hB⟩
    have hzN : (τ * x₁⁻¹)⁻¹ * (τ ^ (k - 1 + 1) * x₁ * τ ^ (k - 1)) ∈ N :=
      mul_mem (inv_mem hx₂N) (mul_mem (mul_mem (hpN _) hx₁N) (hpN _))
    rcases reg₂ _ (mul_mem (inv_mem hx₂) hB) hzN with h | h
    · have := mul_mem (inv_mem hx₁) h
      convert this using 1
      group
    · refine absurd ?_ hx₂'
      have hd : τ ^ (k - 1 + 1) * x₁ * τ ^ (k - 1) * (τ * x₁⁻¹) ∈ P₁ := by
        have := mul_mem h0 (inv_mem hx₁)
        convert this using 1
        group
      have hc : τ ^ (k - 1 + 1) * x₁ * τ ^ (k - 1) ∈ P₁ := by
        have := mul_mem hsq₂ h
        convert this using 1
        group
      have := mul_mem (inv_mem hc) hd
      convert this using 1
      group
  induction j using Int.induction_on with
  | zero =>
    refine ⟨by simpa using hx₁, ?_⟩
    have := mul_mem hx₂ hsq₁
    convert this using 1
    group
  | succ k ih => exact up k ih.1 ih.2
  | pred k ih => exact down (-k) ih.1 ih.2

namespace TrackData

variable (T : TrackData P₁ P₂ H x₁ x₂)
include T

theorem tau_mem_normalizer : x₂ * x₁ ∈ normalizer (H : Set G) :=
  mul_mem T.x₂_norm T.x₁_norm

theorem x₁_mul_self_mem : x₁ * x₁ ∈ P₂ := by
  rcases T.reg₁ x₁⁻¹ (inv_mem T.x₁_mem) (inv_mem T.x₁_norm) with h | h
  · exact absurd (inv_mem_iff.mp h) T.x₁_not_mem
  · have := inv_mem h
    rwa [mul_inv_rev, inv_inv] at this

theorem refl_aux (j : ℤ) :
    (x₂ * x₁) ^ j * x₁ * (x₂ * x₁) ^ j ∈ P₁ ∧
      (x₂ * x₁) ^ (j + 1) * x₁ * (x₂ * x₁) ^ j ∈ P₂ := by
  have h : x₂ * x₁ * x₁⁻¹ = x₂ := mul_inv_cancel_right x₂ x₁
  exact refl_induction T.x₁_mem T.x₁_not_mem (by rw [h]; exact T.x₂_mem)
    (by rw [h]; exact T.x₂_not_mem) T.x₁_norm T.tau_mem_normalizer T.reg₁
    (by rw [h]; exact T.reg₂) j

theorem mem_trackPar (i : ℤ) :
    (trackElt x₁ x₂ (-i))⁻¹ * x₁ * trackElt x₁ x₂ i ∈ trackPar P₁ P₂ i := by
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' i
  · have hpar : trackPar P₁ P₂ (2 * j) = P₁ := by simp [trackPar]
    rw [hpar, trackElt, trackElt, show -(2 * j) / 2 = -j by omega,
      show 2 * j / 2 = j by omega, zpow_neg, inv_inv]
    exact (T.refl_aux j).1
  · have hpar : trackPar P₁ P₂ (2 * j + 1) = P₂ := by
      simp [trackPar, Int.even_add_one]
    rw [hpar, trackElt, trackElt, show -(2 * j + 1) / 2 = -(j + 1) by omega,
      show (2 * j + 1) / 2 = j by omega, zpow_neg, inv_inv]
    exact (T.refl_aux j).2

theorem le_normalizer_qv (hH₁ : H ≤ P₁) (hH₂ : H ≤ P₂) (hQ₁ : P₁ ≤ normalizer (Q₁ : Set G))
    (hQ₂ : P₂ ≤ normalizer (Q₂ : Set G)) (i : ℤ) :
    H ≤ normalizer (qv Q₁ Q₂ x₁ x₂ i : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro y
  rw [mem_qv_iff, mem_qv_iff]
  have ht : (trackElt x₁ x₂ i)⁻¹ ∈ normalizer (H : Set G) :=
    inv_mem (zpow_mem T.tau_mem_normalizer _)
  generalize trackElt x₁ x₂ i = t at ht ⊢
  have hh' : t⁻¹ * h * t ∈ H := by
    have := (mem_normalizer_iff.mp ht h).mp hh
    rwa [inv_inv] at this
  have hP : t⁻¹ * h * t ∈ trackPar P₁ P₂ i := by
    unfold trackPar
    split_ifs
    · exact hH₁ hh'
    · exact hH₂ hh'
  have key : t⁻¹ * (h * y * h⁻¹) * t = t⁻¹ * h * t * (t⁻¹ * y * t) * (t⁻¹ * h * t)⁻¹ := by
    group
  rw [key]
  exact mem_normalizer_iff.mp (trackPar_le_normalizer hQ₁ hQ₂ i hP) _

variable (hQ₁ : P₁ ≤ normalizer (Q₁ : Set G)) (hQ₂ : P₂ ≤ normalizer (Q₂ : Set G))
include hQ₁ hQ₂

theorem map_qv_x₁ (i : ℤ) :
    (qv Q₁ Q₂ x₁ x₂ i).map (MulAut.conj x₁).toMonoidHom = qv Q₁ Q₂ x₁ x₂ (-i) := by
  have heN := trackPar_le_normalizer hQ₁ hQ₂ i (T.mem_trackPar i)
  ext y
  rw [mem_map_conj_iff, mem_qv_iff, mem_qv_iff, trackPar_neg]
  generalize trackElt x₁ x₂ i = s at heN ⊢
  generalize trackElt x₁ x₂ (-i) = t at heN ⊢
  have key : s⁻¹ * (x₁⁻¹ * y * x₁) * s =
      (t⁻¹ * x₁ * s)⁻¹ * (t⁻¹ * y * t) * (t⁻¹ * x₁ * s)⁻¹⁻¹ := by
    group
  rw [key]
  exact (mem_normalizer_iff.mp (inv_mem heN) _).symm

theorem mem_qv_neg_iff (i : ℤ) {y : G} :
    y ∈ qv Q₁ Q₂ x₁ x₂ i ↔ x₁⁻¹ * y * x₁ ∈ qv Q₁ Q₂ x₁ x₂ (-i) := by
  rw [← mem_map_conj_iff, T.map_qv_x₁ hQ₁ hQ₂, neg_neg]

theorem map_qv_x₂ (i : ℤ) :
    (qv Q₁ Q₂ x₁ x₂ i).map (MulAut.conj x₂).toMonoidHom = qv Q₁ Q₂ x₁ x₂ (2 - i) := by
  ext y
  rw [mem_map_conj_iff, T.mem_qv_neg_iff hQ₁ hQ₂, show (2 : ℤ) - i = -i + 2 * 1 by ring,
    ← map_qv_tau_pow (-i) 1, mem_map_conj_iff, zpow_one]
  simp only [mul_inv_rev, mul_assoc]

theorem mem_qv_two_sub_iff (i : ℤ) {y : G} :
    y ∈ qv Q₁ Q₂ x₁ x₂ i ↔ x₂⁻¹ * y * x₂ ∈ qv Q₁ Q₂ x₁ x₂ (2 - i) := by
  rw [← mem_map_conj_iff, T.map_qv_x₂ hQ₁ hQ₂, sub_sub_cancel]

theorem map_win_x₁ (a b : ℤ) :
    (win Q₁ Q₂ x₁ x₂ a b).map (MulAut.conj x₁).toMonoidHom = win Q₁ Q₂ x₁ x₂ (-b) (-a) := by
  ext y
  rw [mem_map_conj_iff, mem_win_iff, mem_win_iff]
  constructor
  · intro h i h1 h2
    rw [T.mem_qv_neg_iff hQ₁ hQ₂]
    exact h _ (by omega) (by omega)
  · intro h i h1 h2
    have := h (-i) (by omega) (by omega)
    rwa [T.mem_qv_neg_iff hQ₁ hQ₂, neg_neg] at this

theorem map_win_x₂ (a b : ℤ) :
    (win Q₁ Q₂ x₁ x₂ a b).map (MulAut.conj x₂).toMonoidHom =
      win Q₁ Q₂ x₁ x₂ (2 - b) (2 - a) := by
  ext y
  rw [mem_map_conj_iff, mem_win_iff, mem_win_iff]
  constructor
  · intro h i h1 h2
    rw [T.mem_qv_two_sub_iff hQ₁ hQ₂]
    exact h _ (by omega) (by omega)
  · intro h i h1 h2
    have := h (2 - i) (by omega) (by omega)
    rwa [T.mem_qv_two_sub_iff hQ₁ hQ₂, sub_sub_cancel] at this

theorem relIndex_refl₁ {j a b j' a' b' : ℤ} (hj : j' = -j) (ha : a' = -b) (hb : b' = -a) :
    (qv Q₁ Q₂ x₁ x₂ j').relIndex (win Q₁ Q₂ x₁ x₂ a' b') =
      (qv Q₁ Q₂ x₁ x₂ j).relIndex (win Q₁ Q₂ x₁ x₂ a b) := by
  subst hj ha hb
  rw [← T.map_qv_x₁ hQ₁ hQ₂, ← T.map_win_x₁ hQ₁ hQ₂,
    relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]

theorem relIndex_refl₂ {j a b j' a' b' : ℤ} (hj : j' = 2 - j) (ha : a' = 2 - b)
    (hb : b' = 2 - a) :
    (qv Q₁ Q₂ x₁ x₂ j').relIndex (win Q₁ Q₂ x₁ x₂ a' b') =
      (qv Q₁ Q₂ x₁ x₂ j).relIndex (win Q₁ Q₂ x₁ x₂ a b) := by
  subst hj ha hb
  rw [← T.map_qv_x₂ hQ₁ hQ₂, ← T.map_win_x₂ hQ₁ hQ₂,
    relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]

theorem rightDrop_eq (a : ℤ) (m : ℕ) :
    (qv Q₁ Q₂ x₁ x₂ (a + m)).relIndex (win Q₁ Q₂ x₁ x₂ a (a + m - 1)) =
      if Even (a + m) then dropS Q₁ Q₂ x₁ x₂ m else dropL Q₁ Q₂ x₁ x₂ m := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (a + m)
  · rw [if_pos (show Even (a + (m : ℤ)) from ⟨k, by omega⟩), dropS,
      relIndex_shift k (j := 0) (a := -m) (b := -1),
      T.relIndex_refl₁ hQ₁ hQ₂ (j' := 0) (a' := 1) (b' := m) (j := 0) (a := -m) (b := -1)]
    all_goals omega
  · rw [if_neg (Int.not_even_iff_odd.mpr ⟨k, hk⟩), dropL,
      relIndex_shift k (j := 1) (a := 1 - m) (b := 0)]
    all_goals omega

theorem leftDrop_eq (b : ℤ) (m : ℕ) :
    (qv Q₁ Q₂ x₁ x₂ (b - m)).relIndex (win Q₁ Q₂ x₁ x₂ (b - m + 1) b) =
      if Even (b - m) then dropS Q₁ Q₂ x₁ x₂ m else dropL Q₁ Q₂ x₁ x₂ m := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (b - m)
  · rw [if_pos (show Even (b - (m : ℤ)) from ⟨k, by omega⟩), dropS,
      relIndex_shift k (j := 0) (a := 1) (b := m)]
    all_goals omega
  · rw [if_neg (Int.not_even_iff_odd.mpr ⟨k, hk⟩), dropL,
      relIndex_shift k (j := 1) (a := 2) (b := m + 1),
      T.relIndex_refl₂ hQ₁ hQ₂ (j' := 1) (a' := 1 - m) (b' := 0) (j := 1) (a := 2) (b := m + 1)]
    all_goals omega

theorem card_win_zero_eq (m : ℤ) (hm : Even m) :
    Nat.card (win Q₁ Q₂ x₁ x₂ 0 (m - 1)) = Nat.card (win Q₁ Q₂ x₁ x₂ 1 m) := by
  obtain ⟨k, rfl⟩ := hm
  have h2 := map_win_tau_pow (Q₁ := Q₁) (Q₂ := Q₂) (x₁ := x₁) (x₂ := x₂) (-(k + k - 1)) (-0) k
  rw [show -(k + k - 1) + 2 * k = 1 by ring, show -0 + 2 * k = k + k by ring] at h2
  rw [← card_map_of_injective (f := (MulAut.conj x₁).toMonoidHom) (MulAut.conj x₁).injective,
    T.map_win_x₁ hQ₁ hQ₂,
    ← card_map_of_injective (f := (MulAut.conj ((x₂ * x₁) ^ k)).toMonoidHom)
      (MulAut.conj _).injective, h2]

end TrackData

end CFSG.Quasithin.Stroth.G5

end
