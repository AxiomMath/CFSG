module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.F112Tree
import CFSG.Timmesfeld.RankOne.Basic
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open CFSG.Timmesfeld.RankOne (map_conj_mul)

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem mem_map_conj_iff_of_map_eq {A B : Subgroup G} {g z : G}
    (h : A.map (MulAut.conj g).toMonoidHom = B) :
    z ∈ A ↔ MulAut.conj g z ∈ B := by
  rw [← h, mem_map_conj_iff, MulAut.conj_apply]
  constructor
  · intro hz; convert hz using 1; group
  · intro hz; convert hz using 1; group

private theorem mem_of_mem_of_map_conj {A B : Subgroup G} {g z : G}
    (h : A.map (MulAut.conj g).toMonoidHom = B) (hz : z ∈ B) :
    MulAut.conj g⁻¹ z ∈ A :=
  (mem_map_conj_iff_of_map_eq h).mpr (by
    simpa [MulAut.conj_apply, mul_assoc] using hz)

private theorem Gv_map_tau (i k : ℤ) :
    (t.Gv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Gv (i + 2 * k) := by
  change (qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ i).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
    qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (i + 2 * k)
  exact map_qv_tau_pow i k

private theorem Zv_map_tau (i k : ℤ) :
    (t.Zv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv (i + 2 * k) := by
  change (qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ i).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
    qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ (i + 2 * k)
  exact map_qv_tau_pow i k

private theorem Gw_map_tau (a b k : ℤ) :
    (t.Gw a b).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
      t.Gw (a + 2 * k) (b + 2 * k) := by
  change (win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ a b).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
    win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (a + 2 * k) (b + 2 * k)
  exact map_win_tau_pow a b k

structure IsMaxArc (ε : ℤ) (n : ℕ) : Prop where
  pCoreOf_ne_bot : pCoreOf 2 (t.Gw ε (ε + n)) ≠ ⊥
  pCoreOf_eq_bot : ∀ a b : ℤ, (n : ℤ) < b - a → pCoreOf 2 (t.Gw a b) = ⊥

structure IsFixRadius (v : ℤ) (b : ℕ) : Prop where
  le_Gw : t.Zv v ≤ t.Gw (v - b) (v + b)
  not_le_Gv : ¬ t.Zv v ≤ t.Gv (v + b + 1)

theorem exists_reflection (v : ℤ) :
    ∃ y ∈ t.Gv v, y ∈ normalizer (t.K : Set G) ∧
      (∀ u w : ℤ, (t.Gw u w).map (MulAut.conj y).toMonoidHom = t.Gw (2 * v - w) (2 * v - u)) ∧
      (∀ i : ℤ, (t.Qv i).map (MulAut.conj y).toMonoidHom = t.Qv (2 * v - i)) ∧
      (∀ i : ℤ, (t.Zv i).map (MulAut.conj y).toMonoidHom = t.Zv (2 * v - i)) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · let τ : G := t.x₂ * t.x₁
    let y : G := τ ^ k * t.x₁ * τ ^ (-k)
    have hyv : y ∈ t.Gv (2 * k) := by
      change y ∈ qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (2 * k)
      rw [mem_qv_iff]
      have he : trackElt t.x₁ t.x₂ (2 * k) = τ ^ k := by
        simp [trackElt, τ, show (2 * k : ℤ) / 2 = k by omega]
      rw [he, show (τ ^ k)⁻¹ * y * τ ^ k = t.x₁ by simp only [y]; group,
        show trackPar (P1 L1 L2 S) (P2 L1 L2 S) (2 * k) = P1 L1 L2 S by simp [trackPar]]
      exact t.track.x₁_mem
    have hyK : y ∈ normalizer (t.K : Set G) := by
      have hτ : τ ∈ normalizer (t.K : Set G) := t.track.tau_mem_normalizer
      simpa only [y, inv_zpow'] using
        mul_mem (mul_mem (zpow_mem hτ k) t.track.x₁_norm) (zpow_mem (inv_mem hτ) k)
    have hmap : ∀ u w : ℤ, (t.Gw u w).map (MulAut.conj y).toMonoidHom =
        t.Gw (2 * (2 * k) - w) (2 * (2 * k) - u) := by
      intro u w
      have hy : (t.Gw u w).map (MulAut.conj y).toMonoidHom =
          (((t.Gw u w).map (MulAut.conj (τ ^ (-k))).toMonoidHom).map
            (MulAut.conj t.x₁).toMonoidHom).map (MulAut.conj (τ ^ k)).toMonoidHom := by
        rw [show y = τ ^ k * (t.x₁ * τ ^ (-k)) by simp only [y]; group,
          map_conj_mul, map_conj_mul]
      rw [hy, map_win_tau_pow,
        t.track.map_win_x₁ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
          Subgroup.le_normalizer Subgroup.le_normalizer, map_win_tau_pow]
      congr 1 <;> ring
    have hQ : ∀ i : ℤ, (t.Qv i).map (MulAut.conj y).toMonoidHom = t.Qv (2 * (2 * k) - i) := by
      intro i
      have hQ₁ : P1 L1 L2 S ≤ normalizer (Q1 L1 L2 S : Set G) :=
        le_normalizer_pCoreOf 2 (P1 L1 L2 S)
      have hQ₂ : P2 L1 L2 S ≤ normalizer (Q2 L1 L2 S : Set G) :=
        le_normalizer_pCoreOf 2 (P2 L1 L2 S)
      have hy : (t.Qv i).map (MulAut.conj y).toMonoidHom =
          (((t.Qv i).map (MulAut.conj (τ ^ (-k))).toMonoidHom).map
            (MulAut.conj t.x₁).toMonoidHom).map (MulAut.conj (τ ^ k)).toMonoidHom := by
        rw [show y = τ ^ k * (t.x₁ * τ ^ (-k)) by simp only [y]; group,
          map_conj_mul, map_conj_mul]
      rw [hy, map_qv_tau_pow, t.track.map_qv_x₁ hQ₁ hQ₂, map_qv_tau_pow]
      congr 1
      ring
    have hZ : ∀ i : ℤ, (t.Zv i).map (MulAut.conj y).toMonoidHom = t.Zv (2 * (2 * k) - i) := by
      intro i
      have hZ₁ : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf _)
      have hZ₂ : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
        (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf _)
      have hy : (t.Zv i).map (MulAut.conj y).toMonoidHom =
          (((t.Zv i).map (MulAut.conj (τ ^ (-k))).toMonoidHom).map
            (MulAut.conj t.x₁).toMonoidHom).map (MulAut.conj (τ ^ k)).toMonoidHom := by
        rw [show y = τ ^ k * (t.x₁ * τ ^ (-k)) by simp only [y]; group,
          map_conj_mul, map_conj_mul]
      rw [hy, map_qv_tau_pow, t.track.map_qv_x₁ hZ₁ hZ₂, map_qv_tau_pow]
      congr 1
      ring
    exact ⟨y, hyv, hyK, hmap, hQ, hZ⟩
  · let τ : G := t.x₂ * t.x₁
    let y : G := τ ^ k * t.x₂ * τ ^ (-k)
    have hyv : y ∈ t.Gv (2 * k + 1) := by
      change y ∈ qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (2 * k + 1)
      rw [mem_qv_iff]
      have he : trackElt t.x₁ t.x₂ (2 * k + 1) = τ ^ k := by
        simp [trackElt, τ, show (2 * k + 1 : ℤ) / 2 = k by omega]
      rw [he, show (τ ^ k)⁻¹ * y * τ ^ k = t.x₂ by simp only [y]; group,
        show trackPar (P1 L1 L2 S) (P2 L1 L2 S) (2 * k + 1) = P2 L1 L2 S by
          simp [trackPar, Int.even_add_one]]
      exact t.track.x₂_mem
    have hyK : y ∈ normalizer (t.K : Set G) := by
      have hτ : τ ∈ normalizer (t.K : Set G) := t.track.tau_mem_normalizer
      simpa only [y, inv_zpow'] using
        mul_mem (mul_mem (zpow_mem hτ k) t.track.x₂_norm) (zpow_mem (inv_mem hτ) k)
    have hmap : ∀ u w : ℤ, (t.Gw u w).map (MulAut.conj y).toMonoidHom =
        t.Gw (2 * (2 * k + 1) - w) (2 * (2 * k + 1) - u) := by
      intro u w
      have hy : (t.Gw u w).map (MulAut.conj y).toMonoidHom =
          (((t.Gw u w).map (MulAut.conj (τ ^ (-k))).toMonoidHom).map
            (MulAut.conj t.x₂).toMonoidHom).map (MulAut.conj (τ ^ k)).toMonoidHom := by
        rw [show y = τ ^ k * (t.x₂ * τ ^ (-k)) by simp only [y]; group,
          map_conj_mul, map_conj_mul]
      rw [hy, map_win_tau_pow,
        t.track.map_win_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
          Subgroup.le_normalizer Subgroup.le_normalizer, map_win_tau_pow]
      congr 1 <;> ring
    have hQ : ∀ i : ℤ, (t.Qv i).map (MulAut.conj y).toMonoidHom =
        t.Qv (2 * (2 * k + 1) - i) := by
      intro i
      have hQ₁ : P1 L1 L2 S ≤ normalizer (Q1 L1 L2 S : Set G) :=
        le_normalizer_pCoreOf 2 (P1 L1 L2 S)
      have hQ₂ : P2 L1 L2 S ≤ normalizer (Q2 L1 L2 S : Set G) :=
        le_normalizer_pCoreOf 2 (P2 L1 L2 S)
      have hy : (t.Qv i).map (MulAut.conj y).toMonoidHom =
          (((t.Qv i).map (MulAut.conj (τ ^ (-k))).toMonoidHom).map
            (MulAut.conj t.x₂).toMonoidHom).map (MulAut.conj (τ ^ k)).toMonoidHom := by
        rw [show y = τ ^ k * (t.x₂ * τ ^ (-k)) by simp only [y]; group,
          map_conj_mul, map_conj_mul]
      rw [hy, map_qv_tau_pow, t.track.map_qv_x₂ hQ₁ hQ₂, map_qv_tau_pow]
      congr 1
      ring
    have hZ : ∀ i : ℤ, (t.Zv i).map (MulAut.conj y).toMonoidHom =
        t.Zv (2 * (2 * k + 1) - i) := by
      intro i
      have hZ₁ : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
        (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf _)
      have hZ₂ : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
        (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf _)
      have hy : (t.Zv i).map (MulAut.conj y).toMonoidHom =
          (((t.Zv i).map (MulAut.conj (τ ^ (-k))).toMonoidHom).map
            (MulAut.conj t.x₂).toMonoidHom).map (MulAut.conj (τ ^ k)).toMonoidHom := by
        rw [show y = τ ^ k * (t.x₂ * τ ^ (-k)) by simp only [y]; group,
          map_conj_mul, map_conj_mul]
      rw [hy, map_qv_tau_pow, t.track.map_qv_x₂ hZ₁ hZ₂, map_qv_tau_pow]
      congr 1
      ring
    exact ⟨y, hyv, hyK, hmap, hQ, hZ⟩

private theorem mem_Gv_of_mem_Gw_zero_one {z : G} (hz : z ∈ t.Gw 0 1)
    (hzK : z ∈ normalizer (t.K : Set G)) : z ∈ t.Gv (-1) ∧ z ∈ t.Gv 2 := by
  have hz0 : z ∈ P1 L1 L2 S := by
    have h := mem_win_iff.mp hz 0 (by norm_num) (by norm_num)
    change z ∈ t.Gv 0 at h
    rwa [t.Gv_zero] at h
  have hz1 : z ∈ P2 L1 L2 S := by
    have h := mem_win_iff.mp hz 1 (by norm_num) (by norm_num)
    change z ∈ t.Gv 1 at h
    rwa [t.Gv_one] at h
  have hneg : z ∈ t.Gv (-1) := by
    refine (t.track.mem_qv_neg_iff (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer (-1)).mpr ?_
    rw [neg_neg]
    change t.x₁⁻¹ * z * t.x₁ ∈ t.Gv 1
    rw [t.Gv_one]
    rcases t.track.reg₁ (z * t.x₁) (mul_mem hz0 t.track.x₁_mem)
      (mul_mem hzK t.track.x₁_norm) with h | h
    · exact absurd (by simpa [mul_assoc] using mul_mem (inv_mem hz1) h) t.track.x₁_not_mem
    · simpa [mul_assoc] using h
  have htwo : z ∈ t.Gv 2 := by
    refine (t.track.mem_qv_two_sub_iff (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer 2).mpr ?_
    rw [sub_self]
    change t.x₂⁻¹ * z * t.x₂ ∈ t.Gv 0
    rw [t.Gv_zero]
    rcases t.track.reg₂ (z * t.x₂) (mul_mem hz1 t.track.x₂_mem)
      (mul_mem hzK t.track.x₂_norm) with h | h
    · exact absurd (by simpa [mul_assoc] using mul_mem (inv_mem hz0) h) t.track.x₂_not_mem
    · simpa [mul_assoc] using h
  exact ⟨hneg, htwo⟩

private theorem mem_Gv_of_mem_Gw_one_two {z : G} (hz : z ∈ t.Gw 1 2)
    (hzK : z ∈ normalizer (t.K : Set G)) : z ∈ t.Gv 0 ∧ z ∈ t.Gv 3 := by
  let g : G := t.x₂
  let z' : G := g * z * g⁻¹
  have hz' : z' ∈ t.Gw 0 1 := by
    have hmap : (t.Gw 1 2).map (MulAut.conj g).toMonoidHom = t.Gw 0 1 := by
      have := t.track.map_win_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        Subgroup.le_normalizer Subgroup.le_normalizer 1 2
      simpa [g] using this
    rw [← hmap]
    exact (mem_map_conj_iff (K := t.Gw 1 2) (g := g) (y := z')).mpr (by
      simpa [z', g, mul_assoc] using hz)
  have hz'K : z' ∈ normalizer (t.K : Set G) := by
    simp only [z', g]
    exact mul_mem (mul_mem t.track.x₂_norm hzK) (inv_mem t.track.x₂_norm)
  obtain ⟨hneg, htwo⟩ := t.mem_Gv_of_mem_Gw_zero_one hz' hz'K
  constructor
  · have hmap : (t.Gv 0).map (MulAut.conj g).toMonoidHom = t.Gv 2 := by
      have := t.track.map_qv_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        Subgroup.le_normalizer Subgroup.le_normalizer 0
      simpa [g] using this
    have h := mem_of_mem_of_map_conj hmap htwo
    convert h using 1
    simp only [z', g, MulAut.conj_apply, inv_inv]
    group
  · have hmap : (t.Gv 3).map (MulAut.conj g).toMonoidHom = t.Gv (-1) := by
      have := t.track.map_qv_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        Subgroup.le_normalizer Subgroup.le_normalizer 3
      simpa [g] using this
    have h := mem_of_mem_of_map_conj hmap hneg
    convert h using 1
    simp only [z', g, MulAut.conj_apply, inv_inv]
    group

private theorem mem_Gw_expand {u : ℤ} {z : G} (hz : z ∈ t.Gw u (u + 1))
    (hzK : z ∈ normalizer (t.K : Set G)) : z ∈ t.Gw (u - 1) (u + 2) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' u
  · let g : G := (t.x₂ * t.x₁) ^ (-k)
    let z' : G := g * z * g⁻¹
    have hz' : z' ∈ t.Gw 0 1 := by
      have hmap : (t.Gw (2 * k) (2 * k + 1)).map (MulAut.conj g).toMonoidHom =
          t.Gw 0 1 := by
        rw [t.Gw_map_tau]
        congr 1 <;> ring
      rw [← hmap]
      exact (mem_map_conj_iff (K := t.Gw (2 * k) (2 * k + 1)) (g := g) (y := z')).mpr (by
        simpa [z', g, mul_assoc] using hz)
    have hz'K : z' ∈ normalizer (t.K : Set G) := by
      have hτ : t.x₂ * t.x₁ ∈ normalizer (t.K : Set G) := t.track.tau_mem_normalizer
      simp only [z', g]
      exact mul_mem (mul_mem (zpow_mem hτ (-k)) hzK) (inv_mem (zpow_mem hτ (-k)))
    obtain ⟨hneg, htwo⟩ := t.mem_Gv_of_mem_Gw_zero_one hz' hz'K
    have hneg' : z ∈ t.Gv (2 * k - 1) := by
      have hmap : (t.Gv (2 * k - 1)).map (MulAut.conj g).toMonoidHom = t.Gv (-1) := by
        rw [t.Gv_map_tau]
        congr 1
        ring
      have h := mem_of_mem_of_map_conj hmap hneg
      convert h using 1
      simp only [z', g, MulAut.conj_apply, inv_inv]
      group
    have htwo' : z ∈ t.Gv (2 * k + 2) := by
      have hmap : (t.Gv (2 * k + 2)).map (MulAut.conj g).toMonoidHom = t.Gv 2 := by
        rw [t.Gv_map_tau]
        congr 1
        ring
      have h := mem_of_mem_of_map_conj hmap htwo
      convert h using 1
      simp only [z', g, MulAut.conj_apply, inv_inv]
      group
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = 2 * k - 1 ∨ i = 2 * k ∨ i = 2 * k + 1 ∨ i = 2 * k + 2 by omega)
      with rfl | rfl | rfl | rfl
    · exact hneg'
    · exact mem_win_iff.mp hz (2 * k) (by omega) (by omega)
    · exact mem_win_iff.mp hz (2 * k + 1) (by omega) (by omega)
    · exact htwo'
  · let g : G := (t.x₂ * t.x₁) ^ (-k)
    let z' : G := g * z * g⁻¹
    have hz' : z' ∈ t.Gw 1 2 := by
      have hmap : (t.Gw (2 * k + 1) (2 * k + 1 + 1)).map (MulAut.conj g).toMonoidHom =
          t.Gw 1 2 := by
        rw [t.Gw_map_tau]
        congr 1 <;> ring
      rw [← hmap]
      exact (mem_map_conj_iff (K := t.Gw (2 * k + 1) (2 * k + 1 + 1)) (g := g)
        (y := z')).mpr (by simpa [z', g, mul_assoc] using hz)
    have hz'K : z' ∈ normalizer (t.K : Set G) := by
      have hτ : t.x₂ * t.x₁ ∈ normalizer (t.K : Set G) := t.track.tau_mem_normalizer
      simp only [z', g]
      exact mul_mem (mul_mem (zpow_mem hτ (-k)) hzK) (inv_mem (zpow_mem hτ (-k)))
    obtain ⟨hzero, hthree⟩ := t.mem_Gv_of_mem_Gw_one_two hz' hz'K
    have hzero' : z ∈ t.Gv (2 * k) := by
      have hmap : (t.Gv (2 * k)).map (MulAut.conj g).toMonoidHom = t.Gv 0 := by
        rw [t.Gv_map_tau]
        congr 1
        ring
      have h := mem_of_mem_of_map_conj hmap hzero
      convert h using 1
      simp only [z', g, MulAut.conj_apply, inv_inv]
      group
    have hthree' : z ∈ t.Gv (2 * k + 3) := by
      have hmap : (t.Gv (2 * k + 3)).map (MulAut.conj g).toMonoidHom = t.Gv 3 := by
        rw [t.Gv_map_tau]
        congr 1
        ring
      have h := mem_of_mem_of_map_conj hmap hthree
      convert h using 1
      simp only [z', g, MulAut.conj_apply, inv_inv]
      group
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = 2 * k ∨ i = 2 * k + 1 ∨ i = 2 * k + 2 ∨ i = 2 * k + 3 by omega)
      with rfl | rfl | rfl | rfl
    · exact hzero'
    · exact mem_win_iff.mp hz (2 * k + 1) (by omega) (by omega)
    · exact mem_win_iff.mp hz (2 * k + 2) (by omega) (by omega)
    · exact hthree'

private theorem mem_Gw_expand_arc {a b : ℤ} {z : G} (hab : a < b)
    (hz : z ∈ t.Gw a b) (hzK : z ∈ normalizer (t.K : Set G)) :
    z ∈ t.Gw (a - 1) (b + 1) := by
  let u : ℤ := b - 1
  have hu : u + 1 = b := by omega
  have hleft : z ∈ t.Gw a (a + 1) := win_mono le_rfl (by omega) hz
  have hright : z ∈ t.Gw u (u + 1) := by
    rw [hu]
    exact win_mono (by omega) le_rfl hz
  have hL : z ∈ t.Gw (a - 1) (a + 2) := t.mem_Gw_expand (u := a) hleft hzK
  have hR := t.mem_Gw_expand (u := u) hright hzK
  have hla : z ∈ t.Gv (a - 1) := mem_win_iff.mp hL (a - 1) le_rfl (by omega)
  have hrb : z ∈ t.Gv (b + 1) := mem_win_iff.mp hR (b + 1) (by omega) (by omega)
  change z ∈ win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (a - 1) (b + 1)
  rw [win_sub_one_left (a := a) (b := b + 1) (by omega),
    win_add_one_right (a := a) (b := b) (by omega)]
  exact ⟨hla, hz, hrb⟩

theorem mem_GT_of_mem_normalizer {v : ℤ} {z : G} (hz : z ∈ t.Gw v (v + 1))
    (hzK : z ∈ normalizer (t.K : Set G)) : z ∈ t.GT := by
  have key : ∀ n : ℕ, z ∈ t.Gw (v - n) (v + 1 + n) := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
        have h := t.mem_Gw_expand_arc (a := v - (n : ℤ)) (b := v + 1 + (n : ℤ))
          (by omega) ih hzK
        have h' : z ∈ t.Gw (v - ((n : ℤ) + 1)) (v + 1 + ((n : ℤ) + 1)) := by
          rw [show v - ((n : ℤ) + 1) = (v - (n : ℤ)) - 1 by ring,
              show v + 1 + ((n : ℤ) + 1) = (v + 1 + (n : ℤ)) + 1 by ring]
          exact h
        simpa only [Nat.cast_add, Nat.cast_one] using h'
  change z ∈ ⨅ i : ℤ, t.Gv i
  rw [mem_iInf]
  intro i
  by_cases hi : v ≤ i
  · let n : ℕ := (i - v).toNat
    have hn : (n : ℤ) = i - v := Int.toNat_of_nonneg (by omega)
    have h := mem_win_iff.mp (key n) i (by rw [hn]; omega) (by rw [hn]; omega)
    change z ∈ t.Gv i at h
    exact h
  · let n : ℕ := (v - i).toNat
    have hn : (n : ℤ) = v - i := Int.toNat_of_nonneg (by omega)
    have h := mem_win_iff.mp (key n) i (by rw [hn]; omega) (by rw [hn]; omega)
    change z ∈ t.Gv i at h
    exact h

theorem exists_isMaxArc {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hO4 : t.GT = t.K) : ∃ ε : ℤ, ∃ n : ℕ, t.IsMaxArc ε n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ℕ → ℕ := fun M => Nat.card (t.Gw (-(M : ℤ)) (M : ℤ))
  have hex : ∃ k, ∃ M, f M = k := ⟨f 0, 0, rfl⟩
  obtain ⟨M₀, hM₀⟩ := Nat.find_spec hex
  have hM₀min : ∀ M, f M₀ ≤ f M := by
    intro M
    rw [hM₀]
    change Nat.find hex ≤ f M
    exact Nat.find_min' (p := fun k => ∃ M, f M = k) (H := hex) ⟨M, rfl⟩
  have hGK : t.Gw (-(M₀ : ℤ)) (M₀ : ℤ) = t.K := by
    refine le_antisymm ?_ (t.K_le_Gw _ _)
    rw [← hO4]
    intro z hz
    change z ∈ ⨅ i : ℤ, t.Gv i
    rw [mem_iInf]
    intro i
    let M : ℕ := max M₀ i.natAbs
    have hM : M₀ ≤ M := le_max_left _ _
    have hMi : -(M : ℤ) ≤ i ∧ i ≤ (M : ℤ) := by
      have h1 : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
      have h2 : -i ≤ (i.natAbs : ℤ) := by
        simpa using Int.le_natAbs (a := -i)
      have h3 : (i.natAbs : ℤ) ≤ (M : ℤ) := by exact_mod_cast le_max_right M₀ i.natAbs
      constructor <;> omega
    have hmono : t.Gw (-(M : ℤ)) (M : ℤ) ≤ t.Gw (-(M₀ : ℤ)) (M₀ : ℤ) :=
      win_mono (by omega) (by omega)
    have heq : t.Gw (-(M : ℤ)) (M : ℤ) = t.Gw (-(M₀ : ℤ)) (M₀ : ℤ) :=
      Subgroup.eq_of_le_of_card_ge hmono (hM₀min M)
    have hzM : z ∈ t.Gw (-(M : ℤ)) (M : ℤ) := by
      rw [heq]
      exact hz
    have hmem := mem_win_iff.mp hzM i hMi.1 hMi.2
    change z ∈ t.Gv i at hmem
    exact hmem
  have hpcK : pCoreOf 2 (t.Gw (-(M₀ : ℤ)) (M₀ : ℤ)) = ⊥ := by
    rw [hGK]
    have hKodd : ¬ 2 ∣ Nat.card ↥(t.K) := t.hHall.2.1.not_two_dvd_nat
    have hdisj := TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hKodd
      (pCoreOf_isPGroup 2 (t.K))
    have h := disjoint_iff.mp hdisj
    rwa [inf_eq_right.mpr (pCoreOf_le 2 (t.K))] at h
  have hM₀pos : 0 < M₀ := by
    rcases Nat.eq_zero_or_pos M₀ with h0 | h0
    · exfalso
      have hpc0 : pCoreOf 2 (t.Gw 0 0) = ⊥ := by simpa [h0] using hpcK
      have hQ : t.Qv 0 = ⊥ := by
        rw [t.Qv_eq 0, show t.Gv 0 = t.Gw 0 0 from (win_self 0).symm, hpc0]
      exact t.Qv_ne_bot hfr.hF 0 hQ
    · exact h0
  have hlong : ∀ a b : ℤ, 2 * (M₀ : ℤ) < b - a → pCoreOf 2 (t.Gw a b) = ⊥ := by
    intro a b hab
    have hd : 1 ≤ (b - a) - 2 * (M₀ : ℤ) := by omega
    let R : ℤ := (M₀ : ℤ) - b
    have hexk : ∃ t : ℤ, Even t ∧ R ≤ t ∧ t ≤ -(M₀ : ℤ) - a := by
      by_cases hR : Even R
      · exact ⟨R, hR, le_rfl, by omega⟩
      · exact ⟨R + 1, Int.even_add_one.mpr hR, by omega, by omega⟩
    obtain ⟨s, hs, hsR, hsL⟩ := hexk
    obtain ⟨k, hk⟩ := hs
    have hk2 : 2 * k = s := by rw [hk]; ring
    have hleft : a + 2 * k ≤ -(M₀ : ℤ) := by rw [hk2]; omega
    have hright : (M₀ : ℤ) ≤ b + 2 * k := by rw [hk2]; omega
    have hX := pCoreOf_isPGroup 2 (t.Gw a b)
    have hXmap : IsPGroup 2 ↥((pCoreOf 2 (t.Gw a b)).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) := hX.map _
    have hleWin : (pCoreOf 2 (t.Gw a b)).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom ≤ t.Gw (-(M₀ : ℤ)) (M₀ : ℤ) :=
      calc (pCoreOf 2 (t.Gw a b)).map
            (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom
          ≤ (t.Gw a b).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom :=
            Subgroup.map_mono (pCoreOf_le 2 (t.Gw a b))
        _ = t.Gw (a + 2 * k) (b + 2 * k) := t.Gw_map_tau a b k
        _ ≤ t.Gw (-(M₀ : ℤ)) (M₀ : ℤ) := win_mono (by omega) (by omega)
    have hlePC := t.le_pCoreOf_Gw hfr (show -(M₀ : ℤ) < (M₀ : ℤ) by omega) hXmap hleWin
    have hmapbot : (pCoreOf 2 (t.Gw a b)).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = ⊥ :=
      le_bot_iff.mp (hlePC.trans_eq hpcK)
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp hmapbot
  let P : ℕ → Prop := fun n => ∃ ε : ℤ, pCoreOf 2 (t.Gw ε (ε + n)) ≠ ⊥
  have hP0 : P 0 := by
    refine ⟨0, ?_⟩
    have h1 : pCoreOf 2 (t.Gw 0 0) = t.Qv 0 := by
      rw [show t.Gw 0 0 = t.Gv 0 from win_self 0, ← t.Qv_eq 0]
    simpa using h1 ▸ t.Qv_ne_bot hfr.hF 0
  let n₀ : ℕ := Nat.findGreatest P (2 * M₀)
  have hn₀ : P n₀ := Nat.findGreatest_spec (P := P) (m := 0) (by omega) hP0
  obtain ⟨ε₀, hε₀⟩ := hn₀
  refine ⟨ε₀, n₀, hε₀, ?_⟩
  intro a b hab
  have hm_nonneg : 0 ≤ b - a := by omega
  let m : ℕ := Int.toNat (b - a)
  have hm : (m : ℤ) = b - a := Int.toNat_of_nonneg hm_nonneg
  have hnm : n₀ < m := by omega
  have hnotP : ¬ P m := by
    by_cases hmn : m ≤ 2 * M₀
    · intro hPm
      have hle := Nat.le_findGreatest hmn hPm
      omega
    · intro hPm
      obtain ⟨e, he⟩ := hPm
      exact he (hlong e (e + (m : ℤ)) (by omega))
  by_contra hne
  exact hnotP ⟨a, by simpa [hm] using hne⟩

theorem IsMaxArc.two_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) : 2 ≤ n := by
  by_contra hlt
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : pCoreOf 2 (t.Gw (-1) 1) = ⊥ := h.pCoreOf_eq_bot (-1) 1 (by omega)
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hfr.hF)
  have hQ1B : Q1 L1 L2 S ≤ bigB L1 L2 S :=
    hQ1S.trans (le_sup_right : S ≤ bigB L1 L2 S)
  have hQ1P2 : Q1 L1 L2 S ≤ P2 L1 L2 S :=
    hQ1B.trans (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)
  have hle : Q1 L1 L2 S ≤ t.Gw (-1) 1 := by
    intro q hq
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = -1 ∨ i = 0 ∨ i = 1 by omega) with rfl | rfl | rfl
    · refine (t.track.mem_qv_neg_iff (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        Subgroup.le_normalizer Subgroup.le_normalizer (-1)).mpr ?_
      rw [neg_neg]
      change t.x₁⁻¹ * q * t.x₁ ∈ t.Gv 1
      rw [t.Gv_one]
      have hx₁ : t.x₁⁻¹ ∈ normalizer (Q1 L1 L2 S : Set G) :=
        inv_mem (le_normalizer_pCoreOf 2 (P1 L1 L2 S) t.track.x₁_mem)
      have hq' : t.x₁⁻¹ * q * t.x₁ ∈ Q1 L1 L2 S := by
        have := (Subgroup.mem_normalizer_iff.mp hx₁ q).mp hq
        simpa using this
      exact hQ1P2 hq'
    · change q ∈ t.Gv 0
      rw [t.Gv_zero]
      exact pCoreOf_le 2 (P1 L1 L2 S) hq
    · change q ∈ t.Gv 1
      rw [t.Gv_one]
      exact hQ1P2 hq
  have hQ1pc : Q1 L1 L2 S ≤ pCoreOf 2 (t.Gw (-1) 1) :=
    t.le_pCoreOf_Gw hfr (by norm_num) (pCoreOf_isPGroup 2 (P1 L1 L2 S)) hle
  have hne : pCoreOf 2 (t.Gw (-1) 1) ≠ ⊥ := by
    intro hb
    have hQ1bot : Q1 L1 L2 S = ⊥ := le_bot_iff.mp (hQ1pc.trans_eq hb)
    have hQ1ne : Q1 L1 L2 S ≠ ⊥ := by
      rw [show Q1 L1 L2 S = t.Qv 0 from t.Qv_zero.symm]
      exact t.Qv_ne_bot hfr.hF 0
    exact hQ1ne hQ1bot
  exact hne hbot

theorem IsMaxArc.reflect {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) (v : ℤ) :
    t.IsMaxArc (2 * v - ε - n) n := by
  obtain ⟨y, -, -, hwin, -, -⟩ := t.exists_reflection v
  constructor
  · intro hbot
    apply h.pCoreOf_ne_bot
    have h1 : (pCoreOf 2 (t.Gw ε (ε + n))).map (MulAut.conj y).toMonoidHom = ⊥ := by
      rw [← pCoreOf_map_mulEquiv 2 (MulAut.conj y) (t.Gw ε (ε + n)), hwin ε (ε + n)]
      convert hbot using 2 <;> ring
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj y).injective).mp h1
  · intro a b hab
    have h0 : pCoreOf 2 (t.Gw (2 * v - b) (2 * v - a)) = ⊥ :=
      h.pCoreOf_eq_bot (2 * v - b) (2 * v - a) (by omega)
    have hmap : (t.Gw (2 * v - b) (2 * v - a)).map (MulAut.conj y).toMonoidHom =
        t.Gw a b := by
      rw [hwin (2 * v - b) (2 * v - a)]
      congr 1 <;> ring
    rw [← hmap,
      pCoreOf_map_mulEquiv 2 (MulAut.conj y) (t.Gw (2 * v - b) (2 * v - a)), h0,
      Subgroup.map_bot]

theorem IsMaxArc.shift {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) (k : ℤ) :
    t.IsMaxArc (ε + 2 * k) n := by
  constructor
  · intro hbot
    apply h.pCoreOf_ne_bot
    have h1 : (pCoreOf 2 (t.Gw ε (ε + n))).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = ⊥ := by
      rw [← pCoreOf_map_mulEquiv 2 (MulAut.conj ((t.x₂ * t.x₁) ^ k)) (t.Gw ε (ε + n)),
        t.Gw_map_tau]
      convert hbot using 2 <;> ring
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp h1
  · intro a b hab
    have h0 : pCoreOf 2 (t.Gw (a - 2 * k) (b - 2 * k)) = ⊥ :=
      h.pCoreOf_eq_bot (a - 2 * k) (b - 2 * k) (by omega)
    have hmap : (t.Gw (a - 2 * k) (b - 2 * k)).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Gw a b := by
      rw [t.Gw_map_tau]
      congr 1 <;> ring
    rw [← hmap,
      pCoreOf_map_mulEquiv 2 (MulAut.conj ((t.x₂ * t.x₁) ^ k))
        (t.Gw (a - 2 * k) (b - 2 * k)), h0, Subgroup.map_bot]

theorem IsMaxArc.inf_Gv_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {n : ℕ} (h : t.IsMaxArc ε n) :
    pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε - 1) = ⊥ ∧
      pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε + n + 1) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · have hX : IsPGroup 2 ↥(pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε - 1)) :=
      (pCoreOf_isPGroup 2 _).to_le inf_le_left
    have hXw : pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε - 1) ≤ t.Gw (ε - 1) (ε + n) := by
      change pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε - 1) ≤
        win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (ε - 1) (ε + n)
      rw [win_sub_one_left (a := ε) (b := ε + n) (by omega)]
      exact le_inf inf_le_right (inf_le_left.trans (pCoreOf_le 2 _))
    have hpc := t.le_pCoreOf_Gw hfr (show ε - 1 < ε + n by omega) hX hXw
    exact le_bot_iff.mp (hpc.trans_eq (h.pCoreOf_eq_bot (ε - 1) (ε + n) (by omega)))
  · have hX : IsPGroup 2 ↥(pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε + n + 1)) :=
      (pCoreOf_isPGroup 2 _).to_le inf_le_left
    have hXw : pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε + n + 1) ≤ t.Gw ε (ε + n + 1) := by
      change pCoreOf 2 (t.Gw ε (ε + n)) ⊓ t.Gv (ε + n + 1) ≤
        win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ ε (ε + n + 1)
      rw [show ε + n + 1 = (ε + n) + 1 by ring,
        win_add_one_right (a := ε) (b := ε + n) (by omega)]
      exact le_inf (inf_le_left.trans (pCoreOf_le 2 _)) inf_le_right
    have hpc := t.le_pCoreOf_Gw hfr (show ε < ε + n + 1 by omega) hX hXw
    exact le_bot_iff.mp (hpc.trans_eq (h.pCoreOf_eq_bot ε (ε + n + 1) (by omega)))

theorem exists_isFixRadius {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hO4 : t.GT = t.K) (v : ℤ) : ∃ b : ℕ, t.IsFixRadius v b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε, n, hγ⟩ := t.exists_isMaxArc hfr hO4
  classical
  let P : ℕ → Prop := fun b => t.Zv v ≤ t.Gw (v - b) (v + b)
  have hP0 : P 0 := by
    change t.Zv v ≤ t.Gw (v - ((0 : ℕ) : ℤ)) (v + ((0 : ℕ) : ℤ))
    simpa [win_self] using (t.Zv_le_Qv v).trans (t.Qv_le_Gv_self v)
  let b : ℕ := Nat.findGreatest P n
  have hPb : P b := Nat.findGreatest_spec (m := 0) (by omega) hP0
  refine ⟨b, hPb, ?_⟩
  intro hle
  obtain ⟨y, hyv, -, hwin, -, -⟩ := t.exists_reflection v
  have hZy : (t.Zv v).map (MulAut.conj y).toMonoidHom = t.Zv v :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.Gv_le_normalizer_Zv v hyv)
  have hGy : (t.Gv (v + (b : ℤ) + 1)).map (MulAut.conj y).toMonoidHom =
      t.Gv (v - (b : ℤ) - 1) := by
    have hi := hwin (v + (b : ℤ) + 1) (v + (b : ℤ) + 1)
    rw [show t.Gw (v + (b : ℤ) + 1) (v + (b : ℤ) + 1) =
        t.Gv (v + (b : ℤ) + 1) from win_self _,
      show 2 * v - (v + (b : ℤ) + 1) = v - (b : ℤ) - 1 by ring,
      show t.Gw (v - (b : ℤ) - 1) (v - (b : ℤ) - 1) =
        t.Gv (v - (b : ℤ) - 1) from win_self _] at hi
    exact hi
  have hGle : t.Zv v ≤ t.Gv (v - (b : ℤ) - 1) := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hle
    rwa [hZy, hGy] at hmap
  have hPsucc : P (b + 1) := by
    change t.Zv v ≤ t.Gw (v - (((b + 1 : ℕ) : ℤ))) (v + (((b + 1 : ℕ) : ℤ)))
    intro z hz
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = v - ((b : ℤ) + 1) ∨ ((v - (b : ℤ) ≤ i) ∧ i ≤ v + (b : ℤ))
        ∨ i = v + (b : ℤ) + 1 by omega) with hi | ⟨h1', h2'⟩ | hi
    · rw [hi]
      convert hGle hz using 1
      ring
    · exact mem_win_iff.mp (hPb hz) i h1' h2'
    · rw [hi]
      exact hle hz
  by_cases hbn : b + 1 ≤ n
  · exact (Nat.findGreatest_is_greatest (by omega) hbn) hPsucc
  · have hbn' : n < b + 1 := by omega
    have hb_eq : b = n := le_antisymm (Nat.findGreatest_le n) (by omega)
    have hpc : pCoreOf 2 (t.Gw (v - ((n : ℤ) + 1)) (v + ((n : ℤ) + 1))) = ⊥ :=
      hγ.pCoreOf_eq_bot (v - ((n : ℤ) + 1)) (v + ((n : ℤ) + 1)) (by omega)
    have hZle : t.Zv v ≤ pCoreOf 2 (t.Gw (v - ((n : ℤ) + 1)) (v + ((n : ℤ) + 1))) :=
      t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv v) (by
        simpa [P, hb_eq, Nat.cast_add, Nat.cast_one] using hPsucc)
    exact t.Zv_ne_bot hfr.hF v (le_bot_iff.mp (hZle.trans_eq hpc))

theorem IsFixRadius.shift {v : ℤ} {b : ℕ} (h : t.IsFixRadius v b) (k : ℤ) :
    t.IsFixRadius (v + 2 * k) b := by
  constructor
  · rw [show v + 2 * k - b = (v - b) + 2 * k by push_cast; ring,
      show v + 2 * k + b = (v + b) + 2 * k by push_cast; ring,
      ← t.Gw_map_tau (v - b) (v + b) k, ← t.Zv_map_tau v k]
    exact Subgroup.map_mono h.le_Gw
  · intro hle
    apply h.not_le_Gv
    have hle' : (t.Zv v).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom ≤
        (t.Gv (v + b + 1)).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
      rw [t.Zv_map_tau, t.Gv_map_tau]
      convert hle using 2 <;> ring
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj _).injective).mp hle'

theorem IsFixRadius.not_le_Gv_sub {v : ℤ} {b : ℕ} (h : t.IsFixRadius v b) :
    ¬ t.Zv v ≤ t.Gv (v - b - 1) := by
  intro hle
  obtain ⟨y, hyv, -, hwin, -, -⟩ := t.exists_reflection v
  apply h.not_le_Gv
  have hZy : (t.Zv v).map (MulAut.conj y).toMonoidHom = t.Zv v :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.Gv_le_normalizer_Zv v hyv)
  have hGy : (t.Gv (v - b - 1)).map (MulAut.conj y).toMonoidHom = t.Gv (v + b + 1) := by
    have hi := hwin (v - b - 1) (v - b - 1)
    rw [show t.Gw (v - b - 1) (v - b - 1) = t.Gv (v - b - 1) from win_self _,
      show 2 * v - (v - b - 1) = v + b + 1 by push_cast; ring,
      show t.Gw (v + b + 1) (v + b + 1) = t.Gv (v + b + 1) from win_self _] at hi
    exact hi
  have hmap := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hle
  rwa [hZy, hGy] at hmap

theorem IsFixRadius.one_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {v : ℤ} {b : ℕ} (h : t.IsFixRadius v b) : 1 ≤ b := by
  by_contra hlt
  have hb : b = 0 := by omega
  subst b
  have hQ1P2 : Q1 L1 L2 S ≤ P2 L1 L2 S :=
    (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hfr.hF)).trans
      ((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S))
  have hQ2P1 : Q2 L1 L2 S ≤ P1 L1 L2 S :=
    (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.hF)).trans
      ((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S))
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · have h0 : t.IsFixRadius 0 0 := by
      simpa [show 2 * k + 2 * (-k) = 0 by ring] using IsFixRadius.shift t h (-k)
    apply h0.not_le_Gv
    have hZ : t.Zv 0 ≤ P2 L1 L2 S :=
      (t.Zv_le_Qv 0).trans (by rw [t.Qv_zero]; exact hQ1P2)
    simpa [t.Gv_one] using hZ
  · have h1 : t.IsFixRadius 1 0 := by
      simpa [show 2 * k + 1 + 2 * (-k) = 1 by ring] using IsFixRadius.shift t h (-k)
    apply h1.not_le_Gv_sub
    have hZ : t.Zv 1 ≤ P1 L1 L2 S :=
      (t.Zv_le_Qv 1).trans (by rw [t.Qv_one]; exact hQ2P1)
    simpa [t.Gv_zero] using hZ

theorem IsFixRadius.two_mul_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε v : ℤ} {n b : ℕ} (hγ : t.IsMaxArc ε n)
    (h : t.IsFixRadius v b) : 2 * b ≤ n := by
  by_contra hlt
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · omega
    · exact h0
  have hpc : pCoreOf 2 (t.Gw (v - b) (v + b)) = ⊥ :=
    hγ.pCoreOf_eq_bot (v - b) (v + b) (by omega)
  have hle : t.Zv v ≤ pCoreOf 2 (t.Gw (v - b) (v + b)) :=
    t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv v) h.le_Gw
  exact t.Zv_ne_bot hfr.hF v (le_bot_iff.mp (hle.trans_eq hpc))

theorem IsFixRadius.commutator_le_inf_or {ε : ℤ} {b₀ b₁ : ℕ} (h₀ : t.IsFixRadius ε b₀)
    (h₁ : t.IsFixRadius (ε + 1) b₁) :
    ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁) ∨
      (¬ t.Zv (ε + 1 + b₁) ≤ t.Gv (ε + 1) ∧ Odd b₁ ∧ b₀ < b₁) := by
  by_cases hB : t.Zv (ε + 1 + b₁) ≤ t.Gv (ε + 1)
  · left
    have hA : t.Zv (ε + 1) ≤ t.Gv (ε + 1 + b₁) := by
      have h := h₁.le_Gw
      have := h.trans (win_mono (a := (ε + 1) - b₁) (b := (ε + 1) + b₁)
        (a' := ε + 1 + b₁) (b' := ε + 1 + b₁) (by omega) (by omega))
      simpa [win_self] using this
    have hAnB : t.Zv (ε + 1) ≤ normalizer (t.Zv (ε + 1 + b₁) : Set G) :=
      hA.trans (t.Gv_le_normalizer_Zv _)
    have hBnA : t.Zv (ε + 1 + b₁) ≤ normalizer (t.Zv (ε + 1) : Set G) :=
      hB.trans (t.Gv_le_normalizer_Zv _)
    exact le_inf
      ((Subgroup.le_normalizer_iff_commutator_le_left (H := t.Zv (ε + 1 + b₁))
        (K := t.Zv (ε + 1))).mp hBnA)
      ((Subgroup.le_normalizer_iff_commutator_le_right (H := t.Zv (ε + 1))
        (K := t.Zv (ε + 1 + b₁))).mp hAnB)
  · right
    refine ⟨hB, ?_⟩
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' (b₁ : ℤ)
    · exfalso
      have hshift := IsFixRadius.shift t h₁ k
      have hv : (ε + 1) + 2 * k = ε + 1 + (b₁ : ℤ) := by rw [hk]
      rw [hv] at hshift
      have hle : t.Zv (ε + 1 + (b₁ : ℤ)) ≤ t.Gv (ε + 1) := by
        have h := hshift.le_Gw
        have hw := h.trans (win_mono
          (a := (ε + 1 + (b₁ : ℤ)) - (b₁ : ℤ))
          (b := (ε + 1 + (b₁ : ℤ)) + (b₁ : ℤ))
          (a' := ε + 1) (b' := ε + 1) (by omega) (by omega))
        simpa [win_self] using hw
      exact hB hle
    · refine ⟨?_, ?_⟩
      · have hb1odd : Odd (b₁ : ℤ) := by
          rw [hk]
          exact ⟨k, by ring⟩
        exact (Int.odd_coe_nat (n := b₁)).mp hb1odd
      · by_contra hle
        have hb1le : b₁ ≤ b₀ := by omega
        have hshift := IsFixRadius.shift t h₀ (k + 1)
        have hv : ε + 2 * (k + 1) = ε + 1 + (b₁ : ℤ) := by rw [hk]; ring
        rw [hv] at hshift
        have hleGv : t.Zv (ε + 1 + (b₁ : ℤ)) ≤ t.Gv (ε + 1) := by
          have h := hshift.le_Gw
          have hw := h.trans (win_mono
            (a := (ε + 1 + (b₁ : ℤ)) - (b₀ : ℤ))
            (b := (ε + 1 + (b₁ : ℤ)) + (b₀ : ℤ))
            (a' := ε + 1) (b' := ε + 1) (by omega) (by omega))
          simpa [win_self] using hw
        exact hB hleGv
end Track

end CFSG.Quasithin.Stroth.Rq

end
