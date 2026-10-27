module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Defs
import all CFSG.Fischer.F4
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34

open CFSG.Fischer

theorem pow_three_eq_zero_of_isNilpotent' {K : Type*} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (h : IsNilpotent N) : N ^ 3 = 0 := by
  have hc : N.charpoly = Polynomial.X ^ 3 := by
    have := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h).eq_zero
    rw [sub_eq_zero, Fintype.card_fin] at this
    exact this
  have := Matrix.aeval_self_charpoly N
  rw [hc, map_pow, Polynomial.aeval_X] at this
  exact this

theorem pow_four_eq_one_of_pow_two_pow (M : Matrix (Fin 3) (Fin 3) F4) (k : ℕ)
    (hM : M ^ 2 ^ k = 1) : M ^ 4 = 1 := by
  set N : Matrix (Fin 3) (Fin 3) F4 := M - 1 with hN
  have hMN : M = N + 1 := by rw [hN, sub_add_cancel]
  have hNk : N ^ 2 ^ k = 0 := by
    have h1 : (N + 1) ^ 2 ^ k = N ^ 2 ^ k + 1 := by
      rw [add_pow_char_pow_of_commute (p := 2) (n := k) (h := Commute.one_right N), one_pow]
    rw [← hMN, hM] at h1
    simp at h1
    exact h1
  have hN3 : N ^ 3 = 0 := pow_three_eq_zero_of_isNilpotent' ⟨2 ^ k, hNk⟩
  have hN4 : N ^ 2 ^ 2 = 0 := by
    rw [show (2 : ℕ) ^ 2 = 3 + 1 from rfl, pow_succ, hN3, zero_mul]
  rw [hMN, show (4 : ℕ) = 2 ^ 2 from rfl,
    add_pow_char_pow_of_commute (p := 2) (n := 2) (h := Commute.one_right N), one_pow, hN4,
    zero_add]

@[expose] def matImage (T : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) :
    Set (Matrix (Fin 3) (Fin 3) F4) :=
  {M | ∃ g ∈ T, (g : Matrix (Fin 3) (Fin 3) F4) = M}

theorem matImage_mul {T : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)}
    {a b : Matrix (Fin 3) (Fin 3) F4} (ha : a ∈ matImage T) (hb : b ∈ matImage T) :
    a * b ∈ matImage T := by
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨h, hh, rfl⟩ := hb
  exact ⟨g * h, T.mul_mem hg hh, Units.val_mul g h⟩

theorem matImage_pow_four {T : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)}
    (hT2 : IsPGroup 2 T) {M : Matrix (Fin 3) (Fin 3) F4} (hM : M ∈ matImage T) : M ^ 4 = 1 := by
  obtain ⟨g, hg, rfl⟩ := hM
  obtain ⟨k, hk⟩ := hT2 ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simp at this
    exact this
  apply pow_four_eq_one_of_pow_two_pow _ k
  rw [← Units.val_pow_eq_pow_val, hk', Units.val_one]

theorem exists_good_involution (X : Matrix.GeneralLinearGroup (Fin 3) F4)
    (hX : (X : Matrix (Fin 3) (Fin 3) F4) = Xd)
    (T : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hXT : X ∈ Subgroup.normalizer (T : Set (Matrix.GeneralLinearGroup (Fin 3) F4))) :
    ∃ t ∈ T, Good3 (t : Matrix (Fin 3) (Fin 3) F4) := by
  haveI : Finite (Matrix.GeneralLinearGroup (Fin 3) F4) :=
    Finite.of_injective (fun u : Matrix.GeneralLinearGroup (Fin 3) F4 =>
      (u : Matrix (Fin 3) (Fin 3) F4)) (fun a b h => Units.ext h)
  have hnt : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card (p := 2) (G := T) hT2).mp hnt
  obtain ⟨t0, ht0⟩ := exists_prime_orderOf_dvd_card' (G := T) 2
    (by rw [hcard]; exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn))
  obtain ⟨t, htT, htord⟩ : ∃ t ∈ T, orderOf t = 2 :=
    ⟨(t0 : Matrix.GeneralLinearGroup (Fin 3) F4), t0.2, by rw [Subgroup.orderOf_coe]; exact ht0⟩
  have ht2 : t ^ 2 = 1 := by rw [← htord]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    norm_num at htord
  have hnorm := Subgroup.mem_normalizer_iff.mp hXT
  have hc1 : X * t * X⁻¹ ∈ T := (hnorm t).mp htT
  have hc2 : X⁻¹ * t * X ∈ T := by
    apply (hnorm (X⁻¹ * t * X)).mpr
    rw [show X * (X⁻¹ * t * X) * X⁻¹ = t by group]
    exact htT
  have hXinv : ((X⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = Xd2 := by
    have h1 : (X : Matrix (Fin 3) (Fin 3) F4) *
        ((X⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : Xd2 * Xd = 1 := by decide
    calc ((X⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
        = (Xd2 * Xd) * ((X⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) := by
          rw [h2, one_mul]
      _ = Xd2 * ((X : Matrix (Fin 3) (Fin 3) F4) *
            ((X⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) := by
          rw [hX, mul_assoc]
      _ = Xd2 := by rw [h1, mul_one]
  have hm1 : ((X * t * X⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = Xd * (t : Matrix (Fin 3) (Fin 3) F4) * Xd2 := by
    rw [Units.val_mul, Units.val_mul, hX, hXinv]
  have hm2 : ((X⁻¹ * t * X : Matrix.GeneralLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4) = Xd2 * (t : Matrix (Fin 3) (Fin 3) F4) * Xd := by
    rw [Units.val_mul, Units.val_mul, hX, hXinv]
  refine ⟨t, htT, ?_⟩
  have hL : ∀ a ∈ letters (t : Matrix (Fin 3) (Fin 3) F4), a ∈ matImage T := by
    intro a ha
    simp [letters] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨t, htT, rfl⟩
    · exact ⟨X * t * X⁻¹, hc1, hm1⟩
    · exact ⟨X⁻¹ * t * X, hc2, hm2⟩
  have hW : ∀ w ∈ words3 (t : Matrix (Fin 3) (Fin 3) F4), w ∈ matImage T := by
    intro w hw
    simp only [words3, List.mem_append, List.mem_flatMap, List.mem_map] at hw
    rcases hw with (hw | ⟨a, ha, b, hb, rfl⟩) | ⟨a, ha, b, hb, c, hc, rfl⟩
    · exact hL w hw
    · exact matImage_mul (hL a ha) (hL b hb)
    · exact matImage_mul (matImage_mul (hL a ha) (hL b hb)) (hL c hc)
  unfold Good3 good3
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← Units.val_mul, ← sq, ht2, Units.val_one]
  · intro h
    exact ht1 (Units.ext h)
  · intro w hw
    exact matImage_pow_four hT2 (hW w hw)

end CFSG.RankThree.PartTwo.Sec10.KS1012GL34

end
