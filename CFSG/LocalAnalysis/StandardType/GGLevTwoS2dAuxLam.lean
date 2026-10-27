module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dCoord
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

noncomputable def levTwoS2d_e {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) : ℕ → ZMod p
  | 0 => (c ⟨n - 1, by omega⟩ + c ⟨n - 2, by omega⟩) / (2 : ZMod p)
  | m + 1 => levTwoS2d_e n hn c m + c ⟨n - 3 - m, by omega⟩

noncomputable def levTwoS2d_dNat {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p)
    (m : ℕ) : ZMod p :=
  if h : m + 1 = n then
    (c ⟨n - 1, by omega⟩ - c ⟨n - 2, by omega⟩) / (2 : ZMod p)
  else
    levTwoS2d_e n hn c (n - 2 - m)

noncomputable def levTwoS2d_d {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p)
    (k : Fin n) : ZMod p :=
  levTwoS2d_dNat n hn c k.val

theorem levTwoS2d_e_succ {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) (m : ℕ) :
    levTwoS2d_e n hn c (m + 1) =
      levTwoS2d_e n hn c m + c ⟨n - 3 - m, by omega⟩ := by
  simp only [levTwoS2d_e]

theorem levTwoS2d_dNat_last {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) :
    levTwoS2d_dNat n hn c (n - 1) =
      (c ⟨n - 1, by omega⟩ - c ⟨n - 2, by omega⟩) / (2 : ZMod p) := by
  unfold levTwoS2d_dNat
  rw [dif_pos (by omega)]

theorem levTwoS2d_dNat_nm2 {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) :
    levTwoS2d_dNat n hn c (n - 2) =
      (c ⟨n - 1, by omega⟩ + c ⟨n - 2, by omega⟩) / (2 : ZMod p) := by
  unfold levTwoS2d_dNat
  rw [dif_neg (by omega), show n - 2 - (n - 2) = 0 from by omega]
  rfl

theorem levTwoS2d_dNat_rec {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) (m : ℕ)
    (hm : m + 2 < n) :
    levTwoS2d_dNat n hn c m = levTwoS2d_dNat n hn c (m + 1) + c ⟨m, by omega⟩ := by
  unfold levTwoS2d_dNat
  rw [dif_neg (by omega), dif_neg (by omega)]
  have hidx : n - 2 - m = (n - 3 - m) + 1 := by omega
  have hidx2 : n - 2 - (m + 1) = n - 3 - m := by omega
  rw [hidx, hidx2, levTwoS2d_e_succ]
  congr 1
  apply congrArg c
  apply Fin.ext
  simp only
  omega

theorem levTwoS2d_d_last {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) :
    levTwoS2d_d n hn c ⟨n - 1, by omega⟩ =
      (c ⟨n - 1, by omega⟩ - c ⟨n - 2, by omega⟩) / (2 : ZMod p) :=
  levTwoS2d_dNat_last n hn c

theorem levTwoS2d_d_nm2 {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) :
    levTwoS2d_d n hn c ⟨n - 2, by omega⟩ =
      (c ⟨n - 1, by omega⟩ + c ⟨n - 2, by omega⟩) / (2 : ZMod p) :=
  levTwoS2d_dNat_nm2 n hn c

theorem levTwoS2d_d_rec {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) (k : Fin n)
    (hk : k.val + 2 < n) :
    levTwoS2d_d n hn c k = levTwoS2d_d n hn c ⟨k.val + 1, by omega⟩ + c k := by
  show levTwoS2d_dNat n hn c k.val = levTwoS2d_dNat n hn c (k.val + 1) + c k
  rw [levTwoS2d_dNat_rec n hn c k.val hk]

private theorem levTwoS2d_sum_single_mul {p : ℕ} [Fact p.Prime] (n : ℕ) (d : Fin n → ZMod p)
    (j : Fin n) :
    ∑ k, (Pi.single j (1 : ZMod p) : Fin n → ZMod p) k * d k = d j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro hj; exact absurd (Finset.mem_univ j) hj

private theorem levTwoS2d_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

private theorem levTwoS2d_half_add_sub {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a b : ZMod p) :
    (a + b) / (2 : ZMod p) + (a - b) / (2 : ZMod p) = a := by
  have h2 := levTwoS2d_two_ne_zero hp2
  refine mul_left_cancel₀ h2 ?_
  rw [mul_add, mul_div_cancel₀ _ h2, mul_div_cancel₀ _ h2]
  ring

private theorem levTwoS2d_half_sub {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a b : ZMod p) :
    (a + b) / (2 : ZMod p) - (a - b) / (2 : ZMod p) = b := by
  have h2 := levTwoS2d_two_ne_zero hp2
  refine mul_left_cancel₀ h2 ?_
  rw [mul_sub, mul_div_cancel₀ _ h2, mul_div_cancel₀ _ h2]
  ring

private theorem levTwoS2d_toStdD_single_eq {p : ℕ} [Fact p.Prime] {n : ℕ} (j : Fin n) (hj : j.val + 1 < n) :
    ∀ k, (toStdD n (Pi.single j 1) k : ZMod p) =
      (((Pi.single j (1 : ZMod p) : Fin n → ZMod p) -
        (Pi.single (⟨j.val + 1, hj⟩ : Fin n) (1 : ZMod p) : Fin n → ZMod p)) k) := by
  intro k
  rw [toStdD_single_of_lt n hj]
  simp only [Pi.sub_apply, Pi.single_apply]
  push_cast
  rfl

theorem levTwoS2d_d_single {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (j : Fin n) :
    ∑ k, (toStdD n (Pi.single j 1) k : ZMod p) * levTwoS2d_d n hn c k = c j := by
  by_cases hj2 : j.val + 2 < n
  · have hj1 : j.val + 1 < n := by omega
    rw [show (∑ k, (toStdD n (Pi.single j 1) k : ZMod p) * levTwoS2d_d n hn c k) =
        ∑ k, (((Pi.single j (1 : ZMod p) : Fin n → ZMod p) -
          (Pi.single (⟨j.val + 1, hj1⟩ : Fin n) (1 : ZMod p) : Fin n → ZMod p)) k) *
          levTwoS2d_d n hn c k from
        Finset.sum_congr rfl (fun k _ => by rw [levTwoS2d_toStdD_single_eq j hj1 k])]
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
      levTwoS2d_sum_single_mul n (levTwoS2d_d n hn c) j,
      levTwoS2d_sum_single_mul n (levTwoS2d_d n hn c) ⟨j.val + 1, hj1⟩]
    rw [levTwoS2d_d_rec n hn c j hj2]
    ring
  · by_cases hj1 : j.val + 1 < n
    · have hval : j.val = n - 2 := by omega
      have hj1' : (⟨j.val + 1, hj1⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
        apply Fin.ext; simp only; omega
      rw [show (∑ k, (toStdD n (Pi.single j 1) k : ZMod p) * levTwoS2d_d n hn c k) =
          ∑ k, (((Pi.single j (1 : ZMod p) : Fin n → ZMod p) -
            (Pi.single (⟨j.val + 1, hj1⟩ : Fin n) (1 : ZMod p) : Fin n → ZMod p)) k) *
            levTwoS2d_d n hn c k from
          Finset.sum_congr rfl (fun k _ => by rw [levTwoS2d_toStdD_single_eq j hj1 k])]
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
        levTwoS2d_sum_single_mul n (levTwoS2d_d n hn c) j,
        levTwoS2d_sum_single_mul n (levTwoS2d_d n hn c) ⟨j.val + 1, hj1⟩]
      have hdj : levTwoS2d_d n hn c j =
          (c ⟨n - 1, by omega⟩ + c ⟨n - 2, by omega⟩) / (2 : ZMod p) := by
        change levTwoS2d_dNat n hn c j.val = _
        rw [hval]
        exact levTwoS2d_dNat_nm2 n hn c
      have hdj1 : levTwoS2d_d n hn c ⟨j.val + 1, hj1⟩ =
          (c ⟨n - 1, by omega⟩ - c ⟨n - 2, by omega⟩) / (2 : ZMod p) := by
        rw [hj1']; exact levTwoS2d_d_last n hn c
      rw [hdj, hdj1, levTwoS2d_half_sub hp2]
      apply congrArg c
      apply Fin.ext
      simp only
      omega
    · have hval : j.val = n - 1 := by omega
      have hto : ∀ k, (toStdD n (Pi.single j 1) k : ZMod p) =
          (((Pi.single (⟨n - 2, by omega⟩ : Fin n) (1 : ZMod p) : Fin n → ZMod p) +
            (Pi.single j (1 : ZMod p) : Fin n → ZMod p)) k) := by
        intro k
        rw [toStdD_single_of_not_lt n hj1 (by omega)]
        simp only [Pi.add_apply, Pi.single_apply]
        push_cast
        rfl
      rw [show (∑ k, (toStdD n (Pi.single j 1) k : ZMod p) * levTwoS2d_d n hn c k) =
          ∑ k, (((Pi.single (⟨n - 2, by omega⟩ : Fin n) (1 : ZMod p) : Fin n → ZMod p) +
            (Pi.single j (1 : ZMod p) : Fin n → ZMod p)) k) *
            levTwoS2d_d n hn c k from
          Finset.sum_congr rfl (fun k _ => by rw [hto k])]
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib,
        levTwoS2d_sum_single_mul n (levTwoS2d_d n hn c) ⟨n - 2, by omega⟩,
        levTwoS2d_sum_single_mul n (levTwoS2d_d n hn c) j]
      have hdj : levTwoS2d_d n hn c j =
          (c ⟨n - 1, by omega⟩ - c ⟨n - 2, by omega⟩) / (2 : ZMod p) := by
        change levTwoS2d_dNat n hn c j.val = _
        rw [hval]
        exact levTwoS2d_dNat_last n hn c
      rw [levTwoS2d_d_nm2 n hn c, hdj, levTwoS2d_half_add_sub hp2]
      apply congrArg c
      apply Fin.ext
      simp only
      omega

theorem levTwoS2d_lam_coord {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (v : Fin n → ℤ) :
    lam c v = ∑ k, (toStdD n v k : ZMod p) * levTwoS2d_d n hn c k := by
  let f : (Fin n → ℤ) →+ ZMod p :=
    { toFun := fun v => lam c v
      map_zero' := by simp [lam]
      map_add' := fun u v => by simp [lam, Finset.sum_add_distrib, add_mul] }
  let g : (Fin n → ℤ) →+ ZMod p :=
    { toFun := fun v => ∑ k, (toStdD n v k : ZMod p) * levTwoS2d_d n hn c k
      map_zero' := by simp [toStdD_zero]
      map_add' := fun u v => by
        simp only [toStdD_add, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib] }
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun k x => ?_
    have hs : (Pi.single k x : Fin n → ℤ) = x • Pi.single k 1 := by
      funext j; simp [Pi.single_apply]
    change lam c (Pi.single k x) =
      ∑ j, (toStdD n (Pi.single k x) j : ZMod p) * levTwoS2d_d n hn c j
    have hL : lam c (Pi.single k x) = (x : ZMod p) * c k := by
      simp only [lam]
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    have hR : (∑ j, (toStdD n (Pi.single k x) j : ZMod p) * levTwoS2d_d n hn c j) =
        (x : ZMod p) * c k := by
      have hstep : ∀ j, (toStdD n (Pi.single k x) j : ZMod p) =
          (x : ZMod p) * (toStdD n (Pi.single k 1) j : ZMod p) := by
        intro j
        rw [hs, toStdD_smul]
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      rw [Finset.sum_congr rfl (fun j _ => by rw [hstep j, mul_assoc]), ← Finset.mul_sum]
      congr 1
      exact levTwoS2d_d_single n hn hp2 c k
    rw [hL, hR]
  exact DFunLike.congr_fun hfg v

theorem levTwoS2d_lam_eps {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {v : Fin n → ℤ} {a b : Fin n} {s t : ℤ}
    (h : toStdD n v = Pi.single a s + Pi.single b t) :
    lam c v = (s : ZMod p) * levTwoS2d_d n hn c a + (t : ZMod p) * levTwoS2d_d n hn c b := by
  rw [levTwoS2d_lam_coord n hn hp2 c v, h]
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · rw [Finset.sum_eq_single b]
    · simp
    · intro a _ ha; simp [Pi.single_eq_of_ne ha]
    · intro hb; exact absurd (Finset.mem_univ b) hb


end CFSG.StandardType.LevTwo
