module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerMain

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType
  CFSG.StandardType.Line63.H5

variable {K : Type} [Field K]

private lemma mod_three_eq_one_or_two {j : ℕ} (hj : ¬ 3 ∣ j) : j % 3 = 1 ∨ j % 3 = 2 := by
  have hlt : j % 3 < 3 := Nat.mod_lt j (by norm_num)
  have hne : j % 3 ≠ 0 := fun h => hj (Nat.dvd_of_mod_eq_zero h)
  omega

private lemma pow_three_ne_of_ne_cube {l : Kˣ} (hl : ∀ c : Kˣ, c ^ 3 ≠ l) {j : ℕ}
    (hj : ¬ 3 ∣ j) : ∀ d : Kˣ, d ^ 3 ≠ l ^ j := by
  rcases mod_three_eq_one_or_two hj with h1 | h2
  · intro d hd
    have hdj : j = 3 * (j / 3) + 1 := by
      rw [← h1]; exact (Nat.div_add_mod j 3).symm
    have hdecomp : l ^ j = (l ^ (j / 3)) ^ 3 * l := by
      calc l ^ j = l ^ (3 * (j / 3) + 1) := congrArg (fun t => l ^ t) hdj
        _ = l ^ (3 * (j / 3)) * l := by rw [pow_add, pow_one]
        _ = (l ^ (j / 3)) ^ 3 * l := by rw [mul_comm 3 (j / 3), pow_mul]
    have hd' : d ^ 3 = (l ^ (j / 3)) ^ 3 * l := by rw [← hdecomp]; exact hd
    have hcube : (d * (l ^ (j / 3))⁻¹) ^ 3 = l := by
      rw [mul_pow, hd', inv_pow]
      group
    exact (hl _) hcube
  · intro d hd
    have hdj : j = 3 * (j / 3) + 2 := by
      rw [← h2]; exact (Nat.div_add_mod j 3).symm
    have hdecomp : l ^ j = (l ^ (j / 3)) ^ 3 * l ^ 2 := by
      calc l ^ j = l ^ (3 * (j / 3) + 2) := congrArg (fun t => l ^ t) hdj
        _ = l ^ (3 * (j / 3)) * l ^ 2 := by rw [pow_add]
        _ = (l ^ (j / 3)) ^ 3 * l ^ 2 := by rw [mul_comm 3 (j / 3), pow_mul]
    have hd' : d ^ 3 = (l ^ (j / 3)) ^ 3 * l ^ 2 := by rw [← hdecomp]; exact hd
    set e : Kˣ := d * (l ^ (j / 3))⁻¹ with he
    have he3 : e ^ 3 = l ^ 2 := by
      rw [he, mul_pow, hd', inv_pow]
      group
    have hcube : (l * e⁻¹) ^ 3 = l := by
      rw [mul_pow, inv_pow, he3]
      have hpow : l ^ 3 = l ^ 2 * l := pow_succ l 2
      rw [hpow]
      group
    exact (hl _) hcube

private lemma mem_largeEvenScalars_of_pow_eq_scalar {Z : GL (Fin 6) K} (hZ3 : Z ^ 3 = 1)
    {j : ℕ} (hj : ¬ 3 ∣ j) {s : Kˣ} (h : Z ^ j = GeneralLinearGroup.scalar (Fin 6) s) :
    Z ∈ LargeEvenScalars (Fin 6) K := by
  have hmem : Z ^ j ∈ LargeEvenScalars (Fin 6) K := by
    rw [h]; exact scalar_mem_largeEvenScalars s
  rcases mod_three_eq_one_or_two hj with h1 | h2
  · have hdj : j = 3 * (j / 3) + 1 := by
      rw [← h1]; exact (Nat.div_add_mod j 3).symm
    have hZj : Z ^ j = Z := by
      calc Z ^ j = Z ^ (3 * (j / 3) + 1) := congrArg (fun t => Z ^ t) hdj
        _ = (Z ^ 3) ^ (j / 3) * Z := by rw [pow_add, pow_one, pow_mul Z 3 (j / 3)]
        _ = Z := by rw [hZ3, one_pow, one_mul]
    rwa [hZj] at hmem
  · have hdj : j = 3 * (j / 3) + 2 := by
      rw [← h2]; exact (Nat.div_add_mod j 3).symm
    have hZj : Z ^ j = Z ^ 2 := by
      calc Z ^ j = Z ^ (3 * (j / 3) + 2) := congrArg (fun t => Z ^ t) hdj
        _ = (Z ^ 3) ^ (j / 3) * Z ^ 2 := by rw [pow_add, pow_mul Z 3 (j / 3)]
        _ = Z ^ 2 := by rw [hZ3, one_pow, one_mul]
    have hZeq : Z = (Z ^ j) ^ 2 := by
      rw [hZj]
      calc Z = Z ^ 3 * Z := by rw [hZ3, one_mul]
        _ = Z ^ 4 := by rw [← pow_succ Z 3, show (3 : ℕ) + 1 = 4 by norm_num]
        _ = (Z ^ 2) ^ 2 := by rw [← pow_mul, show 2 * 2 = 4 by norm_num]
    rw [hZeq]
    exact pow_mem hmem 2

private lemma weyl_pow_Y {W Y Z : GL (Fin 6) K} (hWY : W * Y = Y * Z * W)
    (hYZ : Y * Z = Z * Y) (j : ℕ) : W * Y ^ j = Y ^ j * Z ^ j * W := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hc : Y * Z ^ j = Z ^ j * Y :=
      (Commute.pow_right (show Commute Y Z from hYZ) j).eq
    calc W * Y ^ (j + 1) = (W * Y ^ j) * Y := by rw [pow_succ, mul_assoc]
      _ = (Y ^ j * Z ^ j * W) * Y := by rw [ih]
      _ = Y ^ j * Z ^ j * (W * Y) := by group
      _ = Y ^ j * Z ^ j * (Y * Z * W) := by rw [hWY]
      _ = Y ^ j * (Z ^ j * Y) * Z * W := by group
      _ = Y ^ j * (Y * Z ^ j) * Z * W := by rw [hc]
      _ = Y ^ (j + 1) * Z ^ (j + 1) * W := by rw [pow_succ, pow_succ]; group


theorem mono_pow_three {X Y Z : GL (Fin 6) K} {ζ l : Kˣ} (hζ : ζ ^ 3 = 1) (hX3 : X ^ 3 = 1)
    (hZ3 : Z ^ 3 = 1) (hY3 : Y ^ 3 = GeneralLinearGroup.scalar (Fin 6) l)
    (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X)) (hXZ : X * Z = Z * X)
    (hYZ : Y * Z = Z * Y) (i j k : ℕ) :
    (X ^ i * Y ^ j * Z ^ k) ^ 3 = GeneralLinearGroup.scalar (Fin 6) (l ^ j) := by
  set u : GL (Fin 6) K := GeneralLinearGroup.scalar (Fin 6) ζ with hu
  have hcu : ∀ g : GL (Fin 6) K, Commute u g := fun g => (commute_scalar ζ g).symm
  have hu3 : u ^ 3 = 1 := by rw [hu, ← map_pow, hζ, map_one]
  have hcAZ : Commute (X ^ i * Y ^ j) (Z ^ k) :=
    ((Commute.pow_left (show Commute X Z from hXZ) i).pow_right k).mul_left
      ((Commute.pow_left (show Commute Y Z from hYZ) j).pow_right k)
  have hB3 : (Z ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hZ3, one_pow]
  have hA3 : (X ^ i * Y ^ j) ^ 3 = GeneralLinearGroup.scalar (Fin 6) (l ^ j) := by
    have hq : X ^ i * Y ^ j = u ^ (i * j) * (Y ^ j * X ^ i) :=
      pow_mul_pow_eq_central hcu hXY i j
    have hu3' : (u ^ (i * j)) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hu3, one_pow]
    have hxi3 : (X ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hX3, one_pow]
    have hyj3 : (Y ^ j) ^ 3 = GeneralLinearGroup.scalar (Fin 6) (l ^ j) := by
      rw [← pow_mul, mul_comm, pow_mul, hY3]
      exact (map_pow (GeneralLinearGroup.scalar (Fin 6)) l j).symm
    rw [mul_pow_three_eq_central (fun g => (hcu g).pow_left (i * j)) hq hu3',
      hxi3, hyj3, one_mul]
  rw [hcAZ.mul_pow 3, hB3, hA3, mul_one]

theorem weyl_mono {X Y Z W : GL (Fin 6) K} (hWX : W * X = X * W) (hWZ : W * Z = Z * W)
    (hWY : W * Y = Y * Z * W) (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y) (i j k : ℕ) :
    W * (X ^ i * Y ^ j * Z ^ k) = (X ^ i * Y ^ j * Z ^ k) * Z ^ j * W := by
  have hWXi : W * X ^ i = X ^ i * W :=
    (Commute.pow_right (show Commute W X from hWX) i).eq
  have hWZk : W * Z ^ k = Z ^ k * W :=
    (Commute.pow_right (show Commute W Z from hWZ) k).eq
  have hWYj : W * Y ^ j = Y ^ j * Z ^ j * W := weyl_pow_Y hWY hYZ j
  have hZZ : Z ^ j * Z ^ k = Z ^ k * Z ^ j := by rw [← pow_add, ← pow_add, add_comm]
  calc W * (X ^ i * Y ^ j * Z ^ k)
      = (W * (X ^ i * Y ^ j)) * Z ^ k := by group
    _ = ((W * X ^ i) * Y ^ j) * Z ^ k := by group
    _ = ((X ^ i * W) * Y ^ j) * Z ^ k := by rw [hWXi]
    _ = (X ^ i * (W * Y ^ j)) * Z ^ k := by group
    _ = (X ^ i * (Y ^ j * Z ^ j * W)) * Z ^ k := by rw [hWYj]
    _ = (X ^ i * Y ^ j * Z ^ j * W) * Z ^ k := by group
    _ = (X ^ i * Y ^ j * Z ^ j) * (W * Z ^ k) := by group
    _ = (X ^ i * Y ^ j * Z ^ j) * (Z ^ k * W) := by rw [hWZk]
    _ = (X ^ i * Y ^ j) * (Z ^ j * Z ^ k) * W := by group
    _ = (X ^ i * Y ^ j) * (Z ^ k * Z ^ j) * W := by rw [hZZ]
    _ = (X ^ i * Y ^ j * Z ^ k) * Z ^ j * W := by group

theorem mono_mul_ne {X Y Z : GL (Fin 6) K} {ζ l : Kˣ} (hζ : ζ ^ 3 = 1) (hX3 : X ^ 3 = 1)
    (hZ3 : Z ^ 3 = 1) (hY3 : Y ^ 3 = GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l) (hXY : X * Y = GeneralLinearGroup.scalar (Fin 6) ζ * (Y * X))
    (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y) (hZs : Z ∉ LargeEvenScalars (Fin 6) K)
    {i j k : ℕ} (hj : ¬ 3 ∣ j) (m : ℕ) (c : Kˣ) :
    (X ^ i * Y ^ j * Z ^ k) * Z ^ j ≠
      GeneralLinearGroup.scalar (Fin 6) c * (X ^ i * Y ^ j * Z ^ k) ^ m := by
  intro h
  set T : GL (Fin 6) K := X ^ i * Y ^ j * Z ^ k with hT
  set L : Kˣ := l ^ j with hLdef
  have hT3 : T ^ 3 = GeneralLinearGroup.scalar (Fin 6) L := by
    rw [hT, hLdef]
    exact mono_pow_three hζ hX3 hZ3 hY3 hXY hXZ hYZ i j k
  have hTZ : Commute T Z := by
    rw [hT]
    exact ((Commute.pow_left (show Commute X Z from hXZ) i).mul_left
      (Commute.pow_left (show Commute Y Z from hYZ) j)).mul_left
      ((Commute.refl Z).pow_left k)
  have hL : ∀ d : Kˣ, d ^ 3 ≠ L := by
    rw [hLdef]
    exact pow_three_ne_of_ne_cube hl hj
  obtain ⟨r, hrlt, hr⟩ : ∃ r : ℕ, r < 3 ∧ m = 3 * (m / 3) + r :=
    ⟨m % 3, Nat.mod_lt m (by norm_num), (Nat.div_add_mod m 3).symm⟩
  set s : Kˣ := c * L ^ (m / 3) with hs
  have hTm : T ^ m = GeneralLinearGroup.scalar (Fin 6) (L ^ (m / 3)) * T ^ r := by
    conv_lhs => rw [hr]
    rw [pow_add, pow_mul T 3 (m / 3), hT3, ← map_pow]
  have hmul : T * Z ^ j = GeneralLinearGroup.scalar (Fin 6) s * T ^ r := by
    rw [hTm] at h
    rw [← mul_assoc, ← map_mul] at h
    rw [hs]
    exact h
  interval_cases r
  · have hcube : (T * Z ^ j) ^ 3 = (GeneralLinearGroup.scalar (Fin 6) s) ^ 3 := by
      rw [hmul, pow_zero, mul_one]
    have hleft : (T * Z ^ j) ^ 3 = GeneralLinearGroup.scalar (Fin 6) L := by
      rw [(hTZ.pow_right j).mul_pow 3, hT3]
      have hZj3 : (Z ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hZ3, one_pow]
      rw [hZj3, mul_one]
    have hs3 : s ^ 3 = L := by
      apply TypeA.PGLTor.scalar_injective (ι := Fin 6)
      rw [map_pow]
      exact hcube.symm.trans hleft
    exact (hL s) hs3
  · have hZj : Z ^ j = GeneralLinearGroup.scalar (Fin 6) s := by
      have h1 : T * Z ^ j = T * GeneralLinearGroup.scalar (Fin 6) s := by
        rw [hmul, pow_one, (commute_scalar s T).symm.eq]
      exact mul_left_cancel h1
    exact hZs (mem_largeEvenScalars_of_pow_eq_scalar hZ3 hj hZj)
  · have hcomm : Commute (GeneralLinearGroup.scalar (Fin 6) s) T :=
      (commute_scalar s T).symm
    have hZT : Z ^ j = GeneralLinearGroup.scalar (Fin 6) s * T := by
      have h2 : T * Z ^ j = GeneralLinearGroup.scalar (Fin 6) s * (T * T) := by
        simpa only [pow_two] using hmul
      calc Z ^ j = T⁻¹ * (T * Z ^ j) := (inv_mul_cancel_left T (Z ^ j)).symm
        _ = T⁻¹ * (GeneralLinearGroup.scalar (Fin 6) s * (T * T)) := by rw [h2]
        _ = GeneralLinearGroup.scalar (Fin 6) s * T := by
            rw [← mul_assoc, (hcomm.inv_right).eq.symm]
            group
    have hT' : T = GeneralLinearGroup.scalar (Fin 6) s⁻¹ * Z ^ j := by
      rw [hZT, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have hRHS : (GeneralLinearGroup.scalar (Fin 6) s⁻¹ * Z ^ j) ^ 3 =
        GeneralLinearGroup.scalar (Fin 6) ((s⁻¹) ^ 3) := by
      rw [(commute_scalar s⁻¹ (Z ^ j)).symm.mul_pow 3, ← map_pow]
      have hZj3 : (Z ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hZ3, one_pow]
      rw [hZj3, mul_one]
    have h3 : GeneralLinearGroup.scalar (Fin 6) L =
        GeneralLinearGroup.scalar (Fin 6) ((s⁻¹) ^ 3) := by
      have hcong := congrArg (fun g : GL (Fin 6) K => g ^ 3) hT'
      rw [hT3, hRHS] at hcong
      exact hcong
    exact (hL s⁻¹) (TypeA.PGLTor.scalar_injective h3).symm

end CFSG.StandardType.UnitSixThreeKG

end
