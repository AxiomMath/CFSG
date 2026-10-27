module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUTorus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerHeis

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K]

theorem exists_cube_class [Finite K] (h3 : 3 ∣ Nat.card K - 1) {l : Kˣ}
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l) (s : Kˣ) : ∃ (e : ℕ) (t : Kˣ), e < 3 ∧ s = l ^ e * t ^ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Kˣ)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff l g).mp (hg l)
  obtain ⟨r, hr⟩ := (Submonoid.mem_powers_iff s g).mp (hg s)
  have h3m : ¬ 3 ∣ m := by
    intro hd
    obtain ⟨k, hk⟩ := hd
    exact hl (g ^ k) (by rw [← hm, hk, mul_comm 3 k, pow_mul])
  let e : ℕ := (r * m) % 3
  have he_lt : e < 3 := Nat.mod_lt _ (by norm_num)
  have hdvd : (3 : ℤ) ∣ (r : ℤ) - (m : ℤ) * e := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((r : ℤ) - (m : ℤ) * e) 3).mp ?_
    have hmne : ((m : ℕ) : ZMod 3) ≠ 0 := by
      intro h
      exact h3m ((ZMod.natCast_eq_zero_iff m 3).mp h)
    have hm2 : ((m : ℕ) : ZMod 3) ^ 2 = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one (p := 3) hmne
    have he : ((e : ℕ) : ZMod 3) = (r : ZMod 3) * (m : ZMod 3) := by
      have := ZMod.natCast_mod (r * m) 3
      simpa [e, Nat.cast_mul] using this
    push_cast
    rw [he]
    have hmul : (m : ZMod 3) * ((r : ZMod 3) * (m : ZMod 3)) =
        (r : ZMod 3) * (m : ZMod 3) ^ 2 := by ring
    rw [hmul, hm2, mul_one, sub_self]
  obtain ⟨u, hu⟩ := hdvd
  have hml : g ^ (m : ℤ) = l := by rw [zpow_natCast]; exact hm
  have hrs : g ^ (r : ℤ) = s := by rw [zpow_natCast]; exact hr
  have hru : (r : ℤ) = (m : ℤ) * (e : ℤ) + 3 * u := by linarith [hu]
  have h1 : g ^ ((m : ℤ) * (e : ℤ)) = (g ^ (m : ℤ)) ^ e := by
    rw [_root_.zpow_mul, zpow_natCast]
  have h2 : g ^ (3 * u) = (g ^ u) ^ ((3 : ℕ) : ℤ) := by
    rw [mul_comm 3 u, _root_.zpow_mul]
    norm_num
  refine ⟨e, g ^ u, he_lt, ?_⟩
  calc s = g ^ (r : ℤ) := hrs.symm
    _ = g ^ ((m : ℤ) * (e : ℤ) + 3 * u) := by rw [hru]
    _ = g ^ ((m : ℤ) * (e : ℤ)) * g ^ (3 * u) := by rw [_root_.zpow_add]
    _ = (g ^ (m : ℤ)) ^ e * (g ^ u) ^ ((3 : ℕ) : ℤ) := by rw [h1, h2]
    _ = l ^ e * (g ^ u) ^ 3 := by rw [hml, zpow_natCast]

theorem scalar_mem_primeFormUnitary_of_cube {n : ℕ} (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {t : Kˣ}
    (ht : GeneralLinearGroup.scalar (Fin 6) (t ^ 3) ∈ primeFormUnitary hKd (idGram K 6)) :
    GeneralLinearGroup.scalar (Fin 6) t ∈ primeFormUnitary hKd (idGram K 6) := by
  have ht3 : (t ^ 3) ^ (2 ^ n + 1) = 1 := by
    have h1 := (SUTorus.scalar_mem_primeFormUnitary_iff (n := 6) hKd (t ^ 3)).mp ht
    rw [hKd.bar_apply] at h1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    exact h1
  exact SUModel.scalar_mem_unitary hKd
    (SUTorus.pow_add_one_eq_one_of_pow hKd Nat.prime_three (by norm_num) hpq (l := t)
      (c := t ^ 3) rfl ht3)

theorem exists_normalized {n : ℕ} (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {M N : GL (Fin 6) K} {l c ζ' : Kˣ} (hMu : M ∈ primeFormUnitary hKd (idGram K 6))
    (hNu : N ∈ primeFormUnitary hKd (idGram K 6)) (hM3 : M ^ 3 = GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ d : Kˣ, d ^ 3 ≠ l) (hN3 : N ^ 3 = GeneralLinearGroup.scalar (Fin 6) c)
    (hζ' : ζ' ^ 3 = 1) (hNM : N * M = GeneralLinearGroup.scalar (Fin 6) ζ' * (M * N)) :
    ∃ (j : ℕ) (t : Kˣ), j < 3 ∧
      GeneralLinearGroup.scalar (Fin 6) t ∈ primeFormUnitary hKd (idGram K 6) ∧
      (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * N * M ^ j) ^ 3 = 1 := by
  haveI : Finite K := hKd.finite
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [hKd.card]
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [pow_mul']
      simpa [pow_two] using Nat.mul_self_sub_mul_self_eq (2 ^ n) 1
    rw [hfac]
    exact hpq.mul_right _
  obtain ⟨e, t0, he_lt, hceq⟩ := exists_cube_class h3 hl c
  let j : ℕ := (3 - e) % 3
  have hj_lt : j < 3 := Nat.mod_lt _ (by norm_num)
  have h3ej : 3 ∣ e + j := by
    have he3 : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases he3 with rfl | rfl | rfl <;> decide
  obtain ⟨w, hw⟩ := h3ej
  set t : Kˣ := l ^ w * t0 with ht
  have hsc3 : (GeneralLinearGroup.scalar (Fin 6) ζ') ^ 3 = 1 := by
    rw [← map_pow, hζ', map_one]
  have hMj3 : (M ^ j) ^ 3 = (GeneralLinearGroup.scalar (Fin 6) l) ^ j := by
    rw [← pow_mul, mul_comm j 3, pow_mul, hM3]
  have hct : c * l ^ j = t ^ 3 := by
    rw [hceq, ht]
    calc l ^ e * t0 ^ 3 * l ^ j
        = l ^ e * (t0 ^ 3 * l ^ j) := by rw [mul_assoc]
      _ = l ^ e * (l ^ j * t0 ^ 3) := by rw [mul_comm (t0 ^ 3) (l ^ j)]
      _ = l ^ e * l ^ j * t0 ^ 3 := by rw [mul_assoc]
      _ = l ^ (e + j) * t0 ^ 3 := by rw [← pow_add]
      _ = l ^ (3 * w) * t0 ^ 3 := by rw [hw]
      _ = (l ^ w) ^ 3 * t0 ^ 3 := by rw [mul_comm 3 w, pow_mul]
      _ = (l ^ w * t0) ^ 3 := by rw [mul_pow]
  have hX3 : (N * M ^ j) ^ 3 = GeneralLinearGroup.scalar (Fin 6) (t ^ 3) := by
    have hu : ∀ g : GL (Fin 6) K, Commute ((GeneralLinearGroup.scalar (Fin 6) ζ') ^ j) g :=
      fun g => (commute_scalar ζ' g).symm.pow_left j
    have hnmj : N * M ^ j = (GeneralLinearGroup.scalar (Fin 6) ζ') ^ j * (M ^ j * N) :=
      Line63.H5.mul_pow_eq_central (fun g => (commute_scalar ζ' g).symm) hNM j
    have hu3 : ((GeneralLinearGroup.scalar (Fin 6) ζ') ^ j) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm j 3, pow_mul, hsc3, one_pow]
    rw [Line63.H5.mul_pow_three_eq_central hu hnmj hu3, hN3, hMj3, ← map_pow, ← map_mul, hct]
  have hXt : GeneralLinearGroup.scalar (Fin 6) t ∈ primeFormUnitary hKd (idGram K 6) := by
    have hX : N * M ^ j ∈ primeFormUnitary hKd (idGram K 6) :=
      mul_mem hNu (pow_mem hMu j)
    have hX3u : GeneralLinearGroup.scalar (Fin 6) (t ^ 3) ∈ primeFormUnitary hKd (idGram K 6) := by
      rw [← hX3]
      exact pow_mem hX 3
    exact scalar_mem_primeFormUnitary_of_cube hKd hpq hX3u
  refine ⟨j, t, hj_lt, hXt, ?_⟩
  have hfinal : (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (N * M ^ j)) ^ 3 = 1 := by
    have hinv : (GeneralLinearGroup.scalar (Fin 6) t⁻¹) ^ 3 =
        (GeneralLinearGroup.scalar (Fin 6) (t ^ 3))⁻¹ := by
      rw [← map_pow, inv_pow, map_inv]
    rw [Commute.mul_pow (commute_scalar t⁻¹ (N * M ^ j)).symm 3, hinv, hX3, inv_mul_cancel]
  rw [mul_assoc]
  exact hfinal

end CFSG.StandardType.UnitSixThreeKG

end
