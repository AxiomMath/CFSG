module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeTrans
public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec17

namespace Proof17Res10

open scoped commutatorElement

section Heis

variable {G : Type*} [Group G] {s t w : G}

theorem pow_mul_pow_eq (hs3 : s ^ 3 = 1) (hst : Commute s t) (hsw : Commute s w)
    (htw : t * w = s * w * t) (k j : ℕ) :
    w ^ k * t ^ j = s ^ (2 * k * j) * t ^ j * w ^ k := by
  have hwt : w * t = s ^ 2 * t * w := by
    have h1 : s ^ 2 * (t * w) = s ^ 2 * (s * w * t) := by rw [htw]
    calc w * t = s ^ 3 * (w * t) := by rw [hs3, one_mul]
      _ = s ^ 2 * (s * w * t) := by rw [pow_succ]; group
      _ = s ^ 2 * (t * w) := h1.symm
      _ = s ^ 2 * t * w := by group
  have h1 : ∀ j : ℕ, w * t ^ j = s ^ (2 * j) * t ^ j * w := by
    intro j
    induction j with
    | zero => simp
    | succ n ih =>
      calc w * t ^ (n + 1) = (w * t ^ n) * t := by rw [pow_succ]; group
        _ = s ^ (2 * n) * t ^ n * (w * t) := by rw [ih]; group
        _ = s ^ (2 * n) * t ^ n * (s ^ 2 * t * w) := by rw [hwt]
        _ = s ^ (2 * n) * (t ^ n * s ^ 2) * t * w := by group
        _ = s ^ (2 * n) * (s ^ 2 * t ^ n) * t * w := by
          rw [((hst.pow_right n).pow_left 2).eq]
        _ = s ^ (2 * (n + 1)) * t ^ (n + 1) * w := by
          rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, pow_succ t n]; group
  induction k with
  | zero => simp
  | succ n ih =>
    calc w ^ (n + 1) * t ^ j = w * (w ^ n * t ^ j) := by rw [pow_succ']; group
      _ = w * (s ^ (2 * n * j) * t ^ j * w ^ n) := by rw [ih]
      _ = (w * s ^ (2 * n * j)) * t ^ j * w ^ n := by group
      _ = (s ^ (2 * n * j) * w) * t ^ j * w ^ n := by
          rw [(hsw.pow_left (2 * n * j)).eq]
      _ = s ^ (2 * n * j) * (w * t ^ j) * w ^ n := by group
      _ = s ^ (2 * n * j) * (s ^ (2 * j) * t ^ j * w) * w ^ n := by rw [h1]
      _ = s ^ (2 * (n + 1) * j) * t ^ j * w ^ (n + 1) := by
          rw [show 2 * (n + 1) * j = 2 * n * j + 2 * j by ring, pow_add, pow_succ' w n]; group

theorem nf_mul (hs3 : s ^ 3 = 1) (hst : Commute s t) (hsw : Commute s w)
    (htw : t * w = s * w * t) (i j k i' j' k' : ℕ) :
    s ^ i * t ^ j * w ^ k * (s ^ i' * t ^ j' * w ^ k') =
      s ^ (i + i' + 2 * k * j') * t ^ (j + j') * w ^ (k + k') := by
  have hsw' : Commute (s ^ i') (w ^ k) := (hsw.pow_left i').pow_right k
  have hst' : Commute (s ^ i') (t ^ j) := (hst.pow_left i').pow_right j
  have hst'' : Commute (s ^ (2 * k * j')) (t ^ j) := (hst.pow_left _).pow_right j
  calc s ^ i * t ^ j * w ^ k * (s ^ i' * t ^ j' * w ^ k')
      = s ^ i * t ^ j * (w ^ k * s ^ i') * t ^ j' * w ^ k' := by group
    _ = s ^ i * (t ^ j * s ^ i') * (w ^ k * t ^ j') * w ^ k' := by rw [← hsw'.eq]; group
    _ = s ^ i * (s ^ i' * t ^ j) * (s ^ (2 * k * j') * t ^ j' * w ^ k) * w ^ k' := by
        rw [← hst'.eq, pow_mul_pow_eq hs3 hst hsw htw]
    _ = s ^ i * s ^ i' * (t ^ j * s ^ (2 * k * j')) * t ^ j' * (w ^ k * w ^ k') := by group
    _ = s ^ i * s ^ i' * (s ^ (2 * k * j') * t ^ j) * t ^ j' * (w ^ k * w ^ k') := by
        rw [hst''.eq]
    _ = s ^ (i + i' + 2 * k * j') * t ^ (j + j') * w ^ (k + k') := by
        rw [pow_add, pow_add, pow_add, pow_add]; group

theorem exists_nf_of_mem_closure (hs3 : s ^ 3 = 1) (ht3 : t ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hst : Commute s t) (hsw : Commute s w) (htw : t * w = s * w * t) {g : G}
    (hg : g ∈ Subgroup.closure ({t, w} : Set G)) :
    ∃ i j k : ℕ, g = s ^ i * t ^ j * w ^ k := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨0, 1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, k, rfl⟩ := hx
    obtain ⟨i', j', k', rfl⟩ := hy
    exact ⟨_, _, _, nf_mul hs3 hst hsw htw i j k i' j' k'⟩
  | inv x _ hx =>
    obtain ⟨i, j, k, rfl⟩ := hx
    have hsi : (s ^ i)⁻¹ = s ^ (2 * i) := by
      rw [← mul_eq_one_iff_inv_eq, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hs3,
        one_pow]
    have hti : (t ^ j)⁻¹ = t ^ (2 * j) := by
      rw [← mul_eq_one_iff_inv_eq, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, ht3,
        one_pow]
    have hwi : (w ^ k)⁻¹ = w ^ (2 * k) := by
      rw [← mul_eq_one_iff_inv_eq, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hw3,
        one_pow]
    refine ⟨2 * i + 2 * (2 * k) * (2 * j), 2 * j, 2 * k, ?_⟩
    have hs' : Commute (s ^ (2 * i)) (w ^ (2 * k) * t ^ (2 * j)) :=
      ((hsw.pow_left _).pow_right _).mul_right ((hst.pow_left _).pow_right _)
    calc (s ^ i * t ^ j * w ^ k)⁻¹ = (w ^ k)⁻¹ * (t ^ j)⁻¹ * (s ^ i)⁻¹ := by group
      _ = w ^ (2 * k) * t ^ (2 * j) * s ^ (2 * i) := by rw [hsi, hti, hwi]
      _ = s ^ (2 * i) * (w ^ (2 * k) * t ^ (2 * j)) := by rw [hs'.eq]
      _ = s ^ (2 * i) * (s ^ (2 * (2 * k) * (2 * j)) * t ^ (2 * j) * w ^ (2 * k)) := by
          rw [pow_mul_pow_eq hs3 hst hsw htw]
      _ = s ^ (2 * i + 2 * (2 * k) * (2 * j)) * t ^ (2 * j) * w ^ (2 * k) := by
          rw [pow_add]; group

theorem pow_three_of_mem_closure (hs3 : s ^ 3 = 1) (ht3 : t ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hst : Commute s t) (hsw : Commute s w) (htw : t * w = s * w * t) {g : G}
    (hg : g ∈ Subgroup.closure ({t, w} : Set G)) : g ^ 3 = 1 := by
  obtain ⟨i, j, k, rfl⟩ := exists_nf_of_mem_closure hs3 ht3 hw3 hst hsw htw hg
  rw [pow_succ, pow_two, nf_mul hs3 hst hsw htw, nf_mul hs3 hst hsw htw]
  have e1 : i + i + 2 * k * j + i + 2 * (k + k) * j = 3 * (i + 2 * k * j) := by ring
  have e2 : j + j + j = 3 * j := by ring
  have e3 : k + k + k = 3 * k := by ring
  rw [e1, e2, e3, pow_mul, pow_mul, pow_mul, hs3, ht3, hw3]
  simp

theorem isPGroup_closure (hs3 : s ^ 3 = 1) (ht3 : t ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (hst : Commute s t) (hsw : Commute s w) (htw : t * w = s * w * t) :
    IsPGroup 3 (Subgroup.closure ({t, w} : Set G)) := fun g =>
  ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_three_of_mem_closure hs3 ht3 hw3 hst hsw htw g.2)⟩

end Heis

section SL3

open Matrix CFSG.LieType.SeitzGeneration

variable {F : Type*} [Field F] {ω : F}

@[expose] def tSL (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) F :=
  diagSL 1 ω (ω ^ 2) (by rw [one_mul, ← pow_succ']; exact hω)

@[expose] def sSL (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) F :=
  diagSL ω ω ω (by rw [← pow_two, ← pow_succ]; exact hω)

theorem coe_sSL (hω : ω ^ 3 = 1) :
    ((sSL hω : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = ω • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sSL, diagSL]

theorem commute_sSL (hω : ω ^ 3 = 1) (g : SpecialLinearGroup (Fin 3) F) :
    Commute (sSL hω) g := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sSL]
  simp

theorem tSL_mul_shiftSL (hω : ω ^ 3 = 1) :
    tSL hω * shiftSL = sSL hω * shiftSL * tSL hω := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tSL, sSL, diagSL, shiftSL, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first | ring1 | linear_combination -hω

theorem commutator_tSL_shiftSL (hω : ω ^ 3 = 1) :
    ⁅tSL hω, (shiftSL : SpecialLinearGroup (Fin 3) F)⁆ = sSL hω := by
  rw [commutatorElement_def, tSL_mul_shiftSL hω]
  group

theorem tSL_pow_three (hω : ω ^ 3 = 1) : tSL hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tSL, diagSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first | linear_combination hω | linear_combination (ω ^ 3 + 1) * hω

theorem shiftSL_pow_three : (shiftSL : SpecialLinearGroup (Fin 3) F) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shiftSL, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem sSL_pow_three (hω : ω ^ 3 = 1) : sSL hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sSL, smul_pow, one_pow, hω, one_smul]
  rfl

theorem sSL_ne_one (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : sSL hω ≠ 1 := by
  intro h
  apply hω1
  have := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simpa [coe_sSL] using this

theorem isPGroup_closure_tSL_shiftSL (hω : ω ^ 3 = 1) :
    IsPGroup 3 (Subgroup.closure ({tSL hω, shiftSL} : Set (SpecialLinearGroup (Fin 3) F))) :=
  isPGroup_closure (sSL_pow_three hω) (tSL_pow_three hω) shiftSL_pow_three (commute_sSL hω _)
    (commute_sSL hω _) (tSL_mul_shiftSL hω)

theorem mem_zpowers_sSL_of_commute (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {m : SpecialLinearGroup (Fin 3) F} (h1 : m * tSL hω = tSL hω * m)
    (h2 : m * shiftSL = shiftSL * m) : m ∈ Subgroup.zpowers (sSL hω) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hq : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω ^ 3 / ω ^ 2 := by field_simp
      _ = 1 := by rw [hω, h, div_one]
  have hωω : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hω0
    · exact sub_eq_zero.mp h'
  have hMd : (m : Matrix (Fin 3) (Fin 3) F).det = 1 := m.2
  have e1 : (m : Matrix (Fin 3) (Fin 3) F) * (tSL hω : Matrix (Fin 3) (Fin 3) F) =
      (tSL hω : Matrix (Fin 3) (Fin 3) F) * (m : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h1]
  have e2 : (m : Matrix (Fin 3) (Fin 3) F) * ((shiftSL : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = ((shiftSL : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * (m : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h2]
  set M : Matrix (Fin 3) (Fin 3) F := (m : Matrix (Fin 3) (Fin 3) F) with hM
  have ent : ∀ i j : Fin 3, (M * (tSL hω : Matrix (Fin 3) (Fin 3) F)) i j =
      ((tSL hω : Matrix (Fin 3) (Fin 3) F) * M) i j := fun i j => by
    rw [← e1]
  have ent2 : ∀ i j : Fin 3, (M * ((shiftSL : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)) i j = (((shiftSL : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * M) i j := fun i j => by
    rw [← e2]
  simp only [tSL, diagSL, shiftSL, Matrix.mul_apply, Fin.sum_univ_three] at ent ent2
  have z01 : M 0 1 = 0 := by
    have := ent 0 1
    simp at this
    have h' : M 0 1 * (ω - 1) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h' with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hω1
  have z02 : M 0 2 = 0 := by
    have := ent 0 2
    simp at this
    have h' : M 0 2 * (ω ^ 2 - 1) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h' with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hω2
  have z10 : M 1 0 = 0 := by
    have := ent 1 0
    simp at this
    have h' : M 1 0 * (ω - 1) = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h' with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hω1
  have z12 : M 1 2 = 0 := by
    have := ent 1 2
    simp at this
    have h' : M 1 2 * (ω ^ 2 - ω) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h' with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hωω
  have z20 : M 2 0 = 0 := by
    have := ent 2 0
    simp at this
    have h' : M 2 0 * (ω ^ 2 - 1) = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h' with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hω2
  have z21 : M 2 1 = 0 := by
    have := ent 2 1
    simp at this
    have h' : M 2 1 * (ω ^ 2 - ω) = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h' with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hωω
  have d10 : M 1 1 = M 0 0 := by
    have := ent2 1 0
    simpa using this
  have d21 : M 2 2 = M 1 1 := by
    have := ent2 2 1
    simpa using this
  have hdet : M 0 0 ^ 3 = 1 := by
    have h := hMd
    rw [Matrix.det_fin_three, z01, z02, z10, z12, z20, z21, d21, d10] at h
    linear_combination h
  have hroots : (M 0 0 - 1) * (M 0 0 - ω) * (M 0 0 - ω ^ 2) = 0 := by
    linear_combination hdet - M 0 0 * (M 0 0 - 1) * hq + (M 0 0 - 1) * hω
  have hm : ∀ b : F, M 0 0 = b → M = b • 1 := by
    intro b hab
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z01, z02, z10, z12, z20, z21, d21, d10, hab]
  rw [Subgroup.mem_zpowers_iff]
  rcases mul_eq_zero.mp hroots with h | h
  · rcases mul_eq_zero.mp h with h | h
    ·
      refine ⟨0, Subtype.ext ?_⟩
      rw [zpow_zero, ← hM, hm 1 (sub_eq_zero.mp h), one_smul]
      rfl
    ·
      refine ⟨1, Subtype.ext ?_⟩
      rw [zpow_one, ← hM, hm ω (sub_eq_zero.mp h), coe_sSL]
  ·
    refine ⟨((2 : ℕ) : ℤ), Subtype.ext ?_⟩
    rw [zpow_natCast, ← hM, hm (ω ^ 2) (sub_eq_zero.mp h), Matrix.SpecialLinearGroup.coe_pow,
      coe_sSL, smul_pow, one_pow]

end SL3

section WeaklyClosed

variable {X : Type*} [Group X] [Finite X]

theorem commute_of_le_normalizer {Z S : Subgroup X} (hZ3 : Nat.card Z = 3) (hS : IsPGroup 3 S)
    (hSN : S ≤ Subgroup.normalizer (Z : Set X)) {z : X} (hz : z ∈ Z) {u : X} (hu : u ∈ S) :
    u * z = z * u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  have hZz : Z = Subgroup.zpowers z := Proof176Steps.eq_zpowers_of_card_three hZ3 hz hz1
  have hoz : orderOf z = 3 := by
    rw [← Nat.card_zpowers, ← hZz, hZ3]
  have hmem : u * z * u⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hSN hu) z).mp hz
  rw [hZz] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hconj : ∀ n : ℤ, u * z ^ n * u⁻¹ = z ^ (k * n) := by
    intro n
    rw [_root_.zpow_mul, hk, conj_zpow]
  have hk0 : ¬ (3 : ℤ) ∣ k := by
    intro h3
    apply hz1
    have h1 : z ^ k = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hoz]
      exact_mod_cast h3
    rw [h1] at hk
    calc z = u⁻¹ * (u * z * u⁻¹) * u := by group
      _ = 1 := by rw [← hk]; group
  have hkk : z ^ (k * k) = z := by
    have h3 : (3 : ℤ) ∣ k * k - 1 := by
      have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rw [show k * k - 1 = (k - 1) * (k + 1) by ring]
      rcases hk' with h | h
      · exact Dvd.dvd.mul_right (by omega) _
      · exact Dvd.dvd.mul_left (by omega) _
    have h1 : z ^ (k * k - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hoz]
      exact_mod_cast h3
    calc z ^ (k * k) = z ^ (k * k - 1) * z := by rw [← _root_.zpow_add_one, sub_add_cancel]
      _ = z := by rw [h1, one_mul]
  have hu2 : u ^ 2 * z * (u ^ 2)⁻¹ = z := by
    calc u ^ 2 * z * (u ^ 2)⁻¹ = u * (u * z * u⁻¹) * u⁻¹ := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = u * z ^ k * u⁻¹ := by rw [hk]
      _ = z ^ (k * k) := hconj k
      _ = z := hkk
  have hcomm : Commute (u ^ 2) z := by
    show u ^ 2 * z = z * u ^ 2
    calc u ^ 2 * z = u ^ 2 * z * (u ^ 2)⁻¹ * u ^ 2 := by group
      _ = z * u ^ 2 := by rw [hu2]
  obtain ⟨n, hn⟩ := hS ⟨u, hu⟩
  have hun : u ^ 3 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨r, hr⟩ : Odd (3 ^ n) := (by norm_num : Odd 3).pow
  have hueq : u = (u ^ 2) ^ (r + 1) := by
    rw [← pow_mul, show 2 * (r + 1) = 3 ^ n + 1 by rw [hr]; ring, pow_succ, hun, one_mul]
  rw [hueq]
  exact (hcomm.pow_left (r + 1)).eq

theorem exists_sylow_of_weaklyClosed {Z : Subgroup X} (hZ3 : Nat.card Z = 3)
    (hwc : ∀ g : X, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) →
      Z.map (MulAut.conj g).toMonoidHom = Z) :
    ∃ S : Sylow 3 X, Z ≤ (S : Subgroup X) ∧
      ∀ z ∈ Z, ∀ u ∈ (S : Subgroup X), u * z = z * u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  obtain ⟨S, hZS⟩ := hZp.exists_le_sylow
  have hSp : IsPGroup 3 (S : Subgroup X) := S.isPGroup'
  have hSN : (S : Subgroup X) ≤ Subgroup.normalizer (Z : Set X) := by
    by_contra hne
    set H := (S : Subgroup X) ⊓ Subgroup.normalizer (Z : Set X) with hH
    have hHS : H ≠ (S : Subgroup X) := fun h => hne (h ▸ inf_le_right)
    have hlt := CFSG.Goldschmidt.G310.lt_inf_normalizer hSp inf_le_left hHS
    obtain ⟨s, hs, hsH⟩ := IsConcreteLE.exists_of_lt hlt
    have hZH : Z ≤ H := le_inf hZS Subgroup.le_normalizer
    have hmap : Z.map (MulAut.conj s).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) := by
      rintro _ ⟨z, hz, rfl⟩
      have : s * z * s⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hs.2 z).mp (hZH hz)
      exact this.2
    have hsZ : s ∈ Subgroup.normalizer (Z : Set X) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hwc s hmap)
    exact hsH ⟨hs.1, hsZ⟩
  exact ⟨S, hZS, fun z hz u hu => commute_of_le_normalizer hZ3 hSp hSN hz hu⟩

end WeaklyClosed

end Proof17Res10

end CFSG.RankThree.PartTwo.Sec17
