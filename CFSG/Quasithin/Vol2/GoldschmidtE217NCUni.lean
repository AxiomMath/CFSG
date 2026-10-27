module

public import CFSG.Quasithin.Vol2.GoldschmidtE217NCAbs
public import CFSG.Quasithin.Vol2.Ch3E213MOLA8

public section

namespace CFSG.Quasithin

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace E217R3

theorem exists_pow_eq_neg_one {F : Type} [Field F] [Finite F] {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    (hF : Nat.card F = p ^ 2) : ∃ s : F, s ^ (p + 1) = -1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨k, hk⟩ := hp
  have hk1 : 1 ≤ k := by omega
  have hp2 : p ^ 2 = 4 * k * (k + 1) + 1 := by rw [hk]; ring
  have hcard : Nat.card Fˣ = 4 * k * (k + 1) := by
    rw [Nat.card_units, hF]
    omega
  have hord : orderOf g = 4 * k * (k + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  set w : Fˣ := g ^ (2 * k * (k + 1)) with hw
  have hw2 : w ^ 2 = 1 := by
    rw [hw, ← pow_mul, show 2 * k * (k + 1) * 2 = 4 * k * (k + 1) by ring, ← hord,
      pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    intro h
    have hd : orderOf g ∣ 2 * k * (k + 1) := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    have hpos : 0 < 2 * k * (k + 1) := by positivity
    have := Nat.le_of_dvd hpos hd
    nlinarith
  have hwF : ((w : Fˣ) : F) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hw2, Units.val_one]
  have hw1' : ((w : Fˣ) : F) ≠ 1 := fun h => hw1 (Units.ext h)
  have hwneg : ((w : Fˣ) : F) = -1 := by
    rcases mul_self_eq_one_iff.1
      (show ((w : Fˣ) : F) * ((w : Fˣ) : F) = 1 by rw [← pow_two]; exact hwF) with h | h
    · exact absurd h hw1'
    · exact h
  refine ⟨((g ^ k : Fˣ) : F), ?_⟩
  have hs : (((g ^ k : Fˣ) : F)) ^ (p + 1) = ((w : Fˣ) : F) := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, hw]
    congr 2
    rw [hk]
    ring
  rw [hs, hwneg]

section Mat

variable {F : Type} [Field F]

@[expose] def reflM (s t : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 2 * t, 2; 2 * s, -3, 2 * s; 2, 2 * t, 1]

theorem reflM_mul_self {s t : F} (hts : t * s = -1) : reflM s t * reflM s t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflM, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination 4 * hts | linear_combination 8 * hts

theorem det_reflM {s t : F} (hts : t * s = -1) : (reflM s t).det = 1 := by
  simp [reflM, Matrix.det_fin_three]
  linear_combination 8 * hts

theorem conjTr_reflM {σ : F ≃+* F} {s t : F} (hσs : σ s = t) (hσt : σ t = s) :
    conjTr σ (reflM s t) = reflM s t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, reflM, hσs, hσt, map_ofNat]

@[expose] noncomputable def reflSU {σ : F ≃+* F} {s t : F} (hts : t * s = -1) (hσs : σ s = t)
    (hσt : σ t = s) : SUid σ 3 :=
  ⟨⟨reflM s t, reflM s t, reflM_mul_self hts, reflM_mul_self hts⟩, by
    rw [mem_SUid]
    refine ⟨det_reflM hts, ?_⟩
    show conjTr σ (reflM s t) * reflM s t = 1
    rw [conjTr_reflM hσs hσt, reflM_mul_self hts]⟩

@[expose] def reflN (s t : F) : Matrix (Fin 3) (Fin 3) F :=
  !![-2, -2 * t, -2; -2 * s, 2, -2 * s; 2, 2 * t, 0]

theorem negBlock_mul_reflM (s t : F) :
    (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) * reflM s t = 1 + reflN s t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflM, reflN, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring1

theorem reflN_pow_three {s t : F} (hts : t * s = -1) : reflN s t ^ 3 = 0 := by
  rw [pow_succ, pow_two]
  unfold reflN
  simp only [Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | ring1 | linear_combination (8 : F) * hts | (left; ring1)

end Mat

theorem not_oddCube_uni {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp5 : 5 ≤ p) (hF : Nat.card F = (p ^ 1) ^ 2) {E : Type} [Group E]
    (θ : Phan.Su F p 1 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su F p 1 3)) {z : E} (hz : orderOf z = 2) :
    ¬ OddCube z := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_charP_ne_two (p := p) (by omega)
  obtain ⟨s, hs⟩ := exists_pow_eq_neg_one (hp.odd_of_ne_two (by omega)) (by omega)
    (by simpa using hF)
  set σ := unitaryInvolution F p 1 with hσ
  have hσs : σ s = s ^ p := by rw [hσ, unitaryInvolution_apply, pow_one]
  have hts : σ s * s = -1 := by rw [hσs, ← pow_succ, hs]
  have hσt : σ (σ s) = s := unitaryInvolution_involutive hF s
  set D : Phan.Su F p 1 3 := Models.rootInvSU F p 1 (n := 3) (by norm_num) with hD
  set M₁ : Phan.Su F p 1 3 := reflSU hts rfl hσt with hM₁
  have hDm : Models.suMat D = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := coe_rootInvSU_three
  have hMm : Models.suMat M₁ = reflM s (σ s) := rfl
  have hDD : D * D = 1 := by
    apply Models.suMat_injective
    rw [Models.suMat_mul, hDm, Models.suMat_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hMM : M₁ * M₁ = 1 := by
    apply Models.suMat_injective
    rw [Models.suMat_mul, hMm, Models.suMat_one]
    exact reflM_mul_self hts
  have hnc : D * M₁ ≠ M₁ * D := by
    intro h
    have h' := congrArg (fun g : Phan.Su F p 1 3 => Models.suMat g 0 2) h
    simp only [Models.suMat_mul, hDm, hMm] at h'
    simp [reflM, Matrix.mul_apply, Fin.sum_univ_three] at h'
    apply h2
    have h4 : (2 : F) * 2 = 0 := by linear_combination -h'
    exact mul_self_eq_zero.1 h4
  have hpow : ∀ (x : Phan.Su F p 1 3) (n : ℕ), Models.suMat (x ^ n) = Models.suMat x ^ n := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Models.suMat_mul, ih, pow_succ]
  have hy : (D * M₁) ^ p = 1 := by
    apply Models.suMat_injective
    rw [hpow, Models.suMat_mul, hDm, hMm, negBlock_mul_reflM, Models.suMat_one]
    exact pow_eq_one_of_pow_three_eq_zero (by omega) (reflN_pow_three hts)
  have hconj : ∀ t s : E, orderOf t = 2 → orderOf s = 2 → ∃ g : E, t = g * s * g⁻¹ := by
    intro t s ht hs
    obtain ⟨g₁, hg₁⟩ := CFSG.Quasithin.Ch3E213M.OLA.uni_conj_inv hF (by omega) (by simpa using hp5)
      θ hθ hker t ht
    obtain ⟨g₂, hg₂⟩ := CFSG.Quasithin.Ch3E213M.OLA.uni_conj_inv hF (by omega) (by simpa using hp5)
      θ hθ hker s hs
    refine ⟨g₁ * g₂⁻¹, ?_⟩
    rw [hg₁, hg₂]
    group
  exact not_oddCube_of_pair θ hker hp hp5 hDD hMM hnc hconj hy hz

end E217R3

end CFSG.Quasithin
