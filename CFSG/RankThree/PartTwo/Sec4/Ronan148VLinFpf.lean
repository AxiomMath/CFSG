module

import CFSG.RankThree.PartTwo.Sec4.Ronan148VElation
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VLinHeis
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VLinTorus

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

variable {F : Type} [Field F]

theorem mul_conj_eq_conj_mul {P : Type*} [Group P] (φ : MulAut P) (p : P) :
    φ * MulAut.conj p = MulAut.conj (φ p) * φ := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem eq_one_of_pow_three_eq_one_of_mem {P : Type*} [Group P] {S : Subgroup P}
    (hS : ¬ 3 ∣ Nat.card S) {r : P} (hr : r ∈ S) (h3 : r ^ 3 = 1) : r = 1 := by
  have hcard : r ^ Nat.card S = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := S) (x := ⟨r, hr⟩))
    rw [SubmonoidClass.coe_pow] at h
    exact h
  have hcop : Nat.Coprime 3 (Nat.card S) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hS
  have h := pow_gcd_eq_one.mpr ⟨h3, hcard⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h

theorem conj_conjAut_proj (M : GL (Fin 3) F) (A : SpecialLinearGroup (Fin 3) F) :
    MulAut.conj (conjAut 3 F M (proj 3 F A)) =
      conjAut 3 F (M * Matrix.SpecialLinearGroup.toGL A * M⁻¹) := by
  rw [map_mul, map_mul, map_inv, conjAut_toGL, mul_conj_eq_conj_mul, mul_inv_cancel_right]

theorem exists_conj_eq_scalar_mul [Finite F] {M N : GL (Fin 3) F}
    (h : conjAut 3 F M * conjAut 3 F N = conjAut 3 F N * conjAut 3 F M) :
    ∃ u : Fˣ, M * N * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * N := by
  have h1 : conjAut 3 F (M * N * M⁻¹ * N⁻¹) * fieldAut 3 F 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel_right,
      mul_inv_cancel]
  obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ 1 h1
  exact ⟨u, by rw [hu]; group⟩

theorem fieldAut_mul_conjAut_of_map_eq (ρ : F ≃+* F) {M : GL (Fin 3) F}
    (hM : GeneralLinearGroup.map (ρ : F →+* F) M = M) :
    fieldAut 3 F ρ * conjAut 3 F M = conjAut 3 F M * fieldAut 3 F ρ := by
  rw [fieldAut_mul_conjAut, hM]

section Heis

variable {τ : F} (hτ : τ ^ 3 = 1)

theorem conjAut_diagTau_mul_cycThree :
    conjAut 3 F (diagTau hτ) * conjAut 3 F cycThree =
      conjAut 3 F cycThree * conjAut 3 F (diagTau hτ) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h := congrArg (conjAut 3 F) (cycThree_pow_conj_diagTau hτ hτ0 1)
  rw [pow_one, map_mul, map_mul, map_mul, map_inv, conjAut_scalar, one_mul,
    mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem conjAut_fourier_diagTau (h3 : (3 : F) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) :
    conjAut 3 F (fourierGL h3 hs) * conjAut 3 F (diagTau hτ) *
      (conjAut 3 F (fourierGL h3 hs))⁻¹ = (conjAut 3 F cycThree)⁻¹ := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h := congrArg (conjAut 3 F) (fourier_conj_diagTau hτ h3 hs hτ0)
  rwa [map_mul, map_mul, map_mul, map_inv, map_inv, conjAut_scalar, one_mul] at h

theorem conjAut_fourier_cycThree (h3 : (3 : F) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) :
    conjAut 3 F (fourierGL h3 hs) * conjAut 3 F cycThree * (conjAut 3 F (fourierGL h3 hs))⁻¹ =
      conjAut 3 F (diagTau hτ) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h := congrArg (conjAut 3 F) (fourier_conj_cycThree hτ h3 hs hτ0)
  rwa [map_mul, map_mul, map_mul, map_inv, conjAut_scalar, one_mul] at h

theorem conjAut_phase_diagTau :
    conjAut 3 F (phaseGL hτ) * conjAut 3 F (diagTau hτ) =
      conjAut 3 F (diagTau hτ) * conjAut 3 F (phaseGL hτ) := by
  rw [← map_mul, phase_mul_diagTau, map_mul]

theorem conjAut_phase_cycThree :
    conjAut 3 F (phaseGL hτ) * conjAut 3 F cycThree * (conjAut 3 F (phaseGL hτ))⁻¹ =
      conjAut 3 F (diagTau hτ) * conjAut 3 F cycThree := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h := congrArg (conjAut 3 F) (phase_conj_cycThree hτ hτ0)
  rwa [map_mul, map_mul, map_mul, map_mul, map_inv, conjAut_scalar, one_mul] at h

variable (hτ1 : τ ≠ 1) [Finite F]

include hτ1 in
theorem conjAut_mem_diagTorus_of_commute {m : ℕ} {N : GL (Fin 3) F}
    (h : conjAut 3 F N * conjAut 3 F (diagTau hτ) = conjAut 3 F (diagTau hτ) * conjAut 3 F N)
    {t : projectiveSL 3 F} (ht : t ∈ diagTorus (F := F) m) :
    conjAut 3 F N t ∈ diagTorus (F := F) m := by
  obtain ⟨u, hu⟩ := exists_conj_eq_scalar_mul h
  obtain ⟨k, hk, -, a, b, e, rfl⟩ := exists_cycThree_pow_mul_of_conj hτ hτ1 hu
  exact conjAut_mem_diagTorus hk a b e ht

include hτ1 in
theorem exists_conjAut_eq_pow_mul_pow {N : GL (Fin 3) F}
    (hd : conjAut 3 F N * conjAut 3 F (diagTau hτ) = conjAut 3 F (diagTau hτ) * conjAut 3 F N)
    (hc : conjAut 3 F N * conjAut 3 F cycThree = conjAut 3 F cycThree * conjAut 3 F N) :
    ∃ i j : ℕ, conjAut 3 F N = conjAut 3 F cycThree ^ i * conjAut 3 F (diagTau hτ) ^ j := by
  obtain ⟨u, hu⟩ := exists_conj_eq_scalar_mul hd
  obtain ⟨v, hv⟩ := exists_conj_eq_scalar_mul hc
  obtain ⟨s, k, l, -, -, rfl⟩ := exists_eq_scalar_mul_of_conj_of_conj hτ hτ1 hu hv
  exact ⟨k, l, by rw [map_mul, map_mul, conjAut_scalar, one_mul, map_pow, map_pow]⟩

include hτ1 in
theorem proj_pow_three_eq_one {r : SpecialLinearGroup (Fin 3) F}
    (hd : MulAut.conj (proj 3 F r) * conjAut 3 F (diagTau hτ) =
      conjAut 3 F (diagTau hτ) * MulAut.conj (proj 3 F r))
    (hc : MulAut.conj (proj 3 F r) * conjAut 3 F cycThree =
      conjAut 3 F cycThree * MulAut.conj (proj 3 F r)) :
    proj 3 F r ^ 3 = 1 := by
  rw [← conjAut_toGL] at hd hc
  obtain ⟨i, j, hij⟩ := exists_conjAut_eq_pow_mul_pow hτ hτ1 hd hc
  have hcd : Commute (conjAut 3 F cycThree ^ i) (conjAut 3 F (diagTau hτ) ^ j) :=
    Commute.pow_pow (conjAut_diagTau_mul_cycThree hτ).symm i j
  have hC3 : conjAut 3 F cycThree ^ 3 = 1 := by rw [← map_pow, cycThree_pow_three, map_one]
  have hD3 : conjAut 3 F (diagTau hτ) ^ 3 = 1 := by rw [← map_pow, diagTau_pow_three, map_one]
  have h1 : conjAut 3 F (Matrix.SpecialLinearGroup.toGL (r ^ 3)) * fieldAut 3 F 1 = 1 := by
    rw [map_one, mul_one, map_pow, map_pow, hij, hcd.mul_pow, ← pow_mul, ← pow_mul, mul_comm i,
      mul_comm j, pow_mul, pow_mul, hC3, hD3, one_pow, one_pow, one_mul]
  obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ 1 h1
  rw [← map_pow]
  apply proj_eq_one_of_eq_smul_one (a := (u : F))
  have h2 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hu
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply] at h2
  rw [← smul_one_eq_diagonal] at h2
  exact h2.symm

end Heis

section Main

variable {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) [Finite F]

include hτ1 in
theorem exists_fpf_subgroup [CharP F 2] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 1) {ρ : F ≃+* F} (hρ : orderOf ρ = 3) (hρτ : ρ τ = τ)
    {h₀ : GL (Fin 3) F}
    (hHd : conjAut 3 F h₀ * conjAut 3 F (diagTau hτ) = conjAut 3 F (diagTau hτ) * conjAut 3 F h₀)
    (hHc : conjAut 3 F h₀ * conjAut 3 F cycThree = conjAut 3 F cycThree * conjAut 3 F h₀)
    (RP : Subgroup (projectiveSL 3 F)) (hR3 : ¬ 3 ∣ Nat.card RP) (hR1 : RP ≠ ⊥)
    (hRd : ∀ r ∈ RP, conjAut 3 F (diagTau hτ) r = r)
    (hRθ : ∀ r ∈ RP, conjAut 3 F h₀ (fieldAut 3 F ρ r) = r)
    (hRc : ∀ r ∈ RP, conjAut 3 F cycThree r ∈ RP) :
    ∃ A : Subgroup (projectiveSL 3 F), ¬ 3 ∣ Nat.card A ∧
      (∀ a ∈ A, conjAut 3 F h₀ (fieldAut 3 F ρ a) ∈ A) ∧
      (∀ M : GL (Fin 3) F,
        conjAut 3 F M * conjAut 3 F (diagTau hτ) = conjAut 3 F (diagTau hτ) * conjAut 3 F M →
        conjAut 3 F M * conjAut 3 F cycThree = conjAut 3 F cycThree * conjAut 3 F M →
        ∀ a ∈ A, conjAut 3 F M a ∈ A) ∧
      (∀ a ∈ A, conjAut 3 F (diagTau hτ) a = a → a = 1) ∧
      ∃ u ∈ A, u ≠ 1 ∧ conjAut 3 F h₀ (fieldAut 3 F ρ (conjAut 3 F (diagTau hτ) u)) = u := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h3 : (3 : F) ≠ 0 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have : (3 : F) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  have hs := one_add_tau_add_sq hτ hτ1
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  set D := conjAut 3 F (diagTau hτ) with hDdef
  set C := conjAut 3 F (cycThree : GL (Fin 3) F) with hCdef
  set H := conjAut 3 F h₀ with hHdef
  set f := fieldAut 3 F ρ with hfdef
  set Fo := conjAut 3 F (fourierGL h3 hs) with hFodef
  set Ph := conjAut 3 F (phaseGL hτ) with hPhdef
  have hDC : D * C = C * D := conjAut_diagTau_mul_cycThree hτ
  have hC3 : C ^ 3 = 1 := by rw [hCdef, ← map_pow, cycThree_pow_three, map_one]
  have hCi : C⁻¹ = C ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hC3]
  have hFD : Fo * D * Fo⁻¹ = C⁻¹ := conjAut_fourier_diagTau hτ h3 hs
  have hFC : Fo * C * Fo⁻¹ = D := conjAut_fourier_cycThree hτ h3 hs
  have hPD : Ph * D = D * Ph := conjAut_phase_diagTau hτ
  have hPC : Ph * C * Ph⁻¹ = D * C := conjAut_phase_cycThree hτ
  have hfD : f * D = D * f := fieldAut_mul_conjAut_of_map_eq ρ (map_diagTau hτ ρ hρτ)
  have hfF : f * Fo = Fo * f := fieldAut_mul_conjAut_of_map_eq ρ (map_fourierGL h3 hs ρ hρτ)
  have hfP : f * Ph = Ph * f := fieldAut_mul_conjAut_of_map_eq ρ (map_phaseGL hτ ρ hρτ)
  have hcdet : ((cycThree : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [coe_cycThree, det_fin_three]
    simp
  set cS : SpecialLinearGroup (Fin 3) F :=
    ⟨((cycThree : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hcdet⟩ with hcS
  have hcS' : Matrix.SpecialLinearGroup.toGL cS = cycThree := Units.ext rfl
  have hCconj : C = MulAut.conj (proj 3 F cS) := by
    rw [← conjAut_toGL, hcS']
  set Y := h₀ * diagTau hτ with hYdef
  have hY : conjAut 3 F Y = H * D := map_mul _ _ _
  have hYD : conjAut 3 F Y * D = D * conjAut 3 F Y := by
    rw [hY]
    calc H * D * D = D * H * D := by rw [hHd]
      _ = D * (H * D) := mul_assoc _ _ _
  have hYC : conjAut 3 F Y * C = C * conjAut 3 F Y := by
    rw [hY]
    calc H * D * C = H * (C * D) := by rw [mul_assoc, hDC]
      _ = C * H * D := by rw [← mul_assoc, hHc]
      _ = C * (H * D) := mul_assoc _ _ _
  obtain ⟨ζd, hζd⟩ := exists_conj_eq_scalar_mul (M := Y) (N := diagTau hτ) hYD
  obtain ⟨ζc, hζc⟩ := exists_conj_eq_scalar_mul (M := Y) (N := cycThree) hYC
  set S := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)⁻¹ with hS
  have hFid : (fourierGL h3 hs)⁻¹ * diagTau hτ * fourierGL h3 hs = S * cycThree := by
    have e1 := fourier_conj_cycThree hτ h3 hs hτ0
    have hd : diagTau hτ = S * (fourierGL h3 hs * cycThree * (fourierGL h3 hs)⁻¹) := by
      rw [e1, ← mul_assoc, hS, ← map_mul, inv_mul_cancel, map_one, one_mul]
    rw [hd]
    calc (fourierGL h3 hs)⁻¹ * (S * (fourierGL h3 hs * cycThree * (fourierGL h3 hs)⁻¹)) *
        fourierGL h3 hs = ((fourierGL h3 hs)⁻¹ * S) * fourierGL h3 hs * cycThree := by group
      _ = (S * (fourierGL h3 hs)⁻¹) * fourierGL h3 hs * cycThree := by rw [hS, hsc]
      _ = S * cycThree := by group
  obtain ⟨m, hm, lam, hlm, hρl⟩ := exists_lam_linear hn hF hq hρ
  have hρ3 : ∀ x, ρ (ρ (ρ x)) = x := apply_apply_apply_of_orderOf_eq_three hρ
  have hfpfT : ∀ t ∈ diagTorus (F := F) m, C t = t → t = 1 := by
    intro t ht hCt
    have h1 : MulAut.conj (proj 3 F cS) t = t := by rw [← hCconj]; exact hCt
    rw [MulAut.conj_apply] at h1
    have hc : t * proj 3 F cS = proj 3 F cS * t := by
      calc t * proj 3 F cS = proj 3 F cS * t * (proj 3 F cS)⁻¹ * proj 3 F cS := by rw [h1]
        _ = proj 3 F cS * t := by group
    have h111 : diagUnits (1 : Fˣ) 1 1 = 1 := by
      apply Units.ext
      rw [coe_diagUnits]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    refine eq_one_of_commute_cycThree_pow hm (Or.inl rfl) (w₀ := 1) (w₁ := 1) (w₂ := 1)
      (M := cS) ?_ ht hc
    rw [pow_one, h111, mul_one]
  have torus : ∀ B : GL (Fin 3) F, GeneralLinearGroup.map (ρ : F →+* F) B = B →
      conjAut 3 F B * D * (conjAut 3 F B)⁻¹ = C⁻¹ →
      (∀ X : MulAut (projectiveSL 3 F), X * D = D * X → X * C = C * X →
        X * ((conjAut 3 F B)⁻¹ * D * conjAut 3 F B) =
          ((conjAut 3 F B)⁻¹ * D * conjAut 3 F B) * X) →
      ∀ ζ : Fˣ, ζ ≠ 1 →
      Y * (B⁻¹ * diagTau hτ * B) * Y⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) ζ * (B⁻¹ * diagTau hτ * B) →
      ∃ A : Subgroup (projectiveSL 3 F), ¬ 3 ∣ Nat.card A ∧
        (∀ a ∈ A, H (f a) ∈ A) ∧
        (∀ M : GL (Fin 3) F, conjAut 3 F M * D = D * conjAut 3 F M →
          conjAut 3 F M * C = C * conjAut 3 F M → ∀ a ∈ A, conjAut 3 F M a ∈ A) ∧
        (∀ a ∈ A, D a = a → a = 1) ∧ ∃ u ∈ A, u ≠ 1 ∧ H (f (D u)) = u := by
    intro B hBρ hBD hBY ζ hζ1 hζ
    set G := conjAut 3 F B with hG
    have hconj : ∀ X : MulAut (projectiveSL 3 F), X * (G⁻¹ * D * G) = (G⁻¹ * D * G) * X →
        (G * X * G⁻¹) * D = D * (G * X * G⁻¹) := by
      intro X hX
      calc G * X * G⁻¹ * D = G * (X * (G⁻¹ * D * G)) * G⁻¹ := by group
        _ = G * ((G⁻¹ * D * G) * X) * G⁻¹ := by rw [hX]
        _ = D * (G * X * G⁻¹) := by group
    have hfG : f * G = G * f := fieldAut_mul_conjAut_of_map_eq ρ hBρ
    have hfGi : f * G⁻¹ = G⁻¹ * f := by
      calc f * G⁻¹ = G⁻¹ * (G * f) * G⁻¹ := by group
        _ = G⁻¹ * (f * G) * G⁻¹ := by rw [hfG]
        _ = G⁻¹ * f := by group
    have hstab : ∀ M : GL (Fin 3) F,
        conjAut 3 F M * (G⁻¹ * D * G) = (G⁻¹ * D * G) * conjAut 3 F M →
        ∀ t ∈ diagTorus (F := F) m, (G * conjAut 3 F M * G⁻¹) t ∈ diagTorus (F := F) m := by
      intro M hM t ht
      have e : G * conjAut 3 F M * G⁻¹ = conjAut 3 F (B * M * B⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [e]
      exact conjAut_mem_diagTorus_of_commute hτ hτ1 (by rw [← e]; exact hconj _ hM) ht
    set N := B * Y * B⁻¹ with hN
    have hNd : N * diagTau hτ * N⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ := by
      calc N * diagTau hτ * N⁻¹ = B * (Y * (B⁻¹ * diagTau hτ * B) * Y⁻¹) * B⁻¹ := by
            rw [hN]; group
        _ = B * (GeneralLinearGroup.scalar (Fin 3) ζ * (B⁻¹ * diagTau hτ * B)) * B⁻¹ := by
          rw [hζ]
        _ = GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ := by
          rw [← mul_assoc B, hsc ζ B]
          group
    obtain ⟨k, hk, hkζ, w₀, w₁, w₂, hNk⟩ := exists_cycThree_pow_mul_of_conj hτ hτ1 hNd
    have hk12 : k = 1 ∨ k = 2 := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h0 | h0 | h0
      · exfalso
        apply hζ1
        apply Units.ext
        rw [hkζ, h0, mul_zero, pow_zero, Units.val_one]
      · exact Or.inl h0
      · exact Or.inr h0
    obtain ⟨t, htT, ht1, htfix⟩ := exists_fixed_diagTorus hm hk12 w₀ w₁ w₂ ρ hρ3 hlm hρl
    have hGN : G * (H * D) * G⁻¹ = conjAut 3 F N := by
      rw [hN, map_mul, map_mul, map_inv, hY]
    refine ⟨(diagTorus (F := F) m).comap G.toMonoidHom, fun h => not_three_dvd_card_diagTorus hm
      (h.trans (Subgroup.card_comap_dvd_of_injective _ G.toMonoidHom G.injective)), ?_, ?_, ?_,
      G⁻¹ t, ?_, ?_, ?_⟩
    ·
      intro a ha
      change G a ∈ diagTorus (F := F) m at ha
      change G (H (f a)) ∈ diagTorus (F := F) m
      have e : G * H * f = G * H * G⁻¹ * f * G := by
        calc G * H * f = G * H * G⁻¹ * (G * f) := by group
          _ = G * H * G⁻¹ * (f * G) := by rw [hfG]
          _ = G * H * G⁻¹ * f * G := by group
      have e2 : G (H (f a)) = (G * H * G⁻¹) (f (G a)) :=
        congrArg (fun φ : MulAut (projectiveSL 3 F) => φ a) e
      rw [e2]
      exact hstab h₀ (hBY H hHd hHc) _ (fieldAut_mem_diagTorus ρ ha)
    ·
      intro M hMd hMc a ha
      change G a ∈ diagTorus (F := F) m at ha
      change G (conjAut 3 F M a) ∈ diagTorus (F := F) m
      have e : G (conjAut 3 F M a) = (G * conjAut 3 F M * G⁻¹) (G a) := by
        change G (conjAut 3 F M a) = G (conjAut 3 F M (G⁻¹ (G a)))
        rw [MulAut.inv_apply_self]
      rw [e]
      exact hstab M (hBY _ hMd hMc) _ ha
    ·
      intro a ha hDa
      change G a ∈ diagTorus (F := F) m at ha
      have e : C⁻¹ (G a) = G a := by
        rw [← hBD]
        change G (D (G⁻¹ (G a))) = G a
        rw [MulAut.inv_apply_self, hDa]
      have e2 : C (G a) = G a := by
        conv_lhs => rw [← e]
        rw [MulAut.apply_inv_self]
      have h1 := hfpfT _ ha e2
      rw [← map_one G] at h1
      exact G.injective h1
    · change G (G⁻¹ t) ∈ diagTorus (F := F) m
      rw [MulAut.apply_inv_self]
      exact htT
    · intro h1
      apply ht1
      rw [← MulAut.apply_inv_self _ G t, h1, map_one]
    · apply G.injective
      rw [MulAut.apply_inv_self]
      have e : G * H * f * D * G⁻¹ = conjAut 3 F N * f := by
        rw [← hGN]
        calc G * H * f * D * G⁻¹ = G * H * (f * D) * G⁻¹ := by group
          _ = G * H * (D * f) * G⁻¹ := by rw [hfD]
          _ = G * H * D * (f * G⁻¹) := by group
          _ = G * H * D * (G⁻¹ * f) := by rw [hfGi]
          _ = G * (H * D) * G⁻¹ * f := by group
      have e2 := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ t) e
      change G (H (f (D (G⁻¹ t)))) = conjAut 3 F N (f t) at e2
      rw [e2, hNk]
      exact htfix
  have hFiD : Fo⁻¹ * D * Fo = C := by
    rw [← hFC]
    group
  have hFiC : Fo⁻¹ * C * Fo = D⁻¹ := by
    have : D = Fo⁻¹ * C⁻¹ * Fo := by
      rw [← hFD]
      group
    rw [this]
    group
  by_cases hc1 : ζc = 1
  · by_cases hd1 : ζd = 1
    ·
      rw [hc1, map_one, one_mul] at hζc
      rw [hd1, map_one, one_mul] at hζd
      have hYd' : Y * diagTau hτ = diagTau hτ * Y := by
        calc Y * diagTau hτ = Y * diagTau hτ * Y⁻¹ * Y := by group
          _ = diagTau hτ * Y := by rw [hζd]
      obtain ⟨a, b, e, hab⟩ := eq_diagUnits_of_commute_diagTau hτ hτ1 hYd'
      have h1 : Y * cycThree = cycThree * Y := by
        calc Y * cycThree = Y * cycThree * Y⁻¹ * Y := by group
          _ = cycThree * Y := by rw [hζc]
      have hYc' : cycThree * diagUnits a b e * cycThree⁻¹ = diagUnits a b e := by
        rw [← hab, ← h1, mul_inv_cancel_right]
      rw [cycThree_conj_diagUnits] at hYc'
      have he : e = a := by
        have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) hYc'
        exact Units.ext (by simpa [coe_diagUnits] using this)
      have hb : a = b := by
        have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 1 1) hYc'
        exact Units.ext (by simpa [coe_diagUnits] using this)
      have hHD : H * D = 1 := by
        have hsca : diagUnits a b e = GeneralLinearGroup.scalar (Fin 3) a := by
          apply Units.ext
          rw [coe_diagUnits, GeneralLinearGroup.coe_scalar, scalar_apply, ← hb, he]
          congr 1
          funext i
          fin_cases i <;> rfl
        rw [← hY, hab, hsca, conjAut_scalar]
      have hHi : H = D⁻¹ := eq_inv_of_mul_eq_one_left hHD
      have hRf : ∀ r ∈ RP, f r = r := by
        intro r hr
        have h1 := hRθ r hr
        rw [hHi] at h1
        have h2 : f r = D r := by
          have := congrArg D h1
          rwa [MulAut.apply_inv_self] at this
        rw [h2, hRd r hr]
      have hCpow : ∀ i : ℕ, ∀ r ∈ RP, (C ^ i) r ∈ RP := by
        intro i
        induction i with
        | zero => intro r hr; simpa using hr
        | succ i ih =>
          intro r hr
          rw [pow_succ, MulAut.mul_apply]
          exact ih _ (hRc r hr)
      have hDpow : ∀ j : ℕ, ∀ r ∈ RP, (D ^ j) r = r := by
        intro j
        induction j with
        | zero => intro r hr; simp
        | succ j ih =>
          intro r hr
          rw [pow_succ, MulAut.mul_apply, hRd r hr, ih r hr]
      refine ⟨RP.comap (Fo⁻¹ : MulAut (projectiveSL 3 F)).toMonoidHom, fun h => hR3
        (h.trans (Subgroup.card_comap_dvd_of_injective _ _ (Fo⁻¹).injective)), ?_, ?_, ?_, ?_⟩
      ·
        intro a ha
        change Fo⁻¹ a ∈ RP at ha
        change Fo⁻¹ (H (f a)) ∈ RP
        have e : Fo⁻¹ * (H * f) = C⁻¹ * f * Fo⁻¹ := by
          rw [hHi]
          calc Fo⁻¹ * (D⁻¹ * f) = (Fo⁻¹ * D * Fo)⁻¹ * (Fo⁻¹ * f) := by group
            _ = C⁻¹ * (Fo⁻¹ * f) := by rw [hFiD]
            _ = C⁻¹ * (Fo⁻¹ * (f * Fo) * Fo⁻¹) := by group
            _ = C⁻¹ * (Fo⁻¹ * (Fo * f) * Fo⁻¹) := by rw [hfF]
            _ = C⁻¹ * f * Fo⁻¹ := by group
        have e2 : Fo⁻¹ (H (f a)) = C⁻¹ (f (Fo⁻¹ a)) :=
          congrArg (fun φ : MulAut (projectiveSL 3 F) => φ a) e
        rw [e2, hRf _ ha, hCi]
        exact hCpow 2 _ ha
      ·
        intro M hMd hMc a ha
        change Fo⁻¹ a ∈ RP at ha
        change Fo⁻¹ (conjAut 3 F M a) ∈ RP
        have hM'd : conjAut 3 F ((fourierGL h3 hs)⁻¹ * M * fourierGL h3 hs) * D =
            D * conjAut 3 F ((fourierGL h3 hs)⁻¹ * M * fourierGL h3 hs) := by
          have e : conjAut 3 F ((fourierGL h3 hs)⁻¹ * M * fourierGL h3 hs) =
              Fo⁻¹ * conjAut 3 F M * Fo := by
            rw [map_mul, map_mul, map_inv]
          rw [e]
          have hD' : D = (Fo⁻¹ * C * Fo)⁻¹ := by rw [hFiC, inv_inv]
          have hMci : conjAut 3 F M * C⁻¹ = C⁻¹ * conjAut 3 F M := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, hMc, inv_mul_cancel_left]
          rw [hD']
          calc Fo⁻¹ * conjAut 3 F M * Fo * (Fo⁻¹ * C * Fo)⁻¹ =
              Fo⁻¹ * (conjAut 3 F M * C⁻¹) * Fo := by group
            _ = Fo⁻¹ * (C⁻¹ * conjAut 3 F M) * Fo := by rw [hMci]
            _ = (Fo⁻¹ * C * Fo)⁻¹ * (Fo⁻¹ * conjAut 3 F M * Fo) := by group
        have hM'c : conjAut 3 F ((fourierGL h3 hs)⁻¹ * M * fourierGL h3 hs) * C =
            C * conjAut 3 F ((fourierGL h3 hs)⁻¹ * M * fourierGL h3 hs) := by
          have e : conjAut 3 F ((fourierGL h3 hs)⁻¹ * M * fourierGL h3 hs) =
              Fo⁻¹ * conjAut 3 F M * Fo := by
            rw [map_mul, map_mul, map_inv]
          rw [e, ← hFiD]
          calc Fo⁻¹ * conjAut 3 F M * Fo * (Fo⁻¹ * D * Fo) =
              Fo⁻¹ * (conjAut 3 F M * D) * Fo := by group
            _ = Fo⁻¹ * (D * conjAut 3 F M) * Fo := by rw [hMd]
            _ = Fo⁻¹ * D * Fo * (Fo⁻¹ * conjAut 3 F M * Fo) := by group
        obtain ⟨i, j, hij⟩ := exists_conjAut_eq_pow_mul_pow hτ hτ1 hM'd hM'c
        have e : Fo⁻¹ (conjAut 3 F M a) = (C ^ i * D ^ j) (Fo⁻¹ a) := by
          rw [← hij, map_mul, map_mul, map_inv]
          change Fo⁻¹ (conjAut 3 F M a) = Fo⁻¹ (conjAut 3 F M (Fo (Fo⁻¹ a)))
          rw [MulAut.apply_inv_self]
        rw [e, MulAut.mul_apply, hDpow j _ ha]
        exact hCpow i _ ha
      ·
        intro a ha hDa
        change Fo⁻¹ a ∈ RP at ha
        have hCr : C (Fo⁻¹ a) = Fo⁻¹ a := by
          rw [← hFiD]
          change Fo⁻¹ (D (Fo (Fo⁻¹ a))) = Fo⁻¹ a
          rw [MulAut.apply_inv_self, hDa]
        obtain ⟨r, hr⟩ := proj_surjective 3 F (Fo⁻¹ a)
        have hDr : D (Fo⁻¹ a) = Fo⁻¹ a := hRd _ ha
        have hcomm : ∀ X : MulAut (projectiveSL 3 F), X (Fo⁻¹ a) = Fo⁻¹ a →
            MulAut.conj (proj 3 F r) * X = X * MulAut.conj (proj 3 F r) := by
          intro X hX
          rw [mul_conj_eq_conj_mul, hr, hX]
        have h3r := proj_pow_three_eq_one hτ hτ1 (hcomm D hDr) (hcomm C hCr)
        rw [hr] at h3r
        have h1 := eq_one_of_pow_three_eq_one_of_mem hR3 ha h3r
        rw [← map_one Fo⁻¹] at h1
        exact (Fo⁻¹).injective h1
      ·
        obtain ⟨⟨r, hr⟩, hr1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR1
        have hr1 : r ≠ 1 := fun h => hr1' (Subtype.ext h)
        refine ⟨Fo r, ?_, ?_, ?_⟩
        · change Fo⁻¹ (Fo r) ∈ RP
          rw [MulAut.inv_apply_self]
          exact hr
        · intro h1
          apply hr1
          rw [← MulAut.inv_apply_self _ Fo r, h1, map_one]
        · have e : H * f * D = f := by
            calc H * f * D = H * (f * D) := mul_assoc _ _ _
              _ = H * (D * f) := by rw [hfD]
              _ = H * D * f := (mul_assoc _ _ _).symm
              _ = f := by rw [hHD, one_mul]
          have e2 : H (f (D (Fo r))) = f (Fo r) :=
            congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (Fo r)) e
          rw [e2]
          have e3 : f (Fo r) = Fo (f r) :=
            congrArg (fun φ : MulAut (projectiveSL 3 F) => φ r) hfF
          rw [e3, hRf r hr]
    ·
      have hBρ : GeneralLinearGroup.map (ρ : F →+* F) (fourierGL h3 hs * (phaseGL hτ)⁻¹) =
          fourierGL h3 hs * (phaseGL hτ)⁻¹ := by
        rw [map_mul, map_inv, map_fourierGL h3 hs ρ hρτ, map_phaseGL hτ ρ hρτ]
      have hG : conjAut 3 F (fourierGL h3 hs * (phaseGL hτ)⁻¹) = Fo * Ph⁻¹ := by
        rw [map_mul, map_inv]
      obtain ⟨A, hA⟩ := torus (fourierGL h3 hs * (phaseGL hτ)⁻¹) hBρ (by
          rw [hG]
          calc Fo * Ph⁻¹ * D * (Fo * Ph⁻¹)⁻¹ = Fo * (Ph⁻¹ * D * Ph) * Fo⁻¹ := by group
            _ = Fo * D * Fo⁻¹ := by
              rw [show Ph⁻¹ * D * Ph = D by rw [mul_assoc, ← hPD, inv_mul_cancel_left]]
            _ = C⁻¹ := hFD) (by
          intro X hXd hXc
          have e : (conjAut 3 F (fourierGL h3 hs * (phaseGL hτ)⁻¹))⁻¹ * D *
              conjAut 3 F (fourierGL h3 hs * (phaseGL hτ)⁻¹) = D * C := by
            rw [hG, ← hPC, ← hFC]
            group
          rw [e]
          calc X * (D * C) = D * X * C := by rw [← mul_assoc, hXd]
            _ = D * C * X := by rw [mul_assoc, hXc, ← mul_assoc]) ζd hd1 (by
          have hB : (fourierGL h3 hs * (phaseGL hτ)⁻¹)⁻¹ * diagTau hτ *
              (fourierGL h3 hs * (phaseGL hτ)⁻¹) =
              S * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) *
                (diagTau hτ * cycThree)) := by
            calc (fourierGL h3 hs * (phaseGL hτ)⁻¹)⁻¹ * diagTau hτ *
                (fourierGL h3 hs * (phaseGL hτ)⁻¹) =
                phaseGL hτ * ((fourierGL h3 hs)⁻¹ * diagTau hτ * fourierGL h3 hs) *
                  (phaseGL hτ)⁻¹ := by group
              _ = phaseGL hτ * (S * cycThree) * (phaseGL hτ)⁻¹ := by rw [hFid]
              _ = S * (phaseGL hτ * cycThree * (phaseGL hτ)⁻¹) := by
                rw [← mul_assoc, hS, hsc]
                group
              _ = _ := by rw [phase_conj_cycThree hτ hτ0]
          rw [hB]
          set Z₁ := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) with hZ₁
          have hYS : Y * S = S * Y := hsc _ Y
          have hYZ : Y * Z₁ = Z₁ * Y := hsc _ Y
          calc Y * (S * (Z₁ * (diagTau hτ * cycThree))) * Y⁻¹ =
              S * (Z₁ * ((Y * diagTau hτ * Y⁻¹) * (Y * cycThree * Y⁻¹))) := by
                rw [← mul_assoc Y, hYS, mul_assoc S, ← mul_assoc Y, hYZ]
                group
            _ = S * (Z₁ * (GeneralLinearGroup.scalar (Fin 3) ζd * diagTau hτ * cycThree)) := by
                rw [hζd, hζc, hc1, map_one, one_mul]
            _ = GeneralLinearGroup.scalar (Fin 3) ζd * (S * (Z₁ * (diagTau hτ * cycThree))) := by
                have h1 : Z₁ * GeneralLinearGroup.scalar (Fin 3) ζd =
                    GeneralLinearGroup.scalar (Fin 3) ζd * Z₁ := hsc _ _
                have h2 : S * GeneralLinearGroup.scalar (Fin 3) ζd =
                    GeneralLinearGroup.scalar (Fin 3) ζd * S := hsc _ _
                calc S * (Z₁ * (GeneralLinearGroup.scalar (Fin 3) ζd * diagTau hτ * cycThree)) =
                    S * (Z₁ * GeneralLinearGroup.scalar (Fin 3) ζd) * (diagTau hτ * cycThree) := by
                      group
                  _ = (S * GeneralLinearGroup.scalar (Fin 3) ζd) * Z₁ *
                      (diagTau hτ * cycThree) := by
                      rw [h1]; group
                  _ = _ := by rw [h2]; group)
      exact ⟨A, hA⟩
  ·
    have hBρ := map_fourierGL h3 hs ρ hρτ
    obtain ⟨A, hA⟩ := torus (fourierGL h3 hs) hBρ hFD (by
        intro X hXd hXc
        have e : (conjAut 3 F (fourierGL h3 hs))⁻¹ * D * conjAut 3 F (fourierGL h3 hs) = C :=
          hFiD
        rw [e]
        exact hXc) ζc hc1 (by
        rw [hFid]
        have hYS : Y * S = S * Y := hsc _ Y
        have h2 : S * GeneralLinearGroup.scalar (Fin 3) ζc =
            GeneralLinearGroup.scalar (Fin 3) ζc * S := hsc _ _
        calc Y * (S * cycThree) * Y⁻¹ = S * (Y * cycThree * Y⁻¹) := by
              rw [← mul_assoc Y, hYS]
              group
          _ = S * (GeneralLinearGroup.scalar (Fin 3) ζc * cycThree) := by rw [hζc]
          _ = GeneralLinearGroup.scalar (Fin 3) ζc * (S * cycThree) := by
              rw [← mul_assoc, h2, mul_assoc])
    exact ⟨A, hA⟩

end Main

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
