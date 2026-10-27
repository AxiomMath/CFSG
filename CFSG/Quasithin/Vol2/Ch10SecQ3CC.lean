module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CB
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open SecA

variable {F : Type} [Field F]

theorem unipSL_mul_unipSL (a b : F) : unipSL a * unipSL b = unipSL (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem map_unipSL (σ : F ≃+* F) (b : F) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (unipSL b) = unipSL (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL]

theorem eq_unipSL_of_commute [CharP F 2] {h : Matrix.SpecialLinearGroup (Fin 2) F}
    (hc : h * unipSL 1 = unipSL 1 * h) : h = unipSL ((h : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e00 := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hc
  have e01 := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    coe_unipSL] at e00 e01
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.empty_val'] at e00 e01
  have h10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -e00
  have h11 : (h : Matrix (Fin 2) (Fin 2) F) 1 1 = (h : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -e01
  have hdet := h.2
  rw [Matrix.det_fin_two, h10, h11] at hdet
  have h00 : (h : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have hsq : ((h : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) * ((h : Matrix (Fin 2) (Fin 2) F) 0 0 + 1)
        = 0 := by linear_combination hdet + ((h : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) * h2
    linear_combination mul_self_eq_zero.mp hsq - h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL, h00, h10, h11]

theorem sq_eq_of_fix_unip [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (γ : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hγ : ∀ b : F, γ (unipSL b) = unipSL b) (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    γ (γ x) = x := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  obtain ⟨σ, h, hform⟩ := factAutSL2Char2_holds F n hF γ
  have hcomm : h * unipSL 1 = unipSL 1 * h := by
    have h1 := hγ 1
    rw [hform, map_unipSL, map_one] at h1
    calc h * unipSL 1 = h * unipSL 1 * h⁻¹ * h := by group
      _ = unipSL 1 * h := by rw [h1]
  set c := (h : Matrix (Fin 2) (Fin 2) F) 0 1
  have hh : h = unipSL c := eq_unipSL_of_commute hcomm
  have hinv : h⁻¹ = unipSL c := by
    rw [hh, inv_eq_of_mul_eq_one_right (unipSL_mul_self c)]
  have hσ : ∀ b : F, σ b = b := by
    intro b
    have hb := hγ b
    rw [hform, map_unipSL, hinv, hh, unipSL_mul_unipSL, unipSL_mul_unipSL] at hb
    have hb' := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hb
    simp only [coe_unipSL] at hb'
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.empty_val'] at hb'
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination hb' - c * h2
  have hid : ∀ y : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.map σ.toRingHom y = y := by
    intro y
    ext i j
    simp [hσ]
  rw [hform, hform, hid, hid, hinv, hh]
  calc unipSL c * (unipSL c * x * unipSL c) * unipSL c
      = (unipSL c * unipSL c) * x * (unipSL c * unipSL c) := by group
    _ = x := by rw [unipSL_mul_self, one_mul, mul_one]

theorem sq_eq_of_fix_sylow [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (β : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.index) (hβ : ∀ p ∈ P, β p = p) (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    β (β x) = x := by
  obtain ⟨g, -, hg⟩ := exists_conj_unip hF hP hidx
  let γ : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    ((MulAut.conj g⁻¹).trans β).trans (MulAut.conj g)
  have hγ : ∀ y, γ y = g * β (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ := fun y => rfl
  have hfix : ∀ b : F, γ (unipSL b) = unipSL b := by
    intro b
    rw [hγ, inv_inv, hβ _ (hg b)]
    group
  have key := sq_eq_of_fix_unip hF γ hfix (g * x * g⁻¹)
  rw [hγ, hγ] at key
  have e1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rw [e1] at key
  have e2 : g⁻¹ * (g * β x * g⁻¹) * g⁻¹⁻¹ = β x := by group
  rw [e2] at key
  calc β (β x) = g⁻¹ * (g * β (β x) * g⁻¹) * g := by group
    _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [key]
    _ = x := by group

theorem eq_one_of_fix_quot {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN2 : IsPGroup 2 N) (α : MulAut X) (hodd : Odd (orderOf α)) (hfN : ∀ c ∈ N, α c = c)
    (hq : ∀ x, α x * x⁻¹ ∈ N) : α = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext x
  rw [MulAut.one_apply]
  set c := α x * x⁻¹ with hc
  have hpow : ∀ k : ℕ, (α ^ k) x = c ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfN c (hq x), pow_succ]
      simp [hc, mul_assoc]
  have hk := hpow (orderOf α)
  rw [pow_orderOf_eq_one, MulAut.one_apply] at hk
  have hc1 : c ^ orderOf α = 1 := by
    have := congrArg (· * x⁻¹) hk
    simpa using this.symm
  have hcN : (⟨c, hq x⟩ : N) ^ orderOf α = 1 := Subtype.ext (by simpa using hc1)
  obtain ⟨k, hk'⟩ := hN2 ⟨c, hq x⟩
  have hdvd : orderOf (⟨c, hq x⟩ : N) ∣ orderOf α := orderOf_dvd_of_pow_eq_one hcN
  have hdvd2 : orderOf (⟨c, hq x⟩ : N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h1 : orderOf (⟨c, hq x⟩ : N) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
    rcases j with _ | j
    · simpa using hj
    · exfalso
      rw [hj, pow_succ] at hdvd
      exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr (dvd_of_mul_left_dvd hdvd))
  have hc' : c = 1 := by
    have := orderOf_eq_one_iff.mp h1
    exact congrArg Subtype.val this
  rw [hc] at hc'
  exact mul_inv_eq_one.mp hc'

end C11AmS

open SecA C11AmS

theorem factOddAutCentSylow_holds :
    ∀ (X : Type) [Group X] [Finite X] (F : Type) [Field F] [Finite F] (n : ℕ),
      Nat.card F = 2 ^ n →
      Nonempty (X ⧸ CFSG.pCore 2 X ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
      ∀ (S : Sylow 2 X) (α : MulAut X), Odd (orderOf α) → (∀ s ∈ (S : Subgroup X), α s = s) →
        α = 1 := by
  intro X _ _ F _ _ n hF ⟨ψ⟩ S α hodd hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 X with hN
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup (p := 2) (G := X)
  have hNS : N ≤ (S : Subgroup X) := hN2.le_sylow_of_normal S
  have hNmap : ∀ φ : MulAut X, N.map φ.toMonoidHom = N := fun φ =>
    Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  set α₂ := α * α with hα₂
  let β : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (ψ.symm.trans (QuotientGroup.congr N N α (hNmap α))).trans ψ
  have hβ : ∀ x : X, β (ψ (x : X ⧸ N)) = ψ ((α x : X) : X ⧸ N) := by
    intro x
    change ψ (QuotientGroup.congr N N α (hNmap α) (ψ.symm (ψ (x : X ⧸ N)))) = _
    rw [ψ.symm_apply_apply]
    rfl
  let f : X →* Matrix.SpecialLinearGroup (Fin 2) F := ψ.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := ψ.surjective.comp (QuotientGroup.mk'_surjective N)
  let P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) := S.mapSurjective hf
  have hPfix : ∀ p ∈ (P : Subgroup _), β p = p := by
    intro p hp
    rw [Sylow.coe_mapSurjective] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    change β (ψ (s : X ⧸ N)) = ψ (s : X ⧸ N)
    rw [hβ, hfix s hs]
  have hsq := sq_eq_of_fix_sylow hF β P.isPGroup' P.not_dvd_index hPfix
  have hq : ∀ x : X, α₂ x * x⁻¹ ∈ N := by
    intro x
    have h1 := hsq (ψ (x : X ⧸ N))
    rw [hβ, hβ] at h1
    have h2 : ((α (α x) : X) : X ⧸ N) = (x : X ⧸ N) := ψ.injective h1
    rw [QuotientGroup.eq_iff_div_mem] at h2
    simpa [hα₂, div_eq_mul_inv] using h2
  have hfN : ∀ c ∈ N, α₂ c = c := by
    intro c hc
    rw [hα₂, MulAut.mul_apply, hfix c (hNS hc), hfix c (hNS hc)]
  have hodd₂ : Odd (orderOf α₂) := by
    rw [hα₂, ← sq]
    exact Odd.of_dvd_nat hodd (orderOf_pow_dvd 2)
  have h1 : α₂ = 1 := eq_one_of_fix_quot hN2 α₂ hodd₂ hfN hq
  obtain ⟨k, hk⟩ := hodd
  have hpow : α ^ orderOf α = 1 := pow_orderOf_eq_one α
  rw [hk, pow_succ, pow_mul, sq, ← hα₂, h1, one_pow, one_mul] at hpow
  exact hpow

end CFSG.Quasithin.Vol2.Ch10.SecB
