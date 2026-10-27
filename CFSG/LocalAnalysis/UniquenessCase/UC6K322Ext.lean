module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K322Lin
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K322Ext

open Subgroup CFSG.RepresentationTheory

section Abstract

variable {H : Type*} [Group H] [Finite H]

theorem eq_one_of_sq_eq_one_of_mem {Z : Subgroup H} (hZ : Nat.card Z = 3) {z : H} (hz : z ∈ Z)
    (h2 : z ^ 2 = 1) : z = 1 := by
  have h3 : z ^ 3 = 1 := by
    have : (⟨z, hz⟩ : ↥Z) ^ Nat.card ↥Z = 1 := pow_card_eq_one'
    rw [hZ] at this
    simpa using congrArg Subtype.val this
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3]; group

theorem commutator_mem_center (hex : CFSG.IsExtraspecialPGroup 3 H) (a b : H) :
    a * b * a⁻¹ * b⁻¹ ∈ center H := by
  rw [← hex.2.1]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

theorem pow_three_mem_center (hcard : Nat.card H = 27) (hex : CFSG.IsExtraspecialPGroup 3 H)
    (y : H) : y ^ 3 ∈ center H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Nat.card (center H) = 3 := hex.2.2.2
  have hQ : Nat.card (H ⧸ center H) = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center H)
    rw [hcard, hZ] at h
    omega
  set q : H ⧸ center H := (y : H ⧸ center H) with hq
  have hdvd : orderOf q ∣ 3 ^ 2 := by
    rw [show 3 ^ 2 = 9 by norm_num, ← hQ]
    exact orderOf_dvd_natCard q
  obtain ⟨k, hk, hkq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk2 : k ≠ 2 := by
    rintro rfl
    haveI : IsCyclic (H ⧸ center H) := isCyclic_of_orderOf_eq_card q (by rw [hkq, hQ]; norm_num)
    have hcomm := commutative_of_cyclic_center_quotient (QuotientGroup.mk' (center H))
      (by rw [QuotientGroup.ker_mk'])
    have htop : center H = ⊤ := eq_top_iff.2 fun x _ =>
      Subgroup.mem_center_iff.2 fun g => hcomm g x
    rw [htop, Subgroup.card_top, hcard] at hZ
    norm_num at hZ
  have hq3 : q ^ 3 = 1 := by
    have h1 : orderOf q ∣ 3 := by
      rw [hkq]
      have hk1 : k ≤ 1 := by omega
      interval_cases k <;> norm_num
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hq3
  exact hq3

theorem eq_or_exponent_three (hcard : Nat.card H = 27) (hex : CFSG.IsExtraspecialPGroup 3 H)
    (φ : MulAut H) (hφ2 : ∀ y, φ (φ y) = y) (hφZ : ∀ z ∈ center H, φ z = z) :
    (∀ y, φ y = y) ∨ ∀ y : H, y ^ 3 = 1 := by
  have hZ : Nat.card (center H) = 3 := hex.2.2.2
  have hcen : ∀ z ∈ center H, ∀ g : H, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.1 hz g
  have hZ3 : ∀ z ∈ center H, z ^ 3 = 1 := by
    intro z hz
    have : (⟨z, hz⟩ : ↥(center H)) ^ Nat.card ↥(center H) = 1 := pow_card_eq_one'
    rw [hZ] at this
    simpa using congrArg Subtype.val this
  by_cases hC : ∀ y : H, y⁻¹ * φ y ∈ center H
  ·
    left
    intro y
    obtain ⟨z, hzdef⟩ : ∃ z, z = y⁻¹ * φ y := ⟨_, rfl⟩
    have hzZ : z ∈ center H := hzdef ▸ hC y
    have hφy : φ y = y * z := by rw [hzdef]; group
    have h1 : φ z = z := hφZ z hzZ
    have h2 : y = y * z * z := by
      calc y = φ (φ y) := (hφ2 y).symm
        _ = φ (y * z) := by rw [hφy]
        _ = y * z * z := by rw [map_mul, hφy, h1]
    have hz2 : z ^ 2 = 1 := by
      have : y * (z * z) = y * 1 := by rw [mul_one, ← mul_assoc]; exact h2.symm
      rw [sq]
      exact mul_left_cancel this
    have hz1 : z = 1 := eq_one_of_sq_eq_one_of_mem hZ hzZ hz2
    rw [hφy, hz1, mul_one]
  by_cases hB : ∀ y : H, y * φ y ∈ center H
  ·
    right
    intro y
    obtain ⟨z, hzdef⟩ : ∃ z, z = y * φ y := ⟨_, rfl⟩
    have hzZ : z ∈ center H := hzdef ▸ hB y
    have hφy : φ y = y⁻¹ * z := by rw [hzdef]; group
    have hy3 := pow_three_mem_center hcard hex y
    have h1 : φ (y ^ 3) = y ^ 3 := hφZ _ hy3
    have h2 : φ (y ^ 3) = (y ^ 3)⁻¹ := by
      rw [map_pow, hφy]
      have hc : Commute y⁻¹ z := hcen z hzZ y⁻¹
      rw [hc.mul_pow 3, hZ3 z hzZ, mul_one, inv_pow]
    have h6 : (y ^ 3) ^ 2 = 1 := by
      rw [sq]
      calc y ^ 3 * y ^ 3 = y ^ 3 * φ (y ^ 3) := by rw [h1]
        _ = 1 := by rw [h2, mul_inv_cancel]
    exact eq_one_of_sq_eq_one_of_mem hZ hy3 h6
  exfalso
  push Not at hC hB
  obtain ⟨y₂, hb⟩ := hC
  obtain ⟨y₁, ha⟩ := hB
  obtain ⟨a, hadef⟩ : ∃ a, a = y₁ * φ y₁ := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = y₂⁻¹ * φ y₂ := ⟨_, rfl⟩
  rw [← hadef] at ha
  rw [← hbdef] at hb
  have hφb : φ b = b⁻¹ := by rw [hbdef, map_mul, map_inv, hφ2]; group
  obtain ⟨z₁, hz₁def⟩ : ∃ z₁, z₁ = a⁻¹ * φ a := ⟨_, rfl⟩
  have hz₁ : z₁ ∈ center H := by
    have h := commutator_mem_center hex (φ y₁)⁻¹ y₁⁻¹
    have he : z₁ = (φ y₁)⁻¹ * y₁⁻¹ * (φ y₁)⁻¹⁻¹ * y₁⁻¹⁻¹ := by
      rw [hz₁def, hadef, map_mul, hφ2]
      group
    rw [he]
    exact h
  have hφa : φ a = a * z₁ := by rw [hz₁def]; group
  obtain ⟨c, hcdef⟩ : ∃ c, c = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ center H := hcdef ▸ commutator_mem_center hex a b
  have hab : a * b = b * a := by
    have h1 : φ c = c := hφZ c hcZ
    have h2 : φ c = c⁻¹ := by
      have hz₁c := hcen z₁ hz₁
      have hci := hcen c⁻¹ (Subgroup.inv_mem _ hcZ)
      calc φ c = a * z₁ * b⁻¹ * (a * z₁)⁻¹ * b⁻¹⁻¹ := by
            rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hφa, hφb]
        _ = a * b⁻¹ * a⁻¹ * b := by
            have : z₁ * b⁻¹ = b⁻¹ * z₁ := (hz₁c b⁻¹).symm
            calc a * z₁ * b⁻¹ * (a * z₁)⁻¹ * b⁻¹⁻¹ = a * (z₁ * b⁻¹) * z₁⁻¹ * a⁻¹ * b := by
                  group
              _ = a * b⁻¹ * a⁻¹ * b := by rw [this]; group
        _ = c⁻¹ := by
            have hcb : a * b * a⁻¹ = c * b := by rw [hcdef]; group
            have h3 : a * b⁻¹ * a⁻¹ = b⁻¹ * c⁻¹ := by
              have := congrArg (·⁻¹) hcb
              simp only [mul_inv_rev, inv_inv] at this
              rw [← this]
              group
            rw [h3, mul_assoc, ← hci b, ← mul_assoc, inv_mul_cancel, one_mul]
    have hc2 : c ^ 2 = 1 := by
      rw [sq]
      calc c * c = c * φ c := by rw [h1]
        _ = 1 := by rw [h2, mul_inv_cancel]
    have hc1 := eq_one_of_sq_eq_one_of_mem hZ hcZ hc2
    rw [hcdef] at hc1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hc1, one_mul]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup H := zpowers a ⊔ center H with hAdef
  set C : Subgroup H := centralizer {a} with hCdef
  have hAC : A ≤ C := sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
    (fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (hcen z hz a).symm)
  have hZA : center H < A := lt_of_le_of_ne le_sup_right (fun h => ha (by
    rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)))
  have hCne : C ≠ ⊤ := fun h => ha (by
    refine Subgroup.mem_center_iff.2 fun g => ?_
    have hg : g ∈ C := h ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hcardA : 9 ≤ Nat.card A := by
    have h1 := Subgroup.card_lt_of_lt hZA
    rw [hZ] at h1
    have h2 : Nat.card A ∣ 3 ^ 3 := by
      rw [show 3 ^ 3 = 27 by norm_num, ← hcard]
      exact Subgroup.card_subgroup_dvd_card A
    obtain ⟨k, hk, hkA⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    rw [hkA] at h1 ⊢
    interval_cases k <;> simp_all
  have hcardC : Nat.card C ≤ 9 := by
    have h1 : Nat.card C ∣ 3 ^ 3 := by
      rw [show 3 ^ 3 = 27 by norm_num, ← hcard]
      exact Subgroup.card_subgroup_dvd_card C
    have h2 : Nat.card C ≠ 27 := fun h =>
      hCne (Subgroup.card_eq_iff_eq_top C |>.1 (h.trans hcard.symm))
    obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    rw [hkC] at h2 ⊢
    interval_cases k <;> simp_all
  have hAeq : A = C := Subgroup.eq_of_le_of_card_ge hAC (by omega)
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hab.symm
  rw [← hAeq] at hbC
  have hbA : b ∈ (↑(zpowers a ⊔ center H) : Set H) := hbC
  rw [Subgroup.mul_normal] at hbA
  obtain ⟨u, hu, z, hz, hbuz⟩ := hbA
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hbuz' : b = a ^ k * z := hbuz.symm
  have hφu : φ (a ^ k) = a ^ k * z₁ ^ k := by
    rw [map_zpow, hφa]
    exact Commute.mul_zpow (hcen z₁ hz₁ a) k
  have hzk : z₁ ^ k ∈ center H := Subgroup.zpow_mem _ hz₁ k
  have hb2 : b ^ 2 ∈ center H := by
    have h1 : φ b = b * z₁ ^ k := by
      rw [hbuz', map_mul, hφu, hφZ z hz]
      calc a ^ k * z₁ ^ k * z = a ^ k * (z₁ ^ k * z) := by group
        _ = a ^ k * (z * z₁ ^ k) := by rw [hcen (z₁ ^ k) hzk z]
        _ = a ^ k * z * z₁ ^ k := by group
    rw [hφb] at h1
    have : b ^ 2 = (z₁ ^ k)⁻¹ := by
      rw [sq]
      calc b * b = b * (b * z₁ ^ k) * (z₁ ^ k)⁻¹ := by group
        _ = (z₁ ^ k)⁻¹ := by rw [← h1, mul_inv_cancel, one_mul]
    rw [this]
    exact Subgroup.inv_mem _ hzk
  apply hb
  have hb3 := pow_three_mem_center hcard hex b
  have : b = b ^ 3 * (b ^ 2)⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ hb3 (Subgroup.inv_mem _ hb2)

end Abstract

section Matrix

open Matrix Polynomial

variable {F : Type*} [Field F]

theorem eq_scalar_of_commute_of_pow_three {n : ℕ} {H : Subgroup (GL (Fin n) F)}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hn : 0 < n) {ω : F} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) {z : GL (Fin n) F}
    (hz : ∀ x ∈ H, (x : Matrix (Fin n) (Fin n) F) * z = z * x) (hz3 : z ^ 3 = 1) :
    ∃ c : F, (z : Matrix (Fin n) (Fin n) F) = algebraMap F (Matrix (Fin n) (Fin n) F) c := by
  set Z : Matrix (Fin n) (Fin n) F := (z : Matrix (Fin n) (Fin n) F) with hZdef
  set ι := algebraMap F (Matrix (Fin n) (Fin n) F)
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by ring_nf; rw [hω3]; ring
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hω1)
  have hpoly : (X - 1) * (X - C ω) * (X - C (ω ^ 2)) = (X ^ 3 - 1 : F[X]) := by
    have h : (X - 1) * (X - C ω) * (X - C (ω ^ 2)) =
        (X ^ 3 - C (1 + ω + ω ^ 2) * X ^ 2 + C (ω + ω ^ 2 + ω ^ 3) * X - C (ω ^ 3) : F[X]) := by
      simp only [map_add, map_pow, map_one]
      ring
    have h2 : ω + ω ^ 2 + ω ^ 3 = 0 := by rw [hω3]; linear_combination hsum
    rw [h, hsum, h2, hω3, map_zero, map_one]
    ring
  have hZ3 : Z ^ 3 = 1 := by
    rw [hZdef, ← Units.val_pow_eq_pow_val, hz3, Units.val_one]
  have hprod : (Z - 1) * (Z - ι ω) * (Z - ι (ω ^ 2)) = 0 := by
    have h := congrArg (aeval Z) hpoly
    simp only [map_mul, map_sub, map_one, aeval_X, aeval_C, aeval_X_pow] at h
    rw [hZ3, sub_self] at h
    exact h
  have hcomm : ∀ c : F, ∀ x ∈ H, (x : Matrix (Fin n) (Fin n) F) * (Z - ι c) =
      (Z - ι c) * x := by
    intro c x hx
    rw [Matrix.mul_sub, Matrix.sub_mul, hz x hx, ← Algebra.commutes c]
  have hcomm1 : ∀ x ∈ H, (x : Matrix (Fin n) (Fin n) F) * (Z - 1) = (Z - 1) * x := by
    intro x hx
    rw [Matrix.mul_sub, Matrix.sub_mul, hz x hx, Matrix.mul_one, Matrix.one_mul]
  rcases K322Lin.eq_zero_or_injective_of_commute hirr hcomm1 with h1 | h1
  · exact ⟨1, by rw [map_one]; exact sub_eq_zero.1 h1⟩
  rcases K322Lin.eq_zero_or_injective_of_commute hirr (hcomm ω) with h2 | h2
  · exact ⟨ω, sub_eq_zero.1 h2⟩
  rcases K322Lin.eq_zero_or_injective_of_commute hirr (hcomm (ω ^ 2)) with h3 | h3
  · exact ⟨ω ^ 2, sub_eq_zero.1 h3⟩
  exfalso
  have i : Fin n := ⟨0, hn⟩
  have hv : (Pi.single i (1 : F) : Fin n → F) ≠ 0 := fun h => by
    have := congrFun h i
    simp at this
  apply hv
  apply h3
  apply h2
  apply h1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hprod, Matrix.zero_mulVec]

theorem exponent_three_of_involution {H : Subgroup (GL (Fin 3) F)}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hcard : Nat.card H = 27)
    (hex : CFSG.IsExtraspecialPGroup 3 ↥H) {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {t : GL (Fin 3) F} (ht2 : t * t = 1) (htH : ∀ y ∈ H, t * y * t⁻¹ ∈ H)
    (hfix : Module.finrank F
      (LinearMap.ker (Matrix.toLin' ((t : Matrix (Fin 3) (Fin 3) F) - 1))) = 1) :
    ∀ y ∈ H, y ^ 3 = 1 := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hφφ : ∀ y : GL (Fin 3) F, t * (t * y * t⁻¹) * t⁻¹ = y := fun y => by
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
      _ = y := by rw [ht2]; group
  let φ : MulAut ↥H :=
    { toFun := fun y => ⟨t * y * t⁻¹, htH y y.2⟩
      invFun := fun y => ⟨t * y * t⁻¹, htH y y.2⟩
      left_inv := fun y => Subtype.ext (hφφ y)
      right_inv := fun y => Subtype.ext (hφφ y)
      map_mul' := fun a b => Subtype.ext (by
        show t * (a * b : GL (Fin 3) F) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹)
        group) }
  have hφ : ∀ y : ↥H, ((φ y : ↥H) : GL (Fin 3) F) = t * y * t⁻¹ := fun y => rfl
  have hφ2 : ∀ y, φ (φ y) = y := fun y => Subtype.ext (by rw [hφ, hφ, hφφ])
  have hZ : Nat.card (center ↥H) = 3 := hex.2.2.2
  have hφZ : ∀ z ∈ center ↥H, φ z = z := by
    intro z hz
    have hz3 : (z : GL (Fin 3) F) ^ 3 = 1 := by
      have h1 : (⟨z, hz⟩ : ↥(center ↥H)) ^ Nat.card ↥(center ↥H) = 1 := pow_card_eq_one'
      rw [hZ] at h1
      have h2 : z ^ 3 = 1 := by
        have := congrArg Subtype.val h1
        rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
      have := congrArg Subtype.val h2
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    have hcomm : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) F) * (z : GL (Fin 3) F) =
        ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * x := by
      intro x hx
      have h := Subgroup.mem_center_iff.1 hz ⟨x, hx⟩
      have h2 := congrArg (fun w : ↥H => ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
      simpa only [Subgroup.coe_mul, Units.val_mul] using h2
    obtain ⟨c, hc⟩ := eq_scalar_of_commute_of_pow_three hirr (by norm_num) hω3 hω1 hcomm hz3
    apply Subtype.ext
    rw [hφ]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc, ← Algebra.commutes c, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  haveI : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rcases eq_or_exponent_three hcard hex φ hφ2 hφZ with hid | hexp
  · exfalso
    set K : Submodule F (Fin 3 → F) :=
      LinearMap.ker (Matrix.toLin' ((t : Matrix (Fin 3) (Fin 3) F) - 1))
    have hmemK : ∀ z, z ∈ K ↔ (t : Matrix (Fin 3) (Fin 3) F) *ᵥ z = z := fun z => by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
        sub_eq_zero]
    have htcomm : ∀ x ∈ H, (t : Matrix (Fin 3) (Fin 3) F) * x = x * t := by
      intro x hx
      have h := congrArg (fun w : ↥H => ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        (hid ⟨x, hx⟩)
      simp only [hφ] at h
      calc (t : Matrix (Fin 3) (Fin 3) F) * x =
            ((t * x * t⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * t := by
            rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
              ← Units.val_mul t⁻¹, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = x * t := by rw [h]
    rcases hirr K (fun g w hw => by
        have hg : (H.subtype g : GL (Fin 3) F) = (g : GL (Fin 3) F) := rfl
        rw [hmemK] at hw ⊢
        rw [hg, Matrix.mulVec_mulVec, htcomm g g.2, ← Matrix.mulVec_mulVec, hw]) with hb | ht
    · rw [hb, finrank_bot] at hfix
      exact zero_ne_one hfix
    · rw [ht, finrank_top, Module.finrank_fin_fun] at hfix
      norm_num at hfix
  · intro y hy
    simpa using congrArg Subtype.val (hexp ⟨y, hy⟩)

end Matrix

end CFSG.LocalAnalysis.UniquenessCase.UC6.K322Ext
