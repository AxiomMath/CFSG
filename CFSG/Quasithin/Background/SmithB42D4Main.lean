module

public import CFSG.Quasithin.Background.SmithB42D4Line
public import CFSG.Quasithin.Background.SmithB42D4Sep
public import CFSG.Quasithin.Background.SmithB42D4Out
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality

public section

namespace CFSG.Quasithin.B42D4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.Quasithin.B42Disp

section FieldData

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

omit [Finite K] in
include hf hK in
theorem charP_two_of_card : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    (k := f * 3) (by omega) (by rw [hK, ← pow_mul])

include hK hσ in
theorem sigma_cube : σ.toRingHom ^ 3 = 1 :=
  RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσ c

omit [Finite K] in
include hf hK hσ in
theorem card_fixedField : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f := by
  have h := card_orbitField_D4_orientation Nat.prime_two hf hK (r := 1) (Or.inl rfl)
    (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) ⟨1, by decide⟩
  have h1 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  rw [h1, pow_one] at h
  rw [← h]
  refine Nat.card_congr ⟨fun x => ⟨x, ?_⟩, fun x => ⟨x, ?_⟩, fun x => rfl, fun x => rfl⟩
  · rw [mem_orbitField, h1, pow_one]; exact x.2
  · have := (mem_orbitField (t := TwistTag.D4) (σ := σ.toRingHom) (a := ⟨1, by decide⟩)).1 x.2
    rw [h1, pow_one] at this
    exact this

omit [Finite K] in
include hf hK hσ in
theorem exists_sigma_ne : ∃ x : K, σ x ≠ x := by
  by_contra h
  push Not at h
  have hk := card_fixedField hf hK σ hσ
  have htop : trialityFixedField K σ.toRingHom = ⊤ := eq_top_iff.2 fun c _ => h c
  rw [htop, Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun c : K => c ∈ (⊤ : Subfield K))
    (fun c => Subfield.mem_top c)), hK] at hk
  have : 2 ^ (f * 3) = 2 ^ f := by rw [pow_mul]; exact hk
  have := Nat.pow_right_injective le_rfl this
  omega

include hf hK hσ in
theorem exists_spanning : ∃ t₁ t₂ t₃ : K, ∀ x : K, ∃ a₁ a₂ a₃ : K, σ a₁ = a₁ ∧ σ a₂ = a₂ ∧
    σ a₃ = a₃ ∧ x = a₁ * t₁ + a₂ * t₂ + a₃ * t₃ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set k := trialityFixedField K σ.toRingHom
  have : Fintype k := Fintype.ofFinite k
  have hcard := Module.card_eq_pow_finrank (K := k) (V := K)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, card_fixedField hf hK σ hσ,
    ← pow_mul, ← pow_mul] at hcard
  have h3 : Module.finrank k K = 3 := by
    have := Nat.pow_right_injective le_rfl hcard
    exact (Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) this).symm
  set b := Module.finBasisOfFinrankEq k K h3
  refine ⟨b 0, b 1, b 2, fun x => ?_⟩
  refine ⟨b.repr x 0, b.repr x 1, b.repr x 2, (b.repr x 0).2, (b.repr x 1).2, (b.repr x 2).2, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  rw [Fin.sum_univ_three]
  simp only [Subfield.smul_def]
  rfl

end FieldData

theorem dvd_two_pow_sub_one_iff {ℓ : ℕ} (n : ℕ) :
    ℓ ∣ 2 ^ n - 1 ↔ (2 : ZMod ℓ) ^ n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero]
  push_cast
  rfl

theorem not_dvd_card_SL2 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hord : orderOf (2 : ZMod ℓ) = 12 * f) :
    ¬ ℓ ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hQ : Fintype.card K = 2 ^ (3 * f) := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
  have hno : ∀ n, 0 < n → n < 12 * f → ¬ ℓ ∣ 2 ^ n - 1 := fun n hn hlt h => by
    rw [dvd_two_pow_sub_one_iff] at h
    have := Nat.le_of_dvd hn (hord ▸ orderOf_dvd_of_pow_eq_one h)
    omega
  intro h
  rw [Matrix.card_SL_field 2, Fin.prod_univ_two, hQ] at h
  have hdvd : (2 ^ (3 * f) - 1) ∣ ((2 ^ (3 * f)) ^ 2 - (2 ^ (3 * f)) ^ ((0 : Fin 2) : ℕ)) *
      ((2 ^ (3 * f)) ^ 2 - (2 ^ (3 * f)) ^ ((1 : Fin 2) : ℕ)) := by
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [show (2 ^ (3 * f)) ^ 2 - 2 ^ (3 * f) = 2 ^ (3 * f) * (2 ^ (3 * f) - 1) by
      rw [Nat.mul_sub_one, sq]]
    exact Dvd.dvd.mul_left (dvd_mul_left _ _) _
  have h2 := h.trans (Nat.div_dvd_of_dvd hdvd)
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h2
  rcases (Nat.Prime.dvd_mul hℓ).1 h2 with h3 | h3
  · rw [← pow_mul] at h3
    exact hno (3 * f * 2) (by omega) (by omega) h3
  · rw [show (2 ^ (3 * f)) ^ 2 - 2 ^ (3 * f) = 2 ^ (3 * f) * (2 ^ (3 * f) - 1) by
      rw [Nat.mul_sub_one, sq]] at h3
    rcases (Nat.Prime.dvd_mul hℓ).1 h3 with h4 | h4
    · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h4))
    · exact hno (3 * f) (by omega) (by omega) h4

section Classes

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K

include hf hK hσ in
theorem not_conj_H_of_inverts {y t : C₀} (hyt : y * t * y⁻¹ = t⁻¹) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hord : orderOf (2 : ZMod ℓ) = 12 * f) (hdvd : ℓ ∣ orderOf t) :
    ¬ ConjC σ (y : ModGL TwistTag.D4.tag K) (Xr d4H 1) := by
  have := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  rintro ⟨c, hc, hcy⟩
  have hyt' : (y : ModGL TwistTag.D4.tag K) * t * (y : ModGL TwistTag.D4.tag K)⁻¹ =
      (t : ModGL TwistTag.D4.tag K)⁻¹ := by
    have h := congrArg Subtype.val hyt
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have ht'C : c * (t : ModGL TwistTag.D4.tag K) * c⁻¹ ∈ C₀ :=
    mul_mem (mul_mem hc t.2) (inv_mem hc)
  have hz : Xr d4H 1 * (c * t * c⁻¹) * (Xr d4H 1)⁻¹ = (c * t * c⁻¹)⁻¹ := by
    rw [← hcy]
    calc c * y * c⁻¹ * (c * t * c⁻¹) * (c * y * c⁻¹)⁻¹ =
        c * ((y : ModGL TwistTag.D4.tag K) * t * (y : ModGL TwistTag.D4.tag K)⁻¹) * c⁻¹ := by
          group
      _ = (c * t * c⁻¹)⁻¹ := by rw [hyt']; group
  have hprod : Xr d4H 1 * ((c * t * c⁻¹) * Xr d4H 1 * (c * t * c⁻¹)⁻¹) =
      (c * (t : ModGL TwistTag.D4.tag K) * c⁻¹)⁻¹ *
        (c * (t : ModGL TwistTag.D4.tag K) * c⁻¹)⁻¹ := by
    have hzinv : (Xr d4H (1 : K))⁻¹ = Xr d4H 1 := Xr_inv _ _
    calc Xr d4H 1 * ((c * t * c⁻¹) * Xr d4H 1 * (c * t * c⁻¹)⁻¹) =
        (Xr d4H 1 * (c * t * c⁻¹) * (Xr d4H 1)⁻¹) * (c * t * c⁻¹)⁻¹ := by rw [hzinv]; group
      _ = _ := by rw [hz]
  have hot : orderOf (c * (t : ModGL TwistTag.D4.tag K) * c⁻¹) = orderOf t := by
    rw [orderOf_conj', Subgroup.orderOf_coe]
  have hdvd' : ℓ ∣ orderOf (Xr d4H 1 * ((c * t * c⁻¹) * Xr d4H 1 * (c * t * c⁻¹)⁻¹)) := by
    rw [hprod, ← sq]
    exact dvd_orderOf_sq hℓ hℓ2 (by rw [orderOf_inv, hot]; exact hdvd)
  rcases order_mul_conj σ hσ3 ht'C with h4 | hSL
  · have h2 : ℓ ∣ 2 ^ 2 := hdvd'.trans h4
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h2))
  · exact not_dvd_card_SL2 hf hK hℓ hℓ2 hord (hdvd'.trans hSL)

include hf hK hσ in
theorem exists_B_inverting : ∃ (ℓ : ℕ) (y t : C₀), ℓ.Prime ∧ ℓ ≠ 2 ∧
    orderOf (2 : ZMod ℓ) = 12 * f ∧ y * t * y⁻¹ = t⁻¹ ∧ orderOf t = ℓ ∧
      ConjC σ (y : ModGL TwistTag.D4.tag K) (ox₁ σ 1) := by
  have := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  obtain ⟨ℓ, hℓ, hℓ2, hord⟩ := exists_prime_orderOf_two_eq (12 * f) (by omega) (by omega)
  obtain ⟨hℓ3, hℓd⟩ := ppd_twelve hℓ hf hord
  obtain ⟨y, t, hy, hyt, hto⟩ :=
    exists_involution_inverting Nat.prime_two hf K hK σ hσ hℓ hℓ3 hℓd
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [one_mul, inv_one, mul_one] at hyt
    have h2 : t ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [hyt]
      exact inv_mul_cancel t
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hto] at h3
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h3)
  rcases involution_conj σ hσ3 y hy hy1 with hH | hx
  · exact absurd hH (not_conj_H_of_inverts hf hK σ hσ hyt hℓ hℓ2 hord (by rw [hto]))
  · exact ⟨ℓ, y, t, hℓ, hℓ2, hord, hyt, hto, hx⟩

include hf hK hσ in
theorem negC_mem_C0 {γ : K} (hγ : σ γ = γ) : Xr (-d4C) γ ∈ C₀ := by
  have := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  rw [← nB_C]
  exact mul_mem (mul_mem (nB_mem σ) (Xr_C_mem_C0 σ hσ3 hγ)) (inv_mem (nB_mem σ))

include hf hK hσ in
theorem lineGenAt_of_pure (E : Subgroup C₀) (hE : E ≠ ⊥) (hEa : IsElem2 E)
    (hB : ∀ ξ ∈ E, ξ ≠ 1 → ¬ ConjC σ (ξ : ModGL TwistTag.D4.tag K) (ox₁ σ 1)) :
    LineGenAt C₀ E := by
  classical
  have := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  have hk := card_fixedField hf hK σ hσ
  have hσ1 := exists_sigma_ne hf hK σ hσ
  obtain ⟨t₁, t₂, t₃, hspan⟩ := exists_spanning hf hK σ hσ
  obtain ⟨ℓ, -, t, hℓ, hℓ2, hord, -, hto, -⟩ := exists_B_inverting hf hK σ hσ
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hEa.2 x hx
  obtain ⟨g₀, hg₀, hline₀⟩ := elem_line σ hσ3 E hEa.1 hsq hB
  have hline : ∀ x ∈ E, ∃ e f : K, σ e = e ∧ σ f = f ∧
      (x : ModGL TwistTag.D4.tag K) = g₀ * lam K e f * g₀⁻¹ := hline₀
  obtain ⟨⟨v, hvE⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  obtain ⟨e₀, f₀, he₀, hf₀, hv⟩ := hline v hvE
  have hne : e₀ ≠ 0 ∨ f₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hv1'
    apply Subtype.ext
    rw [hv, h.1, h.2]
    simp [lam, pinnedX_zero]
  set G₀ : C₀ := ⟨g₀, hg₀⟩ with hG₀
  have : Fintype (trialityFixedField K σ.toRingHom) := Fintype.ofFinite _
  let u : trialityFixedField K σ.toRingHom × trialityFixedField K σ.toRingHom ×
      trialityFixedField K σ.toRingHom → ModGL TwistTag.D4.tag K :=
    fun p => Xr d4C p.1 * Xr (-d4C) p.2.1 * Xr d4C p.2.2
  have hu : ∀ p, u p ∈ C₀ := fun p => mul_mem (mul_mem (Xr_C_mem_C0 σ hσ3 p.1.2)
    (negC_mem_C0 hf hK σ hσ p.2.1.2)) (Xr_C_mem_C0 σ hσ3 p.2.2.2)
  set hs : List C₀ := (Finset.univ.toList).map fun p => G₀ * ⟨u p, hu p⟩ * G₀⁻¹ with hhs
  have hmem_hs : ∀ h ∈ hs, ∃ p, (h : ModGL TwistTag.D4.tag K) = g₀ * u p * g₀⁻¹ := by
    intro h hh
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hh
    exact ⟨p, rfl⟩
  let ΛM : Subgroup C₀ :=
    { carrier := {x | ∃ e f : K, σ e = e ∧ σ f = f ∧
        (x : ModGL TwistTag.D4.tag K) = g₀ * lam K e f * g₀⁻¹}
      mul_mem' := by
        rintro x y ⟨e, f, he, hf, hx⟩ ⟨e', f', he', hf', hy⟩
        refine ⟨e + e', f + f', by rw [map_add, he, he'], by rw [map_add, hf, hf'], ?_⟩
        rw [Subgroup.coe_mul, hx, hy, ← lam_mul]
        group
      one_mem' := ⟨0, 0, map_zero σ, map_zero σ, by
        simp [lam, pinnedX_zero]⟩
      inv_mem' := by
        rintro x ⟨e, f, he, hf, hx⟩
        refine ⟨e, f, he, hf, ?_⟩
        rw [Subgroup.coe_inv, hx, mul_inv_rev, mul_inv_rev, inv_inv, lam_inv, mul_assoc] }
  have hEΛ : ∀ a ∈ E, a ∈ ΛM := fun a ha => hline a ha
  have hconj : ∀ h ∈ hs, ∀ a ∈ E, h * a * h⁻¹ ∈ ΛM := by
    intro h hh a ha
    obtain ⟨p, hp⟩ := hmem_hs h hh
    obtain ⟨e, f, he, hf, hae⟩ := hline a ha
    have e1 : ((h * a * h⁻¹ : C₀) : ModGL TwistTag.D4.tag K) =
        g₀ * (u p * lam K e f * (u p)⁻¹) * g₀⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hp, hae]; group
    rw [conj3_lam] at e1
    have hp1 : σ (p.1 : K) = p.1 := p.1.2
    have hp2 : σ (p.2.1 : K) = p.2.1 := p.2.1.2
    have hp3 : σ (p.2.2 : K) = p.2.2 := p.2.2.2
    refine ⟨_, _, ?_, ?_, e1⟩
    · simp only [map_add, map_mul, he, hf, hp2, hp3]
    · simp only [map_add, map_mul, he, hf, hp1, hp2, hp3]
  set gsM : List C₀ := [1, ⟨nW0 K, nW0_mem σ⟩,
    ⟨ox₁ σ t₁ * nA K, mul_mem (ox₁_mem_C0 σ hσ3 t₁) (nA_mem σ)⟩,
    ⟨ox₁ σ t₂ * nA K, mul_mem (ox₁_mem_C0 σ hσ3 t₂) (nA_mem σ)⟩,
    ⟨ox₁ σ t₃ * nA K, mul_mem (ox₁_mem_C0 σ hσ3 t₃) (nA_mem σ)⟩] with hgsM
  set gs : List C₀ := gsM.map fun g => g * G₀⁻¹ with hgs
  refine ⟨ℓ, hs, gs, hℓ, hℓ2, ?_, ?_, ?_⟩
  ·
    intro h hh h' hh' a ha b hb
    obtain ⟨e, f, -, -, hx⟩ := hconj h hh a ha
    obtain ⟨e', f', -, -, hy⟩ := hconj h' hh' b hb
    apply Subtype.ext
    change ((h * a * h⁻¹ : C₀) : ModGL TwistTag.D4.tag K) *
        ((h' * b * h'⁻¹ : C₀) : ModGL TwistTag.D4.tag K) =
      ((h' * b * h'⁻¹ : C₀) : ModGL TwistTag.D4.tag K) *
        ((h * a * h⁻¹ : C₀) : ModGL TwistTag.D4.tag K)
    rw [hx, hy]
    calc g₀ * lam K e f * g₀⁻¹ * (g₀ * lam K e' f' * g₀⁻¹) =
        g₀ * (lam K e f * lam K e' f') * g₀⁻¹ := by group
      _ = g₀ * (lam K e' f' * lam K e f) * g₀⁻¹ := by rw [lam_comm]
      _ = _ := by group
  ·
    set T := {y : C₀ | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹} with hT
    set S := {y : C₀ | ∃ g ∈ gs, ∃ h ∈ hs, ∃ a ∈ E, y = g * (h * a * h⁻¹) * g⁻¹} with hS
    have hΛT : ∀ e f : K, σ e = e → σ f = f →
        ∃ w ∈ Subgroup.closure T, (w : ModGL TwistTag.D4.tag K) = g₀ * lam K e f * g₀⁻¹ := by
      intro e f he hf
      set S₀ : Subgroup (ModGL TwistTag.D4.tag K) :=
        ((Subgroup.closure T).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype).map
            (MulAut.conj g₀⁻¹).toMonoidHom
      have hS₀ : ∀ γ γ' γ'' : K, σ γ = γ → σ γ' = γ' → σ γ'' = γ'' →
          (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * lam K e₀ f₀ *
            (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'')⁻¹ ∈ S₀ := by
        intro γ γ' γ'' h1 h2 h3
        have hUC : Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'' ∈ graphFixedRootGroup TwistTag.D4 K
            σ.toRingHom := hu (⟨γ, h1⟩, ⟨γ', h2⟩, ⟨γ'', h3⟩)
        have hh : G₀ * ⟨Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'', hUC⟩ * G₀⁻¹ ∈ hs :=
          List.mem_map.2 ⟨(⟨γ, h1⟩, ⟨γ', h2⟩, ⟨γ'', h3⟩), Finset.mem_toList.2
            (Finset.mem_univ _), rfl⟩
        have hw : (G₀ * ⟨Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'', hUC⟩ * G₀⁻¹) * v *
            (G₀ * ⟨Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'', hUC⟩ * G₀⁻¹)⁻¹ ∈
              Subgroup.closure T := Subgroup.subset_closure ⟨_, hh, v, hvE, rfl⟩
        refine ⟨_, ⟨_, hw, rfl⟩, ?_⟩
        change g₀⁻¹ * (g₀ * (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * g₀⁻¹ * (v : ModGL
          TwistTag.D4.tag K) * (g₀ * (Xr d4C γ * Xr (-d4C) γ' * Xr d4C γ'') * g₀⁻¹)⁻¹) *
            g₀⁻¹⁻¹ = _
        rw [hv]
        group
      have hl := lam_closure (S := S₀) he₀ hf₀ hne hS₀ he hf
      obtain ⟨_, ⟨w, hw, rfl⟩, hw'⟩ := hl
      refine ⟨w, hw, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        Subgroup.coe_subtype] at hw'
      rw [← hw']; group
    have hTS : ∀ g ∈ gs, ∀ w ∈ Subgroup.closure T, g * w * g⁻¹ ∈ Subgroup.closure S := by
      intro g hg w hw
      have hle : (Subgroup.closure T).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
        rw [MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨y, ⟨h, hh, a, ha, rfl⟩, rfl⟩
        exact Subgroup.subset_closure ⟨g, hg, h, hh, a, ha, rfl⟩
      exact hle ⟨w, hw, rfl⟩
    set H' := (Subgroup.closure S).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype with hH'
    have hgen : ∀ g ∈ gsM, ∀ e f : K, σ e = e → σ f = f →
        (g : ModGL TwistTag.D4.tag K) * lam K e f * (g : ModGL TwistTag.D4.tag K)⁻¹ ∈ H' := by
      intro g hg e f he hf
      obtain ⟨w, hw, hw'⟩ := hΛT e f he hf
      refine ⟨g * G₀⁻¹ * w * (g * G₀⁻¹)⁻¹, hTS _ (List.mem_map.2 ⟨g, hg, rfl⟩) w hw, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hw', hG₀]
      group
    have hm1 : (1 : C₀) ∈ gsM := List.mem_cons_self
    have hm2 : (⟨nW0 K, nW0_mem σ⟩ : C₀) ∈ gsM := List.mem_cons_of_mem _ List.mem_cons_self
    have hm3 : ∀ s ∈ ({t₁, t₂, t₃} : Set K),
        (⟨ox₁ σ s * nA K, mul_mem (ox₁_mem_C0 σ hσ3 s) (nA_mem σ)⟩ : C₀) ∈ gsM := by
      intro s hs'
      rcases hs' with h | h | h
      · subst h
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · subst h
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self))
      · rw [Set.mem_singleton_iff] at h
        subst h
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self)))
    have hC : C₀ ≤ H' := by
      refine five_lines_generate σ hσ3 hσ1 hspan (fun e f he hf => ?_) (fun e f he hf => ?_)
        (fun s hs' e f he hf => hgen _ (hm3 s hs') e f he hf)
      · have := hgen 1 hm1 e f he hf
        rwa [Subgroup.coe_one, one_mul, inv_one, mul_one] at this
      · exact hgen ⟨nW0 K, nW0_mem σ⟩ hm2 e f he hf
    obtain ⟨x, hx, hxt⟩ := hC t.2
    have hxt' : x = t := Subtype.ext hxt
    exact ⟨t, hxt' ▸ hx, by rw [hto]⟩
  ·
    have hle : Subgroup.closure {y | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹} ≤ ΛM := by
      rw [Subgroup.closure_le]
      rintro _ ⟨h, hh, a, ha, rfl⟩
      exact hconj h hh a ha
    have hcardΛ : Nat.card ΛM ≤ 2 ^ (2 * f) := by
      choose e f' he hf' hx using fun x : ΛM => x.2
      let F : ΛM → trialityFixedField K σ.toRingHom × trialityFixedField K σ.toRingHom :=
        fun x => (⟨e x, he x⟩, ⟨f' x, hf' x⟩)
      have hF : Function.Injective F := by
        intro x y hxy
        have h1 : e x = e y := congrArg (fun p => (p.1 : K)) hxy
        have h2 : f' x = f' y := congrArg (fun p => (p.2 : K)) hxy
        apply Subtype.ext; apply Subtype.ext
        rw [hx x, hx y, h1, h2]
      calc Nat.card ΛM ≤ Nat.card (trialityFixedField K σ.toRingHom ×
            trialityFixedField K σ.toRingHom) := Nat.card_le_card_of_injective F hF
        _ = 2 ^ (2 * f) := by rw [Nat.card_prod, hk, ← pow_add, two_mul]
    have hlen : gs.length = 5 := by rw [hgs, List.length_map]; rfl
    rw [hlen, hord]
    calc Nat.card (Subgroup.closure {y | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹}) ^ 5 ≤
        (2 ^ (2 * f)) ^ 5 := Nat.pow_le_pow_left ((Subgroup.card_le_of_le hle).trans hcardΛ) _
      _ < 2 ^ (12 * f) := by
        rw [← pow_mul]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)

include hf hK hσ in
theorem dispCriterion_trialityD4 : DispCriterion C₀ := by
  have := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  have hk := card_fixedField hf hK σ hσ
  have hZ : Subgroup.center C₀ = ⊥ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  obtain ⟨ℓ, y, t, hℓ, hℓ2, hord, hyt, hto, hyB⟩ := exists_B_inverting hf hK σ hσ
  refine dispCriterion_of_classes hZ (fun ξ => ConjC σ (ξ : ModGL TwistTag.D4.tag K) (ox₁ σ 1))
    (5 * f) (2 * f) (if Even f then 1 else 0) ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro E hE
    have hK' : Nat.card K = Nat.card (trialityFixedField K σ.toRingHom) ^ 3 := by rw [hK, hk]
    have h := card_le_of_elemAbelian σ hσ3 hK' E hE.1 hE.2
    rwa [hk, ← pow_mul, mul_comm] at h
  ·
    intro E hE hB
    have h := card_le_of_pure σ hσ3 E hE.1 (fun x hx => by rw [← sq]; exact hE.2 x hx) hB
    rwa [hk, ← pow_mul, mul_comm] at h
  ·
    intro F hF
    exact card_le_index hf K hK σ hσ F hF
  ·
    intro ξ hξ hξ1 hξB
    left
    obtain ⟨g, hg, hgy⟩ := hyB.trans σ hξB.symm
    set G : C₀ := ⟨g, hg⟩ with hG
    have hGy : G * y * G⁻¹ = ξ := Subtype.ext hgy
    have hξt : ξ * (G * t * G⁻¹) * ξ⁻¹ = (G * t * G⁻¹)⁻¹ := by
      rw [← hGy]
      calc G * y * G⁻¹ * (G * t * G⁻¹) * (G * y * G⁻¹)⁻¹ = G * (y * t * y⁻¹) * G⁻¹ := by group
        _ = (G * t * G⁻¹)⁻¹ := by rw [hyt]; group
    refine dispAt_of_inverts hZ (by rw [← map_mul, hξ, map_one]) (c := G * t * G⁻¹)
      (by rw [MulAut.conj_apply, hξt]) hℓ hℓ2 (by rw [orderOf_conj', hto]) ?_
    rw [hord, ← pow_mul]
    refine Nat.pow_lt_pow_right (by norm_num) ?_
    by_cases hev : Even f
    · simp only [hev, ↓reduceIte]
      obtain ⟨r, hr⟩ := hev
      omega
    · simp only [hev, ↓reduceIte]
      omega
  ·
    intro α hα hαo
    obtain ⟨hev, hD⟩ := dispAt_outer hf K hK σ hσ α hα hαo
    left
    simp only [hev, ↓reduceIte]
    exact hD
  ·
    intro E hE hEa hB
    exact Or.inr (lineGenAt_of_pure hf hK σ hσ E hE hEa hB)

end Classes

end CFSG.Quasithin.B42D4

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley B42D4

theorem asB42TrialityD4_holds :
    AsB42TrialityD4 :=
  B42Disp.asB42NoOffenderFor_of_dispCriterion fun X _ h => by
    obtain ⟨f, hf, hX⟩ := h
    obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hX
    exact ⟨graphFixedRootGroup TwistTag.D4 K σ.toRingHom, inferInstance, ⟨e⟩,
      dispCriterion_trialityD4 hf hK σ hσ⟩

end CFSG.Quasithin
