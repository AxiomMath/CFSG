module

public import CFSG.Quasithin.Background.SmithB42D4Weyl
public import CFSG.Quasithin.Background.SmithB42D4Rank
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin.B42D4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

section Field

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

omit [CharP K 2] in
theorem tr_mul_fixed {c : K} (hc : σ c = c) (x : K) : tr σ (c * x) = c * tr σ x := by
  simp only [tr, map_mul, hc]; ring

omit [CharP K 2] in
theorem bF_mul_right (a u : K) : bF σ a (a * u) = σ a * σ (σ a) * (σ u + σ (σ u)) := by
  simp only [bF, map_mul]; ring

theorem sigma_add_of_tr_eq_zero {w : K} (hw : tr σ w = 0) : σ w + σ (σ w) = w := by
  rw [tr] at hw; linear_combination (norm := ring2) hw

theorem sigma_eq_of_mul_self {r x : K} (hr : r * r = x) (hx : σ x = x) : σ r = r := by
  have h : (σ r + r) * (σ r + r) = 0 := by
    have h1 : σ r * σ r = σ x := by rw [← hr, map_mul]
    linear_combination (norm := ring2) h1 - hx + hr
  have h2 := mul_self_eq_zero.1 h
  linear_combination (norm := ring2) h2

omit [CharP K 2] in
theorem nK_ne_zero {a : K} (ha : a ≠ 0) : nK σ a ≠ 0 := by
  rw [nK]
  exact mul_ne_zero (mul_ne_zero ha ((map_ne_zero σ).2 ha)) ((map_ne_zero σ).2
    ((map_ne_zero σ).2 ha))

include hσ3 in
theorem fixed_of_bF_eq_zero {a c : K} (ha : a ≠ 0) (hB : bF σ a c = 0) : σ (c / a) = c / a := by
  have h3 := sigma_sigma_sigma σ hσ3
  set γ := c / a with hγdef
  have hc : c = a * γ := by rw [hγdef, mul_div_cancel₀ _ ha]
  have hs1 : σ a ≠ 0 := (map_ne_zero σ).2 ha
  have hs2 : σ (σ a) ≠ 0 := (map_ne_zero σ).2 hs1
  rw [hc, bF_mul_right] at hB
  have h2 : σ γ + σ (σ γ) = 0 := (mul_eq_zero.1 hB).resolve_left (mul_ne_zero hs1 hs2)
  have h4 : σ (σ γ) = σ γ := by linear_combination (norm := ring2) h2
  have h5 := congrArg σ h4
  rw [h3, h4] at h5
  exact h5.symm

theorem exists_mul_self_eq [Finite K] (x : K) : ∃ r : K, r * r = x := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' x
  exact ⟨r, hr.symm⟩

end Field

section Coset

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K

include hσ3 in
theorem conj_coset (a : K) (P Q : ModGL TwistTag.D4.tag K) :
    P * (ox₁ σ a * Q) * P⁻¹ = ox₁ σ a * ((ox₁ σ a * P * (ox₁ σ a)⁻¹) * Q * P⁻¹) := by
  have h := ox₁_mul_self σ hσ3 a
  have hi := ox₁_inv σ hσ3 a
  rw [hi]
  calc P * (ox₁ σ a * Q) * P⁻¹ = (ox₁ σ a * ox₁ σ a) * P * ox₁ σ a * Q * P⁻¹ := by
        rw [h]; group
    _ = _ := by group

include hσ3 in
theorem coset_step1 {a γ : K} (hγ : σ γ = γ) (d e f : K) :
    Xr d4C γ * (ox₁ σ a * qE σ 0 (a * γ) d e f) * (Xr d4C γ)⁻¹ =
      ox₁ σ a * qE σ 0 0 (d + γ * (σ a * σ (σ a))) (e + γ * nK σ a)
        (f + γ * e + γ * γ * nK σ a) := by
  have hN : σ (nK σ a) = nK σ a := sigma_nK σ hσ3 a
  rw [conj_coset σ hσ3, conj_ox₁_C σ hσ3 hγ, Xr_inv, qE_C σ, qE_mul σ hσ3, qE_mul σ hσ3]
  refine congrArg (ox₁ σ a * ·) ?_
  have ht : tr σ (γ * (σ a * σ (σ a)) * (a * γ)) = γ * γ * nK σ a := by
    have e1 : γ * (σ a * σ (σ a)) * (a * γ) = γ * γ * nK σ a := by rw [nK]; ring
    rw [e1, tr_of_fixed σ (by rw [map_mul, map_mul, hγ, hN])]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_
  · ring2
  · ring2
  · ring2
  · ring2
  · rw [ht]; simp only [mul_zero, add_zero]
    rw [tr]; simp only [map_zero, add_zero]; ring2

include hσ3 in
theorem ox₃_inv' (β : K) : (ox₃ σ β)⁻¹ = ox₃ σ β := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← ox₃_add σ hσ3, CharTwo.add_self_eq_zero, ox₃_zero']

include hσ3 in
theorem coset_step2 {a β d : K} (hB : bF σ a β = d) (e f : K) :
    ox₃ σ β * (ox₁ σ a * qE σ 0 0 d e f) * (ox₃ σ β)⁻¹ =
      ox₁ σ a * qE σ 0 0 0 (e + e5F σ a β) (f + e6F σ a β) := by
  rw [conj_coset σ hσ3, conj_ox₁_ox₃ σ hσ3, ox₃_inv' σ hσ3, qE_ox₃ σ, qE_mul σ hσ3,
    qE_mul σ hσ3, hB]
  refine congrArg (ox₁ σ a * ·) (qE_congr σ ?_ ?_ ?_ ?_ ?_)
  · ring2
  · ring2
  · ring2
  · ring2
  · rw [CharTwo.add_self_eq_zero, zero_mul]; simp only [tr, mul_zero, map_zero, add_zero]
    ring2

include hσ3 in
theorem coset_step3 {a δ e : K} (hT : tr σ (a * δ) = e) (f : K) :
    ox₄ σ δ * (ox₁ σ a * qE σ 0 0 0 e f) * (ox₄ σ δ)⁻¹ = ox₁ σ a * qE σ 0 0 0 0 f := by
  rw [conj_coset σ hσ3, conj_ox₁_ox₄ σ hσ3, qE_ox₄ σ, qE_inv σ hσ3, qE_mul σ hσ3, qE_mul σ hσ3, hT]
  refine congrArg (ox₁ σ a * ·) (qE_congr σ ?_ ?_ ?_ ?_ ?_)
  · ring2
  · ring2
  · ring2
  · ring2
  · simp only [tr, mul_zero, map_zero, add_zero, zero_add]

include hσ3 in
theorem coset_step4 {a ρ δ f : K} (hρ : σ ρ = ρ) (hT : tr σ (a * δ) = ρ * nK σ a)
    (hf : ρ * ρ * nK σ a = f) :
    qE σ 0 (a * ρ) δ 0 0 * (ox₁ σ a * qE σ 0 0 0 0 f) * (qE σ 0 (a * ρ) δ 0 0)⁻¹ = ox₁ σ a := by
  have hN : σ (nK σ a) = nK σ a := sigma_nK σ hσ3 a
  have hB : bF σ a (a * ρ) = 0 := by
    rw [bF_mul_right]; simp only [hρ, CharTwo.add_self_eq_zero, mul_zero]
  have h5 : e5F σ a (a * ρ) = ρ * nK σ a := by
    have e1 : a * σ a * σ (σ (a * ρ)) = ρ * nK σ a := by
      simp only [map_mul, hρ, nK]; ring
    rw [e5F, e1, tr_of_fixed σ (by rw [map_mul, hρ, hN])]
  have h6 : e6F σ a (a * ρ) = ρ * ρ * nK σ a := by
    have e1 : a * σ (a * ρ) * σ (σ (a * ρ)) = ρ * ρ * nK σ a := by
      simp only [map_mul, hρ, nK]; ring
    rw [e6F, e1, tr_of_fixed σ (by rw [map_mul, map_mul, hρ, hN])]
  rw [conj_coset σ hσ3, conj_ox₁_qE σ hσ3 (map_zero σ), qE_inv σ hσ3, qE_mul σ hσ3, qE_mul σ hσ3,
    hB, h5, h6, hT, hf]
  have h1 : qE σ 0 0 0 0 0 = 1 := by rw [← qE_H, pinnedX_zero]
  refine (congrArg (ox₁ σ a * ·) ?_).trans (mul_one _)
  rw [← h1]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_
  · ring2
  · ring2
  · ring2
  · ring2
  · simp only [tr, mul_zero, map_zero, add_zero, zero_mul, map_mul]
    ring2

include hσ3 in
theorem qE_eq_one {b c d e f : K} (hb : σ b = b) (he : σ e = e) (hf : σ f = f)
    (h : qE σ b c d e f = 1) : b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  have h1 : qE σ 0 0 0 0 0 = 1 := by rw [← qE_H, pinnedX_zero]
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := qE_inj σ hσ3 (b := ⟨b, hb⟩) (b' := 0) (c := c) (c' := 0)
    (d := d) (d' := 0) (e := ⟨e, he⟩) (e' := 0) (f := ⟨f, hf⟩) (f' := 0) (h.trans h1.symm)
  exact ⟨congrArg Subtype.val h₁, h₂, h₃, congrArg Subtype.val h₄, congrArg Subtype.val h₅⟩

include hσ3 in
theorem coset_conj {a : K} (ha : a ≠ 0) {b c d e f : K} (hb : σ b = b) (he : σ e = e)
    (hf : σ f = f) (h : (ox₁ σ a * qE σ b c d e f) * (ox₁ σ a * qE σ b c d e f) = 1) :
    ∃ g ∈ Q0 σ, g * (ox₁ σ a * qE σ b c d e f) * g⁻¹ = ox₁ σ a := by
  have h3 := sigma_sigma_sigma σ hσ3
  have hN : σ (nK σ a) = nK σ a := sigma_nK σ hσ3 a
  have hN0 : nK σ a ≠ 0 := nK_ne_zero σ ha
  have hs1 : σ a ≠ 0 := (map_ne_zero σ).2 ha
  have hs2 : σ (σ a) ≠ 0 := (map_ne_zero σ).2 hs1
  have hD : σ a * σ (σ a) ≠ 0 := mul_ne_zero hs1 hs2
  have hsq : (ox₁ σ a * qE σ b c d e f) * (ox₁ σ a * qE σ b c d e f) =
      (ox₁ σ a * qE σ b c d e f * (ox₁ σ a)⁻¹) * qE σ b c d e f := by
    rw [ox₁_inv σ hσ3]; group
  rw [hsq, conj_ox₁_qE σ hσ3 hb, qE_mul σ hσ3] at h
  obtain ⟨-, hc0, hd0, he0, -⟩ := qE_eq_one σ hσ3 (by rw [map_add, hb])
    (by simp only [map_add, map_mul, hb, he, hN, sigma_e5F σ hσ3, sigma_tr σ hσ3])
    (by simp only [map_add, map_mul, hb, he, hf, hN, sigma_e5F σ hσ3, sigma_e6F σ hσ3,
      sigma_tr σ hσ3]) h
  have hb0 : b = 0 := by
    have : a * b = 0 := by linear_combination (norm := ring2) hc0
    exact (mul_eq_zero.1 this).resolve_left ha
  subst hb0
  have hBc : bF σ a c = 0 := by linear_combination (norm := ring2) hd0
  have h5c : e5F σ a c + tr σ (a * d) = 0 := by linear_combination (norm := ring2) he0
  set γ := c / a with hγdef
  have hγ : σ γ = γ := fixed_of_bF_eq_zero σ hσ3 ha hBc
  have hc : c = a * γ := by rw [hγdef, mul_div_cancel₀ _ ha]
  have he5 : e5F σ a c = γ * nK σ a := by
    have e1 : a * σ a * σ (σ c) = γ * nK σ a := by simp only [hc, map_mul, hγ, nK]; ring
    rw [e5F, e1, tr_of_fixed σ (by rw [map_mul, hγ, hN])]
  have s1 := coset_step1 σ hσ3 (a := a) hγ d e f
  rw [← hc] at s1
  set d₁ := d + γ * (σ a * σ (σ a)) with hd₁
  set e₁ := e + γ * nK σ a with he₁
  set f₁ := f + γ * e + γ * γ * nK σ a with hf₁
  have htd : tr σ (a * d₁) = 0 := by
    have e1 : tr σ (a * (γ * (σ a * σ (σ a)))) = γ * nK σ a := by
      have e2 : a * (γ * (σ a * σ (σ a))) = γ * nK σ a := by rw [nK]; ring
      rw [e2, tr_of_fixed σ (by rw [map_mul, hγ, hN])]
    have e3 : tr σ (a * d₁) = tr σ (a * d) + tr σ (a * (γ * (σ a * σ (σ a)))) := by
      simp only [hd₁, tr, mul_add, map_add]; ring
    rw [e3, e1]
    linear_combination (norm := ring2) h5c - he5
  set u := d₁ / (σ a * σ (σ a)) with hu
  have hu' : u = (nK σ a)⁻¹ * (a * d₁) := by
    rw [hu, nK]; field_simp
  have htu : tr σ u = 0 := by
    have hNi : σ (nK σ a)⁻¹ = (nK σ a)⁻¹ := by rw [map_inv₀, hN]
    rw [hu', tr_mul_fixed σ hNi, htd, mul_zero]
  have hB2 : bF σ a (a * u) = d₁ := by
    rw [bF_mul_right, sigma_add_of_tr_eq_zero σ htu, hu, mul_div_cancel₀ _ hD]
  have s2 := coset_step2 σ hσ3 (a := a) hB2 e₁ f₁
  set e₂ := e₁ + e5F σ a (a * u) with he₂
  set f₂ := f₁ + e6F σ a (a * u) with hf₂
  have he₂k : σ e₂ = e₂ := by
    simp only [he₂, he₁, map_add, map_mul, he, hγ, hN, sigma_e5F σ hσ3]
  have hf₂k : σ f₂ = f₂ := by
    simp only [hf₂, hf₁, map_add, map_mul, he, hf, hγ, hN, sigma_e6F σ hσ3]
  have hT3 : tr σ (a * (e₂ / a)) = e₂ := by
    rw [mul_div_cancel₀ _ ha, tr_of_fixed σ he₂k]
  have s3 := coset_step3 σ hσ3 hT3 f₂
  obtain ⟨ρ, hρ⟩ := exists_mul_self_eq (f₂ / nK σ a)
  have hρk : σ ρ = ρ := sigma_eq_of_mul_self σ hρ (by rw [map_div₀, hf₂k, hN])
  have hT4 : tr σ (a * (ρ * nK σ a / a)) = ρ * nK σ a := by
    rw [mul_div_cancel₀ _ ha, tr_of_fixed σ (by rw [map_mul, hρk, hN])]
  have hf4 : ρ * ρ * nK σ a = f₂ := by rw [hρ, div_mul_cancel₀ _ hN0]
  have s4 := coset_step4 σ hσ3 hρk hT4 hf4
  have key : ∀ P₁ P₂ P₃ P₄ x : ModGL TwistTag.D4.tag K,
      (P₄ * P₃ * P₂ * P₁) * x * (P₄ * P₃ * P₂ * P₁)⁻¹ =
        P₄ * (P₃ * (P₂ * (P₁ * x * P₁⁻¹) * P₂⁻¹) * P₃⁻¹) * P₄⁻¹ := fun _ _ _ _ _ => by group
  refine ⟨qE σ 0 (a * ρ) (ρ * nK σ a / a) 0 0 * ox₄ σ (e₂ / a) * ox₃ σ (a * u) * Xr d4C γ,
    ?_, ?_⟩
  swap
  · rw [key, s1, s2, s3, s4]
  have m0 : ∀ (b' : trialityFixedField K τ₀) (c' d' : K) (e' f' : trialityFixedField K τ₀),
      qE σ b' c' d' e' f' ∈ Q0 σ := qE_mem_Q0 σ hσ3
  refine mul_mem (mul_mem (mul_mem (m0 0 _ _ 0 0) ?_) ?_) ?_
  · rw [qE_ox₄ σ]; exact m0 0 0 _ 0 0
  · rw [qE_ox₃ σ]; exact m0 0 _ 0 0 0
  · rw [qE_C σ]; exact m0 ⟨γ, hγ⟩ 0 0 0 0

end Coset

section Defs

variable {K : Type} [Field K] (σ : K ≃+* K)

local notation "Xr" => pinnedX TwistTag.D4.tag K

@[expose] def ConjC (x y : ModGL TwistTag.D4.tag K) : Prop :=
  ∃ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g * x * g⁻¹ = y

@[expose] def IsPure (g : ModGL TwistTag.D4.tag K) : Prop :=
  (∃ s β f : K, σ β = β ∧ σ f = f ∧ g = ox₁ σ s * (Xr d4C β * Xr d4H f) * (ox₁ σ s)⁻¹) ∨
    ∃ e f : K, σ e = e ∧ σ f = f ∧ g = Xr d4P e * Xr d4H f

theorem ConjC.symm {x y : ModGL TwistTag.D4.tag K} (h : ConjC σ x y) : ConjC σ y x := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, inv_mem hg, by group⟩

theorem ConjC.trans {x y z : ModGL TwistTag.D4.tag K} (h : ConjC σ x y) (h' : ConjC σ y z) :
    ConjC σ x z := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', rfl⟩ := h'
  exact ⟨g' * g, mul_mem hg' hg, by group⟩

theorem ConjC.of_conj {x y : ModGL TwistTag.D4.tag K} {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (h : g * x * g⁻¹ = y) :
    ConjC σ x y :=
  ⟨g, hg, h⟩

end Defs

section Classes

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

include hσ3 in
theorem ox₁_mem_C0 (s : K) : ox₁ σ s ∈ C₀ :=
  graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ ((ox_data σ hσ3).2.1.1 s)

include hσ3 in
theorem qE_mem_C0 {b c d e f : K} (hb : σ b = b) (he : σ e = e) (hf : σ f = f) :
    qE σ b c d e f ∈ C₀ :=
  graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (Q0_le_U σ hσ3 (qE_mem_Q0 σ hσ3 ⟨b, hb⟩ c d ⟨e, he⟩ ⟨f, hf⟩))

include hσ3 in
theorem Xr_C_mem_C0 {b : K} (hb : σ b = b) : Xr d4C b ∈ C₀ := by
  rw [qE_C σ]; exact qE_mem_C0 σ hσ3 hb (map_zero σ) (map_zero σ)

include hσ3 in
theorem Xr_P_mem_C0 {e : K} (he : σ e = e) : Xr d4P e ∈ C₀ := by
  rw [qE_P σ]; exact qE_mem_C0 σ hσ3 (map_zero σ) he (map_zero σ)

include hσ3 in
theorem Xr_H_mem_C0 {f : K} (hf : σ f = f) : Xr d4H f ∈ C₀ := by
  rw [qE_H σ]; exact qE_mem_C0 σ hσ3 (map_zero σ) (map_zero σ) hf

include hσ3 in
theorem ox₁_conj_one {a : K} (ha : a ≠ 0) : ConjC σ (ox₁ σ a) (ox₁ σ 1) := by
  obtain ⟨r, hr⟩ := exists_mul_self_eq a⁻¹
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hr
    exact inv_ne_zero ha hr.symm
  refine ⟨trialityTorusHom σ (Units.mk0 r hr0, 1), torus_mem σ hσ3 _, ?_⟩
  rw [torA_ox₁ σ hσ3, Units.val_mk0, sq, hr, inv_mul_cancel₀ ha]

omit [Finite K] [CharP K 2] in
include hσ3 in
theorem H_conj_one {f : K} (hf : σ f = f) (hf0 : f ≠ 0) : ConjC σ (Xr d4H f) (Xr d4H 1) := by
  set f' : trialityFixedField K τ₀ := ⟨f, hf⟩
  have hf' : f' ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  refine ⟨trialityTorusHom σ (1, (Units.mk0 f' hf')⁻¹), torus_mem σ hσ3 _, ?_⟩
  have h := torus_b_ox₆ σ hσ3 (Units.mk0 f' hf')⁻¹ f'
  rw [coe_ox₆_eq, coe_ox₆_eq] at h
  rw [h]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [inv_mul_cancel₀ hf']
  rfl

omit [Finite K] in
theorem nB_qE (c d e f : K) :
    nB K * qE σ 0 c d e f * (nB K)⁻¹ = ox₁ σ c * qE σ 0 0 d f e := by
  have c5 : ∀ g x₁ x₂ x₃ x₄ : ModGL TwistTag.D4.tag K,
      g * (x₁ * x₂ * x₃ * x₄) * g⁻¹ = (g * x₁ * g⁻¹) * (g * x₂ * g⁻¹) * (g * x₃ * g⁻¹) *
        (g * x₄ * g⁻¹) := fun g x₁ x₂ x₃ x₄ => by group
  have hPH : Commute (Xr d4H e) (Xr d4P f) := commute_of_d4CommB (by decide +kernel) _ _
  simp only [qE, pinnedX_zero, ox₃_zero', one_mul, mul_one]
  rw [c5, nB_ox₃ σ, nB_ox₄ σ, nB_P, nB_H, mul_assoc (ox₁ σ c * ox₄ σ d), hPH.eq]
  group

omit [Finite K] in
theorem nA_qE (b d f : K) : nA K * qE σ b 0 d 0 f * (nA K)⁻¹ = qE σ 0 d 0 b f := by
  have c3 : ∀ g x₁ x₂ x₃ : ModGL TwistTag.D4.tag K,
      g * (x₁ * x₂ * x₃) * g⁻¹ = (g * x₁ * g⁻¹) * (g * x₂ * g⁻¹) * (g * x₃ * g⁻¹) :=
    fun g x₁ x₂ x₃ => by group
  simp only [qE, pinnedX_zero, ox₃_zero', ox₄_zero', one_mul, mul_one]
  rw [c3, nA_C, nA_ox₄ σ, nA_H, (commute_P_ox₃ b d σ).eq]

include hσ3 in
theorem coset_conj_one {a : K} (ha : a ≠ 0) {b c d e f : K} (hb : σ b = b) (he : σ e = e)
    (hf : σ f = f) (h : (ox₁ σ a * qE σ b c d e f) * (ox₁ σ a * qE σ b c d e f) = 1) :
    ConjC σ (ox₁ σ a * qE σ b c d e f) (ox₁ σ 1) := by
  obtain ⟨g, hg, hgx⟩ := coset_conj σ hσ3 ha hb he hf h
  exact (ConjC.of_conj σ (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (Q0_le_U σ hσ3 hg)) hgx).trans σ (ox₁_conj_one σ hσ3 ha)

include hσ3 in
theorem Q0_conj_of_c {c d e f : K} (hc : c ≠ 0) (he : σ e = e) (hf : σ f = f)
    (h : qE σ 0 c d e f * qE σ 0 c d e f = 1) : ConjC σ (qE σ 0 c d e f) (ox₁ σ 1) := by
  have h' : (ox₁ σ c * qE σ 0 0 d f e) * (ox₁ σ c * qE σ 0 0 d f e) = 1 := by
    rw [← nB_qE σ]
    calc nB K * qE σ 0 c d e f * (nB K)⁻¹ * (nB K * qE σ 0 c d e f * (nB K)⁻¹) =
        nB K * (qE σ 0 c d e f * qE σ 0 c d e f) * (nB K)⁻¹ := by group
      _ = 1 := by rw [h]; group
  exact (ConjC.of_conj σ (nB_mem σ) (nB_qE σ c d e f)).trans σ
    (coset_conj_one σ hσ3 hc (map_zero σ) hf he h')

include hσ3 in
theorem Q0_classification {b c d e f : K} (hb : σ b = b) (he : σ e = e) (hf : σ f = f)
    (h : qE σ b c d e f * qE σ b c d e f = 1) :
    IsPure σ (qE σ b c d e f) ∨ ConjC σ (qE σ b c d e f) (ox₁ σ 1) := by
  have hN : ∀ s, σ (nK σ s) = nK σ s := sigma_nK σ hσ3
  have hconj : ∀ (s : K) (x : ModGL TwistTag.D4.tag K), x * x = 1 →
      (ox₁ σ s * x * (ox₁ σ s)⁻¹) * (ox₁ σ s * x * (ox₁ σ s)⁻¹) = 1 := fun s x hx => by
    calc ox₁ σ s * x * (ox₁ σ s)⁻¹ * (ox₁ σ s * x * (ox₁ σ s)⁻¹) =
        ox₁ σ s * (x * x) * (ox₁ σ s)⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hconjA : ∀ x : ModGL TwistTag.D4.tag K, x * x = 1 →
      (nA K * x * (nA K)⁻¹) * (nA K * x * (nA K)⁻¹) = 1 := fun x hx => by
    calc nA K * x * (nA K)⁻¹ * (nA K * x * (nA K)⁻¹) = nA K * (x * x) * (nA K)⁻¹ := by group
      _ = 1 := by rw [hx]; group
  by_cases hb0 : b = 0
  · subst hb0
    by_cases hc0 : c = 0
    · subst hc0
      by_cases hd0 : d = 0
      · subst hd0
        left; right
        refine ⟨e, f, he, hf, ?_⟩
        simp only [qE, pinnedX_zero, ox₃_zero', ox₄_zero', one_mul]
      · right
        set s := e / d
        have hs : tr σ (s * d) = e := by rw [div_mul_cancel₀ _ hd0, tr_of_fixed σ he]
        have h1 := conj_ox₁_qE σ hσ3 (map_zero σ) s 0 d e f
        have hz : e + 0 * nK σ s + e5F σ s 0 + tr σ (s * d) = 0 := by
          rw [hs]; simp only [e5F, tr, map_zero, mul_zero, zero_mul, add_zero]; ring2
        simp only [mul_zero, add_zero, zero_mul] at h1
        have hb5 : bF σ s 0 = 0 := by simp [bF]
        rw [hb5, add_zero] at h1
        have he5 : e + e5F σ s 0 + tr σ (s * d) = 0 := by
          simpa only [zero_mul, add_zero] using hz
        rw [he5] at h1
        set f' := f + e6F σ s 0
        have hf' : σ f' = f' := by simp only [f', map_add, hf, sigma_e6F σ hσ3]
        have hy := hconj s _ h
        rw [h1] at hy
        have h2 := nA_qE σ 0 d f'
        have hy' := hconjA _ hy
        rw [h2] at hy'
        exact (ConjC.of_conj σ (ox₁_mem_C0 σ hσ3 s) h1).trans σ
          ((ConjC.of_conj σ (nA_mem σ) h2).trans σ
            (Q0_conj_of_c σ hσ3 hd0 (map_zero σ) hf' hy'))
    · right
      exact Q0_conj_of_c σ hσ3 hc0 he hf h
  ·
    set s := c / b with hsdef
    have hsb : c + s * b = 0 := by rw [hsdef, div_mul_cancel₀ _ hb0]; ring2
    have h1 := conj_ox₁_qE σ hσ3 hb s c d e f
    rw [hsb] at h1
    set d' := d + b * (σ s * σ (σ s)) + bF σ s c
    set e' := e + b * nK σ s + e5F σ s c + tr σ (s * d)
    set f' := f + b * b * nK σ s + e6F σ s c + b * e5F σ s c
    have hf' : σ f' = f' := by
      simp only [f', map_add, map_mul, hb, hf, hN, sigma_e5F σ hσ3, sigma_e6F σ hσ3]
    have hy := hconj s _ h
    rw [h1, qE_mul_self_eq_one_iff σ hσ3, mul_zero] at hy
    have he' : e' = 0 := by
      have : e' * b = 0 := by
        rw [tr] at hy; simpa only [map_zero, add_zero, zero_add] using hy
      exact (mul_eq_zero.1 this).resolve_right hb0
    rw [he'] at h1
    by_cases hd' : d' = 0
    · left; left
      refine ⟨s, b, f', hb, hf', ?_⟩
      rw [hd'] at h1
      have e1 : qE σ b 0 0 0 f' = Xr d4C b * Xr d4H f' := by
        simp only [qE, pinnedX_zero, ox₃_zero', ox₄_zero', mul_one]
      rw [e1] at h1
      rw [← h1, ox₁_inv σ hσ3]
      calc qE σ b c d e f = (ox₁ σ s * ox₁ σ s) * qE σ b c d e f * (ox₁ σ s * ox₁ σ s) := by
            rw [ox₁_mul_self σ hσ3]; group
        _ = _ := by group
    · right
      have hy2 := hconj s _ h
      rw [h1] at hy2
      have h2 := nA_qE σ b d' f'
      have hy' := hconjA _ hy2
      rw [h2] at hy'
      exact (ConjC.of_conj σ (ox₁_mem_C0 σ hσ3 s) h1).trans σ
        ((ConjC.of_conj σ (nA_mem σ) h2).trans σ (Q0_conj_of_c σ hσ3 hd' hb hf' hy'))

include hσ3 in
theorem U_classification {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) (h : g * g = 1) :
    IsPure σ g ∨ ConjC σ g (ox₁ σ 1) := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ := (mem_U_iff σ hσ3).1 hg
  by_cases ha : a = 0
  · subst ha
    rw [ox₁_zero σ hσ3, one_mul] at h ⊢
    exact Q0_classification σ hσ3 b.2 e.2 f.2 h
  · exact Or.inr (coset_conj_one σ hσ3 ha b.2 e.2 f.2 h)

omit [Finite K] in
theorem C_conj_H {β : K} : ConjC σ (Xr d4C β) (Xr d4H β) :=
  (ConjC.of_conj σ (nA_mem σ) (nA_C β)).trans σ (ConjC.of_conj σ (nB_mem σ) (nB_P β))

include hσ3 in
theorem CH_conj_C {β f : K} (hβ : σ β = β) (hf : σ f = f) (hβ0 : β ≠ 0) :
    ConjC σ (Xr d4C β * Xr d4H f) (Xr d4C β) := by
  set γ := f / β
  have hγ : σ γ = γ := by simp only [γ, map_div₀, hβ, hf]
  refine ⟨Xr d4P γ, Xr_P_mem_C0 σ hσ3 hγ, ?_⟩
  have hPH : Commute (Xr d4P γ) (Xr d4H f) := commute_of_d4CommB (by decide +kernel) _ _
  have hCH : Commute (Xr d4C β) (Xr d4H (γ * β)) := commute_of_d4CommB (by decide +kernel) _ _
  have hPH' : Commute (Xr d4P γ) (Xr d4H (γ * β)) := commute_of_d4CommB (by decide +kernel) _ _
  have e1 : Xr d4P γ * Xr d4C β * (Xr d4P γ)⁻¹ = Xr d4C β * Xr d4H (γ * β) := by
    rw [rel_P_C, mul_assoc, ← hPH'.inv_left.eq, ← mul_assoc, mul_inv_cancel_right]
  calc Xr d4P γ * (Xr d4C β * Xr d4H f) * (Xr d4P γ)⁻¹ =
      (Xr d4P γ * Xr d4C β * (Xr d4P γ)⁻¹) * Xr d4H f := by
        rw [conj_mul2, hPH.eq, mul_inv_cancel_right]
    _ = Xr d4C β * (Xr d4H (γ * β) * Xr d4H f) := by rw [e1, mul_assoc]
    _ = Xr d4C β := by
        rw [← pinnedX_add, div_mul_cancel₀ _ hβ0, CharTwo.add_self_eq_zero, pinnedX_zero, mul_one]

include hσ3 in
theorem PH_conj_P {e f : K} (he : σ e = e) (hf : σ f = f) (he0 : e ≠ 0) :
    ConjC σ (Xr d4P e * Xr d4H f) (Xr d4P e) := by
  set γ := f / e
  have hγ : σ γ = γ := by simp only [γ, map_div₀, he, hf]
  refine ⟨Xr d4C γ, Xr_C_mem_C0 σ hσ3 hγ, ?_⟩
  have hCH : Commute (Xr d4C γ) (Xr d4H f) := commute_of_d4CommB (by decide +kernel) _ _
  have e1 : Xr d4C γ * Xr d4P e * (Xr d4C γ)⁻¹ = Xr d4P e * Xr d4H (e * γ) := by
    have h := rel_P_C (K := K) e γ
    rw [Xr_inv]
    calc Xr d4C γ * Xr d4P e * Xr d4C γ = Xr d4C γ * (Xr d4P e * Xr d4C γ) := by group
      _ = Xr d4C γ * (Xr d4C γ * Xr d4P e * Xr d4H (e * γ)) := by rw [h]
      _ = (Xr d4C γ * Xr d4C γ) * Xr d4P e * Xr d4H (e * γ) := by group
      _ = _ := by rw [Xr_mul_self, one_mul]
  calc Xr d4C γ * (Xr d4P e * Xr d4H f) * (Xr d4C γ)⁻¹ =
      (Xr d4C γ * Xr d4P e * (Xr d4C γ)⁻¹) * Xr d4H f := by
        rw [conj_mul2, hCH.eq, mul_inv_cancel_right]
    _ = Xr d4P e * (Xr d4H (e * γ) * Xr d4H f) := by rw [e1, mul_assoc]
    _ = Xr d4P e := by
        rw [← pinnedX_add, mul_div_cancel₀ _ he0, CharTwo.add_self_eq_zero, pinnedX_zero, mul_one]

include hσ3 in
theorem pure_conj {g : ModGL TwistTag.D4.tag K} (hp : IsPure σ g) (hg : g ≠ 1) :
    ConjC σ g (Xr d4H 1) := by
  rcases hp with ⟨s, β, f, hβ, hf, rfl⟩ | ⟨e, f, he, hf, rfl⟩
  · have h1 : ConjC σ (ox₁ σ s * (Xr d4C β * Xr d4H f) * (ox₁ σ s)⁻¹)
        (Xr d4C β * Xr d4H f) := (ConjC.of_conj σ (ox₁_mem_C0 σ hσ3 s) rfl).symm σ
    by_cases hβ0 : β = 0
    · subst hβ0
      have hf0 : f ≠ 0 := by
        rintro rfl
        apply hg
        rw [pinnedX_zero, pinnedX_zero, one_mul, mul_one, mul_inv_cancel]
      refine h1.trans σ ?_
      rw [pinnedX_zero, one_mul]
      exact H_conj_one σ hσ3 hf hf0
    · refine (h1.trans σ (CH_conj_C σ hσ3 hβ hf hβ0)).trans σ ((C_conj_H σ).trans σ ?_)
      exact H_conj_one σ hσ3 hβ hβ0
  · by_cases he0 : e = 0
    · subst he0
      have hf0 : f ≠ 0 := by
        rintro rfl
        apply hg
        rw [pinnedX_zero, pinnedX_zero, one_mul]
      rw [pinnedX_zero, one_mul]
      exact H_conj_one σ hσ3 hf hf0
    · exact (PH_conj_P σ hσ3 he hf he0).trans σ ((ConjC.of_conj σ (nB_mem σ) (nB_P e)).trans σ
        (H_conj_one σ hσ3 he he0))

end Classes

end CFSG.Quasithin.B42D4
