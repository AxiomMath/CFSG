module

public import CFSG.Quasithin.Background.SmithB42D4Inv

public section

namespace CFSG.Quasithin.B42D4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

section Field

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

omit [CharP K 2] in
include hσ3 in
theorem nK_add (s s' : K) :
    nK σ (s + s') = nK σ s + nK σ s' + tr σ (s' * (σ s * σ (σ s))) +
      tr σ (s * (σ s' * σ (σ s'))) := by
  simp only [nK, tr, map_add, map_mul, sigma_sigma_sigma σ hσ3]; ring2

omit [CharP K 2] in
theorem nK_eq_zero {s : K} (h : nK σ s = 0) : s = 0 := by
  by_contra hs
  exact nK_ne_zero σ hs h

end Field

section Sylow

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

theorem exists_conj_le_U (E : Subgroup C₀) (hE : IsPGroup 2 E) :
    ∃ g : C₀, ∀ x ∈ E, ((g⁻¹ * x * g : C₀) : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨P, hP⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq C₀ P Q
  rw [Sylow.coe_subgroup_smul, hP] at hQ
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hQ hx
  have hxy : g⁻¹ * x * g = y := by
    rw [← hyx]
    change g⁻¹ * (g * y * g⁻¹) * g = y
    group
  rw [hxy]
  exact hy

end Sylow

section Line

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

include hσ3 in
theorem conj_line (s : K) {β : K} (hβ : σ β = β) (f : K) :
    ox₁ σ s * (Xr d4C β * Xr d4H f) * (ox₁ σ s)⁻¹ =
      qE σ β (s * β) (β * (σ s * σ (σ s))) (β * nK σ s) (f + β * β * nK σ s) := by
  have e1 : Xr d4C β * Xr d4H f = qE σ β 0 0 0 f := by
    simp only [qE, pinnedX_zero, ox₃_zero', ox₄_zero', mul_one]
  rw [e1, conj_ox₁_qE σ hσ3 hβ]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_
  · rfl
  · ring
  · simp [bF]
  · simp [e5F, tr]
  · simp [e6F, e5F, tr]

include hσ3 in
theorem line_comm_eq {s s' β β' f f' : K} (hβ : σ β = β) (hβ' : σ β' = β') (hβ0 : β ≠ 0)
    (hβ0' : β' ≠ 0)
    (h : ox₁ σ s * (Xr d4C β * Xr d4H f) * (ox₁ σ s)⁻¹ *
        (ox₁ σ s' * (Xr d4C β' * Xr d4H f') * (ox₁ σ s')⁻¹) =
      ox₁ σ s' * (Xr d4C β' * Xr d4H f') * (ox₁ σ s')⁻¹ *
        (ox₁ σ s * (Xr d4C β * Xr d4H f) * (ox₁ σ s)⁻¹)) : s = s' := by
  rw [conj_line σ hσ3 s hβ, conj_line σ hσ3 s' hβ', qE_commute_iff σ hσ3] at h
  have key : β * β' * nK σ (s + s') = 0 := by
    rw [nK_add σ hσ3]
    have e1 : tr σ (β * (σ s * σ (σ s)) * (s' * β')) = β * β' * tr σ (s' * (σ s * σ (σ s))) := by
      rw [show β * (σ s * σ (σ s)) * (s' * β') = (β * β') * (s' * (σ s * σ (σ s))) by ring,
        tr_mul_fixed σ (by rw [map_mul, hβ, hβ'])]
    have e2 : tr σ (β' * (σ s' * σ (σ s')) * (s * β)) =
        β * β' * tr σ (s * (σ s' * σ (σ s'))) := by
      rw [show β' * (σ s' * σ (σ s')) * (s * β) = (β * β') * (s * (σ s' * σ (σ s'))) by ring,
        tr_mul_fixed σ (by rw [map_mul, hβ, hβ'])]
    rw [e1, e2] at h
    linear_combination (norm := ring2) h
  have h0 := (mul_eq_zero.1 key).resolve_left (mul_ne_zero hβ0 hβ0')
  have := nK_eq_zero σ h0
  linear_combination (norm := ring2) this

include hσ3 in
theorem line_not_comm {s β f e f' : K} (hβ0 : β ≠ 0) (hβ : σ β = β) (he0 : e ≠ 0)
    (h : ox₁ σ s * (Xr d4C β * Xr d4H f) * (ox₁ σ s)⁻¹ * (Xr d4P e * Xr d4H f') =
      Xr d4P e * Xr d4H f' * (ox₁ σ s * (Xr d4C β * Xr d4H f) * (ox₁ σ s)⁻¹)) : False := by
  have e1 : Xr d4P e * Xr d4H f' = qE σ 0 0 0 e f' := by
    simp only [qE, pinnedX_zero, ox₃_zero', ox₄_zero', one_mul]
  rw [conj_line σ hσ3 s hβ, e1, qE_commute_iff σ hσ3] at h
  simp only [mul_zero, tr, map_zero, add_zero, zero_mul, zero_add] at h
  exact mul_ne_zero he0 hβ0 h.symm

omit
  [Finite K] in
theorem line_eq (s β f : K) :
    ox₁ σ s * (Xr d4C β * Xr d4H f) * (ox₁ σ s)⁻¹ =
      (ox₁ σ s * nA K) * (Xr d4P β * Xr d4H f) * (ox₁ σ s * nA K)⁻¹ := by
  have : nA K * (Xr d4P β * Xr d4H f) * (nA K)⁻¹ = Xr d4C β * Xr d4H f := by
    rw [conj_mul2, nA_P, nA_H]
  rw [← this]; group

include hσ3 in
theorem pure_line {E : Set (ModGL TwistTag.D4.tag K)} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hpure : ∀ x ∈ E, IsPure σ x) :
    ∃ g ∈ C₀, ∀ x ∈ E, ∃ e f : K, σ e = e ∧ σ f = f ∧
      x = g * (Xr d4P e * Xr d4H f) * g⁻¹ := by
  by_cases hex : ∃ x₀ ∈ E, ∃ s₀ β₀ f₀ : K, σ β₀ = β₀ ∧ σ f₀ = f₀ ∧ β₀ ≠ 0 ∧
      x₀ = ox₁ σ s₀ * (Xr d4C β₀ * Xr d4H f₀) * (ox₁ σ s₀)⁻¹
  · obtain ⟨x₀, hx₀, s₀, β₀, f₀, hβ₀, hf₀, hβ₀0, rfl⟩ := hex
    refine ⟨ox₁ σ s₀ * nA K, mul_mem (ox₁_mem_C0 σ hσ3 s₀) (nA_mem σ), fun x hx => ?_⟩
    have hlineH : ∀ f : K, σ f = f → ∃ e f' : K, σ e = e ∧ σ f' = f' ∧
        Xr d4H f = (ox₁ σ s₀ * nA K) * (Xr d4P e * Xr d4H f') * (ox₁ σ s₀ * nA K)⁻¹ := by
      intro f hf
      refine ⟨0, f, map_zero σ, hf, ?_⟩
      rw [← line_eq σ, pinnedX_zero, one_mul, ← (commute_H_ox₁ f s₀ σ).eq,
        mul_inv_cancel_right]
    rcases hpure x hx with ⟨s, β, f, hβ, hf, rfl⟩ | ⟨e, f, he, hf, rfl⟩
    · by_cases hβ0 : β = 0
      · subst hβ0
        rw [pinnedX_zero, one_mul, ← (commute_H_ox₁ f s σ).eq, mul_inv_cancel_right]
        exact hlineH f hf
      · have hs := line_comm_eq σ hσ3 hβ₀ hβ hβ₀0 hβ0 (hcomm _ hx₀ _ hx)
        subst hs
        exact ⟨β, f, hβ, hf, line_eq σ s₀ β f⟩
    · by_cases he0 : e = 0
      · subst he0
        rw [pinnedX_zero, one_mul]
        exact hlineH f hf
      · exact (line_not_comm σ hσ3 hβ₀0 hβ₀ he0 (hcomm _ hx₀ _ hx)).elim
  · push Not at hex
    refine ⟨1, one_mem _, fun x hx => ?_⟩
    rcases hpure x hx with ⟨s, β, f, hβ, hf, rfl⟩ | ⟨e, f, he, hf, rfl⟩
    · have hβ0 : β = 0 := by
        by_contra hβ0
        exact hex _ hx s β f hβ hf hβ0 rfl
      subst hβ0
      refine ⟨0, f, map_zero σ, hf, ?_⟩
      rw [pinnedX_zero, pinnedX_zero, one_mul, one_mul, ← (commute_H_ox₁ f s σ).eq,
        mul_inv_cancel_right]
      group
    · exact ⟨e, f, he, hf, by group⟩

omit
  [Finite K] [CharP K 2] in
theorem conjC_of_mem (c x : C₀) :
    ConjC σ (x : ModGL TwistTag.D4.tag K) ((c⁻¹ * x * c : C₀) : ModGL TwistTag.D4.tag K) :=
  ⟨(c⁻¹ : C₀), (c⁻¹ : C₀).2, by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]⟩

include hσ3 in
theorem involution_conj (ξ : C₀) (hξ : ξ * ξ = 1) (hξ1 : ξ ≠ 1) :
    ConjC σ ξ (Xr d4H 1) ∨ ConjC σ ξ (ox₁ σ 1) := by
  have h2 : IsPGroup 2 (Subgroup.zpowers ξ) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [sq]; exact hξ) hξ1)
  obtain ⟨c, hc⟩ := exists_conj_le_U σ _ h2
  have hU := hc ξ (Subgroup.mem_zpowers ξ)
  have hcξ : ((c⁻¹ * ξ * c : C₀) : ModGL TwistTag.D4.tag K) *
      ((c⁻¹ * ξ * c : C₀) : ModGL TwistTag.D4.tag K) = 1 := by
    rw [← Subgroup.coe_mul]
    have : c⁻¹ * ξ * c * (c⁻¹ * ξ * c) = 1 := by
      calc c⁻¹ * ξ * c * (c⁻¹ * ξ * c) = c⁻¹ * (ξ * ξ) * c := by group
        _ = 1 := by rw [hξ]; group
    rw [this]; rfl
  have hconj := conjC_of_mem σ c ξ
  rcases U_classification σ hσ3 hU hcξ with hp | hx
  · left
    refine hconj.trans σ (pure_conj σ hσ3 hp ?_)
    intro h1
    apply hξ1
    have : c⁻¹ * ξ * c = 1 := Subtype.ext h1
    calc ξ = c * (c⁻¹ * ξ * c) * c⁻¹ := by group
      _ = 1 := by rw [this]; group
  · exact Or.inr (hconj.trans σ hx)

include hσ3 in
theorem elem_line (E : Subgroup C₀) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1)
    (hB : ∀ x ∈ E, x ≠ 1 → ¬ ConjC σ (x : ModGL TwistTag.D4.tag K) (ox₁ σ 1)) :
    ∃ g ∈ C₀, ∀ x ∈ E, ∃ e f : K, σ e = e ∧ σ f = f ∧
      (x : ModGL TwistTag.D4.tag K) = g * (Xr d4P e * Xr d4H f) * g⁻¹ := by
  have h2 : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hsq x x.2)⟩
  obtain ⟨c, hc⟩ := exists_conj_le_U σ E h2
  set E' : Set (ModGL TwistTag.D4.tag K) :=
    {y | ∃ x ∈ E, y = ((c⁻¹ * x * c : C₀) : ModGL TwistTag.D4.tag K)} with hE'
  have hcomm' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    congr 1
    calc c⁻¹ * x * c * (c⁻¹ * y * c) = c⁻¹ * (x * y) * c := by group
      _ = c⁻¹ * (y * x) * c := by rw [hcomm x hx y hy]
      _ = _ := by group
  have hpure : ∀ y ∈ E', IsPure σ y := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hx1 : x = 1
    · subst hx1
      right
      refine ⟨0, 0, map_zero σ, map_zero σ, ?_⟩
      rw [pinnedX_zero, pinnedX_zero, mul_one, mul_one, inv_mul_cancel]
      rfl
    · have hsq' : ((c⁻¹ * x * c : C₀) : ModGL TwistTag.D4.tag K) *
          ((c⁻¹ * x * c : C₀) : ModGL TwistTag.D4.tag K) = 1 := by
        rw [← Subgroup.coe_mul]
        have : c⁻¹ * x * c * (c⁻¹ * x * c) = 1 := by
          calc c⁻¹ * x * c * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c := by group
            _ = 1 := by rw [hsq x hx]; group
        rw [this]; rfl
      rcases U_classification σ hσ3 (hc x hx) hsq' with hp | hconj
      · exact hp
      · exact (hB x hx hx1 ((conjC_of_mem σ c x).trans σ hconj)).elim
  obtain ⟨g, hg, hgE⟩ := pure_line σ hσ3 hcomm' hpure
  refine ⟨c * g, mul_mem c.2 hg, fun x hx => ?_⟩
  obtain ⟨e, f, he, hf, hx'⟩ := hgE _ ⟨x, hx, rfl⟩
  refine ⟨e, f, he, hf, ?_⟩
  have e1 : (x : ModGL TwistTag.D4.tag K) =
      (c : ModGL TwistTag.D4.tag K) * ((c⁻¹ * x * c : C₀) : ModGL TwistTag.D4.tag K) *
        (c : ModGL TwistTag.D4.tag K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [e1, hx']; group

include hσ3 in
theorem card_le_of_pure (E : Subgroup C₀) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1)
    (hB : ∀ x ∈ E, x ≠ 1 → ¬ ConjC σ (x : ModGL TwistTag.D4.tag K) (ox₁ σ 1)) :
    Nat.card E ≤ Nat.card (trialityFixedField K τ₀) ^ 2 := by
  classical
  obtain ⟨g, -, hg⟩ := elem_line σ hσ3 E hcomm hsq hB
  choose e f he hf hx using fun x : E => hg x x.2
  let F : E → trialityFixedField K τ₀ × trialityFixedField K τ₀ :=
    fun x => (⟨e x, he x⟩, ⟨f x, hf x⟩)
  have hF : Function.Injective F := by
    intro x y hxy
    have h1 : e x = e y := congrArg (fun p => (p.1 : K)) hxy
    have h2 : f x = f y := congrArg (fun p => (p.2 : K)) hxy
    apply Subtype.ext; apply Subtype.ext
    rw [hx x, hx y, h1, h2]
  calc Nat.card E ≤ Nat.card (trialityFixedField K τ₀ × trialityFixedField K τ₀) :=
        Nat.card_le_card_of_injective F hF
    _ = _ := by rw [Nat.card_prod, sq]

end Line

end CFSG.Quasithin.B42D4
