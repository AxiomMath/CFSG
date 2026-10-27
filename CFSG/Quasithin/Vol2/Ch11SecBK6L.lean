module

public import CFSG.Quasithin.Vol2.Ch11SecBK6J

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin.Vol2.KGNat
open scoped commutatorElement

namespace BK6

section CoordSp

variable {G : Type} [Group G] {L V A V₂ : Subgroup G} {K : Type} [Field K]
  {x : ↥V → (Fin 2 ⊕ Fin 2 → K)}

theorem vec4_zero : (vec4 0 0 0 0 : Fin 2 ⊕ Fin 2 → K) = 0 := vec4_eq rfl rfl rfl rfl

theorem coord_comm_sp {hAV : A ≤ Subgroup.normalizer (V : Set G)} {α β γ : ↥A → K}
    (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u')
    (hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0) (a : ↥A) (w : ↥V) :
    x (w * (SecA.conjV V a (hAV a.2) w)⁻¹) =
      -vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0 := by
  rw [coord_mul_inv hmul, hact, sub_add_cancel_left]

theorem le_inf_centralizer_sp {hAV : A ≤ Subgroup.normalizer (V : Set G)} {α β γ : ↥A → K}
    (hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0)
    (hfix : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w →
      SecA.conjV V a (hAV a.2) w = w) (hV₂V : V₂ ≤ V)
    (hV₂ : ∀ w : ↥V, (w : G) ∈ V₂ ↔ x w (.inr 0) = 0 ∧ x w (.inr 1) = 0) :
    V₂ ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
  intro v hv
  refine Subgroup.mem_inf.mpr ⟨hV₂V hv, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
  obtain ⟨h2, h3⟩ := (hV₂ ⟨v, hV₂V hv⟩).mp hv
  refine mul_comm_of_conjV_eq (hAV ha) (hfix ⟨a, ha⟩ ⟨v, hV₂V hv⟩ ?_)
  rw [hact, h2, h3]
  simp only [mul_zero, add_zero, vec4_zero]

theorem inf_centralizer_eq_of_det_sp {hAV : A ≤ Subgroup.normalizer (V : Set G)}
    {α β γ : ↥A → K}
    (hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0)
    (hfix : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w →
      SecA.conjV V a (hAV a.2) w = w) (hV₂V : V₂ ≤ V)
    (hV₂ : ∀ w : ↥V, (w : G) ∈ V₂ ↔ x w (.inr 0) = 0 ∧ x w (.inr 1) = 0) {a₀ : ↥A}
    (hD : α a₀ * γ a₀ - β a₀ ^ 2 ≠ 0) :
    V ⊓ Subgroup.centralizer (A : Set G) = V₂ := by
  refine le_antisymm (fun v hv => ?_) (le_inf_centralizer_sp hact hfix hV₂V hV₂)
  obtain ⟨hvV, hvA⟩ := Subgroup.mem_inf.mp hv
  have h := hact a₀ ⟨v, hvV⟩
  rw [conjV_eq_self (hAV a₀.2) (Subgroup.mem_centralizer_iff.mp hvA a₀ a₀.2), left_eq_add] at h
  have e0 := congrFun h (.inl 0)
  have e1 := congrFun h (.inl 1)
  rw [vec4_apply_inl0, Pi.zero_apply] at e0
  rw [vec4_apply_inl1, Pi.zero_apply] at e1
  refine (hV₂ ⟨v, hvV⟩).mpr ⟨?_, ?_⟩
  · have h' : x ⟨v, hvV⟩ (.inr 0) * (α a₀ * γ a₀ - β a₀ ^ 2) = 0 := by
      linear_combination γ a₀ * e0 - β a₀ * e1
    exact (mul_eq_zero.mp h').resolve_right hD
  · have h' : x ⟨v, hvV⟩ (.inr 1) * (α a₀ * γ a₀ - β a₀ ^ 2) = 0 := by
      linear_combination α a₀ * e1 - β a₀ * e0
    exact (mul_eq_zero.mp h').resolve_right hD

theorem sup_comm_eq_plane_sp {hAV : A ≤ Subgroup.normalizer (V : Set G)} {α β γ : ↥A → K}
    (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u')
    (hker : ∀ u : ↥V, x u = 0 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G))
    (hsurj : Function.Surjective x)
    (hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0) (hV₂V : V₂ ≤ V)
    (hV₂ : ∀ w : ↥V, (w : G) ∈ V₂ ↔ x w (.inr 0) = 0 ∧ x w (.inr 1) = 0) {a₀ : ↥A}
    (hD : α a₀ * γ a₀ - β a₀ ^ 2 ≠ 0) :
    ⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V₂ := by
  refine sup_commutator_eq_of (fun v hv => ?_) (fun v hv a ha => ?_) (fun q hq => ?_)
  · obtain ⟨hvV, hvL⟩ := Subgroup.mem_inf.mp hv
    refine (hV₂ ⟨v, hvV⟩).mpr ?_
    rw [(hker ⟨v, hvV⟩).mpr hvL]
    exact ⟨rfl, rfl⟩
  · rw [commutatorElement_eq (hAV ha) ⟨v, hv⟩, hV₂, coord_comm_sp hmul hact ⟨a, ha⟩ ⟨v, hv⟩]
    exact ⟨by rw [Pi.neg_apply, vec4_apply_inr0, neg_zero],
      by rw [Pi.neg_apply, vec4_apply_inr1, neg_zero]⟩
  · obtain ⟨hq2, hq3⟩ := (hV₂ ⟨q, hV₂V hq⟩).mp hq
    obtain ⟨l₂, l₃, h₂, h₃⟩ : ∃ l₂ l₃ : K,
        α a₀ * l₂ + β a₀ * l₃ = -x ⟨q, hV₂V hq⟩ (.inl 0) ∧
          β a₀ * l₂ + γ a₀ * l₃ = -x ⟨q, hV₂V hq⟩ (.inl 1) :=
      ⟨(β a₀ * x ⟨q, hV₂V hq⟩ (.inl 1) - γ a₀ * x ⟨q, hV₂V hq⟩ (.inl 0)) /
          (α a₀ * γ a₀ - β a₀ ^ 2),
        (β a₀ * x ⟨q, hV₂V hq⟩ (.inl 0) - α a₀ * x ⟨q, hV₂V hq⟩ (.inl 1)) /
          (α a₀ * γ a₀ - β a₀ ^ 2),
        by linear_combination (-x ⟨q, hV₂V hq⟩ (.inl 0)) * inv_mul_cancel₀ hD,
        by linear_combination (-x ⟨q, hV₂V hq⟩ (.inl 1)) * inv_mul_cancel₀ hD⟩
    obtain ⟨w, hw⟩ := hsurj (vec4 0 0 l₂ l₃)
    refine ⟨((w * (SecA.conjV V a₀ (hAV a₀.2) w)⁻¹ : ↥V) : G), ?_, ?_⟩
    · rw [← commutatorElement_eq]
      exact Subgroup.commutator_mem_commutator w.2 a₀.2
    · have h0 : x (⟨q, hV₂V hq⟩ * (w * (SecA.conjV V a₀ (hAV a₀.2) w)⁻¹)⁻¹) = 0 := by
        rw [coord_mul_inv hmul, coord_comm_sp hmul hact, hw, sub_neg_eq_add]
        refine vec4_eq ?_ ?_ ?_ ?_ <;>
          simp only [Pi.add_apply, Pi.zero_apply, vec4_apply_inl0, vec4_apply_inl1,
            vec4_apply_inr0, vec4_apply_inr1, hq2, hq3, add_zero]
        · linear_combination h₂
        · linear_combination h₃
      exact Subgroup.mem_inf.mpr ⟨mul_mem (hV₂V hq) (inv_mem (SetLike.coe_mem _)),
        (hker _).mp h0⟩

theorem exists_root_form [CharP K 2] {ι : Type*} {α β γ : ι → K}
    (hsing : ∀ i, α i * γ i = β i ^ 2) (i₀ : ι)
    (hsum : ∀ i, (α i + α i₀) * (γ i + γ i₀) = (β i + β i₀) ^ 2)
    (h₀ : ¬ (α i₀ = 0 ∧ β i₀ = 0 ∧ γ i₀ = 0)) :
    ∃ r₀ r₁ : K, (∃ u v : K, u * r₀ + v * r₁ = 1) ∧ ∀ i, ∃ t : K,
      α i = t * r₀ ^ 2 ∧ β i = t * (r₀ * r₁) ∧ γ i = t * r₁ ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hE : ∀ i, α i * γ i₀ + α i₀ * γ i = 0 := fun i => by
    linear_combination hsum i - hsing i - hsing i₀ + β i * β i₀ * h2
  by_cases hα : α i₀ = 0
  · have hβ : β i₀ = 0 := by
      have h := hsing i₀
      rw [hα, zero_mul] at h
      exact (pow_eq_zero_iff two_ne_zero).mp h.symm
    have hγ : γ i₀ ≠ 0 := fun hγ => h₀ ⟨hα, hβ, hγ⟩
    have hαi : ∀ i, α i = 0 := fun i => by
      have h := hE i
      rw [hα, zero_mul, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hγ
    refine ⟨0, 1, ⟨0, 1, by ring⟩, fun i => ⟨γ i, by rw [hαi i]; ring, ?_, by ring⟩⟩
    have h := hsing i
    rw [hαi i, zero_mul] at h
    rw [(pow_eq_zero_iff two_ne_zero).mp h.symm]
    ring
  · refine ⟨α i₀, β i₀, ⟨(α i₀)⁻¹, 0, by rw [zero_mul, add_zero, inv_mul_cancel₀ hα]⟩,
      fun i => ⟨α i / α i₀ ^ 2, (div_mul_cancel₀ _ (pow_ne_zero 2 hα)).symm, ?_, ?_⟩⟩
    · have hsq : (α i₀ * β i - α i * β i₀) ^ 2 = 0 := by
        linear_combination α i₀ * α i * hE i - α i₀ ^ 2 * hsing i - α i ^ 2 * hsing i₀ -
          α i₀ * α i * β i * β i₀ * h2
      have hlin : α i₀ * β i - α i * β i₀ = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
      rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hα)]
      linear_combination α i₀ * hlin
    · have hlin : α i₀ * γ i - α i * γ i₀ = 0 := by
        linear_combination hE i - α i * γ i₀ * h2
      rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hα)]
      linear_combination α i₀ * hlin + α i * hsing i₀

end CoordSp

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
