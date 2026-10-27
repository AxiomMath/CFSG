module

public import CFSG.Quasithin.Vol2.Ch11SecBK6L

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin.Vol2.KGNat
open scoped commutatorElement

namespace BK6

section CoordSp

variable {G : Type} [Group G] {L V A V₂ : Subgroup G} {K : Type} [Field K]
  {x : ↥V → (Fin 2 ⊕ Fin 2 → K)}

theorem add_params_sp {hAV : A ≤ Subgroup.normalizer (V : Set G)} {α β γ : ↥A → K}
    (hsurj : Function.Surjective x)
    (hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0) (a a' : ↥A) :
    α (a * a') = α a + α a' ∧ β (a * a') = β a + β a' ∧ γ (a * a') = γ a + γ a' := by
  have key : ∀ u : ↥V, x (SecA.conjV V ((a * a' : ↥A) : G) (hAV (a * a').2) u) =
      x (SecA.conjV V a (hAV a.2) (SecA.conjV V a' (hAV a'.2) u)) := fun u => by
    rw [show SecA.conjV V ((a * a' : ↥A) : G) (hAV (a * a').2) =
        SecA.conjV V a (hAV a.2) * SecA.conjV V a' (hAV a'.2) from SecA.conjV_mul V _ _,
      MulAut.mul_apply]
  obtain ⟨w, hw⟩ := hsurj (vec4 0 0 1 0)
  obtain ⟨w', hw'⟩ := hsurj (vec4 0 0 0 1)
  have h1 := key w
  have h2 := key w'
  rw [hact, hact, hact, hw] at h1
  rw [hact, hact, hact, hw'] at h2
  have e0 := congrFun h1 (.inl 0)
  have e1 := congrFun h1 (.inl 1)
  have e2 := congrFun h2 (.inl 1)
  simp only [Pi.add_apply, vec4_apply_inl0, vec4_apply_inl1, vec4_apply_inr0,
    vec4_apply_inr1] at e0 e1 e2
  exact ⟨by linear_combination e0, by linear_combination e1, by linear_combination e2⟩

theorem sup_comm_eq_line_sp {hAV : A ≤ Subgroup.normalizer (V : Set G)} {α β γ : ↥A → K}
    (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u')
    (hker : ∀ u : ↥V, x u = 0 ↔ (u : G) ∈ Subgroup.centralizer (L : Set G))
    (hsurj : Function.Surjective x)
    (hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0)
    {r₀ r₁ u v : K} (huv : u * r₀ + v * r₁ = 1) {t : ↥A → K}
    (ht : ∀ a : ↥A, α a = t a * r₀ ^ 2 ∧ β a = t a * (r₀ * r₁) ∧ γ a = t a * r₁ ^ 2)
    {a₀ : ↥A} (ht₀ : t a₀ ≠ 0) {P : Subgroup G} (hPV : P ≤ V)
    (hP : ∀ w : ↥V, (w : G) ∈ P ↔ ∃ μ : K, x w = μ • vec4 r₀ r₁ 0 0) :
    ⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = P := by
  have hcl : ∀ (a : ↥A) (w : ↥V), x (w * (SecA.conjV V a (hAV a.2) w)⁻¹) =
      (-(t a * (r₀ * x w (.inr 0) + r₁ * x w (.inr 1)))) • vec4 r₀ r₁ 0 0 := fun a w => by
    rw [coord_comm_sp hmul hact, (ht a).1, (ht a).2.1, (ht a).2.2]
    refine vec4_eq ?_ ?_ ?_ ?_ <;>
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, vec4_apply_inl0, vec4_apply_inl1,
        vec4_apply_inr0, vec4_apply_inr1] <;> ring
  refine sup_commutator_eq_of (fun w hw => ?_) (fun w hw a ha => ?_) (fun q hq => ?_)
  · obtain ⟨hwV, hwL⟩ := Subgroup.mem_inf.mp hw
    exact (hP ⟨w, hwV⟩).mpr ⟨0, by rw [(hker ⟨w, hwV⟩).mpr hwL, zero_smul]⟩
  · rw [commutatorElement_eq (hAV ha) ⟨w, hw⟩, hP, hcl ⟨a, ha⟩ ⟨w, hw⟩]
    exact ⟨_, rfl⟩
  · obtain ⟨μ, hμ⟩ := (hP ⟨q, hPV hq⟩).mp hq
    obtain ⟨w, hw⟩ := hsurj (vec4 0 0 (-(μ * (t a₀)⁻¹) * u) (-(μ * (t a₀)⁻¹) * v))
    refine ⟨((w * (SecA.conjV V a₀ (hAV a₀.2) w)⁻¹ : ↥V) : G), ?_, ?_⟩
    · rw [← commutatorElement_eq]
      exact Subgroup.commutator_mem_commutator w.2 a₀.2
    · have hs : -(t a₀ * (r₀ * x w (.inr 0) + r₁ * x w (.inr 1))) = μ := by
        rw [hw, vec4_apply_inr0, vec4_apply_inr1]
        linear_combination (μ * (u * r₀ + v * r₁)) * mul_inv_cancel₀ ht₀ + μ * huv
      have h0 : x (⟨q, hPV hq⟩ * (w * (SecA.conjV V a₀ (hAV a₀.2) w)⁻¹)⁻¹) = 0 := by
        rw [coord_mul_inv hmul, hcl, hs, hμ, sub_self]
      exact Subgroup.mem_inf.mpr ⟨mul_mem (hPV hq) (inv_mem (SetLike.coe_mem _)),
        (hker _).mp h0⟩

theorem relIndex_inf_centralizer_sp {hAV : A ≤ Subgroup.normalizer (V : Set G)}
    {α β γ : ↥A → K} (hmul : ∀ u u' : ↥V, x (u * u') = x u + x u')
    (hsurj : Function.Surjective x)
    (hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0)
    (hfix : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w →
      SecA.conjV V a (hAV a.2) w = w)
    {r₀ r₁ u v : K} (huv : u * r₀ + v * r₁ = 1) {t : ↥A → K}
    (ht : ∀ a : ↥A, α a = t a * r₀ ^ 2 ∧ β a = t a * (r₀ * r₁) ∧ γ a = t a * r₁ ^ 2)
    {a₀ : ↥A} (ht₀ : t a₀ ≠ 0) :
    (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V = Nat.card K := by
  have hS : ∀ (a : ↥A) (w : ↥V), vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
      (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0 =
        (t a * (r₀ * x w (.inr 0) + r₁ * x w (.inr 1))) • vec4 r₀ r₁ 0 0 := fun a w => by
    rw [(ht a).1, (ht a).2.1, (ht a).2.2]
    refine vec4_eq ?_ ?_ ?_ ?_ <;>
      simp only [Pi.smul_apply, smul_eq_mul, vec4_apply_inl0, vec4_apply_inl1,
        vec4_apply_inr0, vec4_apply_inr1] <;> ring
  have hr : (vec4 r₀ r₁ 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h => by
    have e0 := congrFun h (.inl 0)
    have e1 := congrFun h (.inl 1)
    rw [vec4_apply_inl0, Pi.zero_apply] at e0
    rw [vec4_apply_inl1, Pi.zero_apply] at e1
    rw [e0, e1, mul_zero, mul_zero, add_zero] at huv
    exact zero_ne_one huv
  refine relIndex_eq_card_of_hom (fun w => r₀ * x w (.inr 0) + r₁ * x w (.inr 1))
    (fun w w' => by simp only [hmul, Pi.add_apply]; ring)
    (fun c => (hsurj (vec4 0 0 (c * u) (c * v))).imp fun w hw => ?_)
    (fun w => ⟨fun h => ?_, fun h => ?_⟩)
  · show r₀ * x w (.inr 0) + r₁ * x w (.inr 1) = c
    rw [hw, vec4_apply_inr0, vec4_apply_inr1]
    linear_combination c * huv
  · have h1 := hact a₀ w
    rw [conjV_eq_self (hAV a₀.2)
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 a₀ a₀.2),
      left_eq_add, hS, smul_eq_zero] at h1
    exact (mul_eq_zero.mp (h1.resolve_right hr)).resolve_left ht₀
  · refine Subgroup.mem_inf.mpr ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    refine mul_comm_of_conjV_eq (hAV ha) (hfix ⟨a, ha⟩ w ?_)
    rw [hact, hS, show r₀ * x w (.inr 0) + r₁ * x w (.inr 1) = 0 from h, mul_zero, zero_smul,
      add_zero]

theorem relIndex_le_of_line_sp [Finite K] {hAV : A ≤ Subgroup.normalizer (V : Set G)}
    {α β γ : ↥A → K} (hsurj : Function.Surjective x)
    (hact : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w +
      vec4 (α a * x w (.inr 0) + β a * x w (.inr 1))
        (β a * x w (.inr 0) + γ a * x w (.inr 1)) 0 0)
    (hfix : ∀ (a : ↥A) (w : ↥V), x (SecA.conjV V a (hAV a.2) w) = x w →
      SecA.conjV V a (hAV a.2) w = w)
    {r₀ r₁ u v : K} (huv : u * r₀ + v * r₁ = 1) {t : ↥A → K}
    (ht : ∀ a : ↥A, α a = t a * r₀ ^ 2 ∧ β a = t a * (r₀ * r₁) ∧ γ a = t a * r₁ ^ 2) :
    (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ Nat.card K := by
  have htf : ∀ a : ↥A, t a = u ^ 2 * α a + 2 * u * v * β a + v ^ 2 * γ a := fun a => by
    rw [(ht a).1, (ht a).2.1, (ht a).2.2]
    linear_combination (-(t a) * (u * r₀ + v * r₁ + 1)) * huv
  refine relIndex_le_of_hom t (fun a a' => ?_) (fun a ha => ?_)
  · obtain ⟨h1, h2, h3⟩ := add_params_sp hsurj hact a a'
    rw [htf, htf a, htf a', h1, h2, h3]
    ring
  · refine Subgroup.mem_inf.mpr ⟨a.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    refine (mul_comm_of_conjV_eq (hAV a.2) (hfix a ⟨w, hw⟩ ?_)).symm
    rw [hact, (ht a).1, (ht a).2.1, (ht a).2.2, ha]
    simp only [zero_mul, add_zero, vec4_zero]

end CoordSp

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
