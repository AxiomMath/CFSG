module

public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin

namespace B69

section Perm5

open Equiv

private theorem perm5_sq_eq_one_of_pow_four {x : Perm (Fin 5)} (hx : x ∈ alternatingGroup (Fin 5))
    (h4 : x ^ 4 = 1) : x ^ 2 = 1 := by
  have key : ∀ y : Perm (Fin 5), Perm.sign y = 1 → y ^ 4 = 1 → y ^ 2 = 1 := by
    set_option maxRecDepth 100000 in decide
  exact key x (Perm.mem_alternatingGroup.mp hx) h4

private theorem perm5_exists_unique_fixed {x : Perm (Fin 5)} (hx : Perm.sign x = 1) (h2 : x ^ 2 = 1)
    (h1 : x ≠ 1) : ∃ p, x p = p ∧ ∀ q, x q = q → q = p := by
  have key : ∀ y : Perm (Fin 5), Perm.sign y = 1 → y ^ 2 = 1 → y ≠ 1 →
      ∃ p, y p = p ∧ ∀ q, y q = q → q = p := by
    set_option maxRecDepth 100000 in decide
  exact key x hx h2 h1

private theorem perm5_card_fixing (p : Fin 5) :
    (Finset.univ.filter (fun x : Perm (Fin 5) => Perm.sign x = 1 ∧ x ^ 2 = 1 ∧ x p = p)).card = 4 := by
  have key : ∀ q : Fin 5, (Finset.univ.filter (fun x : Perm (Fin 5) =>
      Perm.sign x = 1 ∧ x ^ 2 = 1 ∧ x q = q)).card = 4 := by
    set_option maxRecDepth 100000 in decide
  exact key p

theorem perm5_normalizer_of_card_four (V : Subgroup (Equiv.Perm (Fin 5)))
    (hVA : V ≤ alternatingGroup (Fin 5)) (hV4 : Nat.card V = 4) :
    ∃ p : Fin 5, ∀ σ : Equiv.Perm (Fin 5),
      σ ∈ Subgroup.normalizer (V : Set (Equiv.Perm (Fin 5))) ↔ σ p = p := by
  classical
  have hsq : ∀ x ∈ V, x ^ 2 = 1 := by
    intro x hx
    have h4 : (⟨x, hx⟩ : V) ^ Nat.card V = 1 := pow_card_eq_one'
    rw [hV4] at h4
    exact perm5_sq_eq_one_of_pow_four (hVA hx) (congrArg Subtype.val h4)
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq y hy)
    have hxyi : (x * y)⁻¹ = x * y :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq _ (V.mul_mem hx hy))
    rw [mul_inv_rev, hxi, hyi] at hxyi
    exact hxyi.symm
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ V, x ≠ 1 := by
    by_contra hcon
    have hbot : V = ⊥ :=
      (Subgroup.eq_bot_iff_forall V).mpr fun x hx => by_contra fun hne => hcon ⟨x, hx, hne⟩
    rw [hbot, Subgroup.card_bot] at hV4
    omega
  obtain ⟨p, hp, hpu⟩ := perm5_exists_unique_fixed (Perm.mem_alternatingGroup.mp (hVA hx₀))
    (hsq x₀ hx₀) hx₀1
  have hfix : ∀ y ∈ V, y p = p := by
    intro y hy
    apply hpu
    have h := hcomm x₀ hx₀ y hy
    calc x₀ (y p) = (x₀ * y) p := rfl
      _ = (y * x₀) p := by rw [h]
      _ = y p := by simp [Perm.mul_apply, hp]
  have hVK : ∀ x : Perm (Fin 5), x ∈ V ↔ (Perm.sign x = 1 ∧ x ^ 2 = 1 ∧ x p = p) := by
    set Kp : Finset (Perm (Fin 5)) :=
      Finset.univ.filter (fun x : Perm (Fin 5) => Perm.sign x = 1 ∧ x ^ 2 = 1 ∧ x p = p) with hKp
    set Vf : Finset (Perm (Fin 5)) := Finset.univ.filter (fun x => x ∈ V) with hVf
    have hsub : Vf ⊆ Kp := by
      intro x hx
      rw [hVf, Finset.mem_filter] at hx
      rw [hKp, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Perm.mem_alternatingGroup.mp (hVA hx.2), hsq x hx.2, hfix x hx.2⟩
    have hcardV : Vf.card = 4 := by
      rw [hVf, ← hV4, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hcardK : Kp.card = 4 := perm5_card_fixing p
    have heq : Vf = Kp := Finset.eq_of_subset_of_card_le hsub (by rw [hcardV, hcardK])
    intro x
    constructor
    · intro hx
      exact ⟨Perm.mem_alternatingGroup.mp (hVA hx), hsq x hx, hfix x hx⟩
    · intro hx
      have hxK : x ∈ Kp := by
        rw [hKp, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hx⟩
      rw [← heq, hVf, Finset.mem_filter] at hxK
      exact hxK.2
  have hconj : ∀ τ : Perm (Fin 5), τ p = p → ∀ x ∈ V, τ * x * τ⁻¹ ∈ V := by
    intro τ hτ x hx
    rw [hVK] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    have hτi : τ⁻¹ p = p := by rw [Perm.inv_def, Equiv.symm_apply_eq]; exact hτ.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, map_mul, h1, map_inv, mul_one, mul_inv_cancel]
    · rw [conj_pow, h2, mul_one, mul_inv_cancel]
    · simp [Perm.mul_apply, hτi, h3, hτ]
  refine ⟨p, fun σ => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hσ
    have h1 := (hσ x₀).mp hx₀
    have h2 : (σ * x₀ * σ⁻¹) p = p := hfix _ h1
    have h3 : x₀ (σ⁻¹ p) = σ⁻¹ p := by
      have h4 : σ (x₀ (σ⁻¹ p)) = p := h2
      calc x₀ (σ⁻¹ p) = σ⁻¹ (σ (x₀ (σ⁻¹ p))) := by simp
        _ = σ⁻¹ p := by rw [h4]
    have h5 : σ⁻¹ p = p := hpu _ h3
    calc σ p = σ (σ⁻¹ p) := by rw [h5]
      _ = p := by simp
  · intro hσ x
    constructor
    · exact hconj σ hσ x
    · intro hx
      have hσi : σ⁻¹ p = p := by rw [Perm.inv_def, Equiv.symm_apply_eq]; exact hσ.symm
      have h1 := hconj σ⁻¹ hσi _ hx
      have e : σ⁻¹ * (σ * x * σ⁻¹) * σ⁻¹⁻¹ = x := by group
      rwa [e] at h1

end Perm5

theorem perm5_stabilizer_coatom (p : Fin 5) (R : Subgroup (Equiv.Perm (Fin 5)))
    (hR : MulAction.stabilizer (Equiv.Perm (Fin 5)) p ≤ R) :
    R = MulAction.stabilizer (Equiv.Perm (Fin 5)) p ∨ R = ⊤ := by
  have hpre : MulAction.IsPreprimitive (Equiv.Perm (Fin 5)) (Fin 5) :=
    MulAction.isPreprimitive_of_is_two_pretransitive (Equiv.Perm.isMultiplyPretransitive _ 2)
  have hcoatom := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (Equiv.Perm (Fin 5)) p
  rcases hR.lt_or_eq with h | h
  · exact Or.inr (hcoatom.2 R h)
  · exact Or.inl h.symm

private theorem surjective_comp_conj {G K : Type*} [Group G] [Group K] {π : G →* K}
    (hπ : Function.Surjective π) (ρ : G) :
    Function.Surjective (π.comp (MulAut.conj ρ).toMonoidHom) := by
  rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact hπ.comp (MulAut.conj ρ).surjective

theorem realizesVia_conj_of_isActionModel {V : Type*} [CommGroup V] {D : FFModel}
    (hD : D.IsActionModel) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) (ρ : D.Gam) :
    D.RealizesVia H U Z (π.comp (MulAut.conj ρ).toMonoidHom) := by
  obtain ⟨hsurj, hZU, hker, hU, hZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  refine ⟨surjective_comp_conj hsurj ρ, hZU, hker, hU, hZ, hsec, hkerinv,
    (hD.modAct ρ⁻¹).toMonoidHom.comp β, ?_, ?_, ?_⟩
  · rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact (hD.modAct ρ⁻¹).surjective.comp hβs
  · intro u
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact hβk u
  · intro γ u m hu hm hum
    have hmρ : D.act ρ (m : D.Amb) ∈ D.sec := hsec ρ m m.2
    have hβu : β u = QuotientGroup.mk (⟨D.act ρ (m : D.Amb), hmρ⟩ : ↥D.sec) := by
      have h1 : hD.modAct ρ⁻¹ (β u) = QuotientGroup.mk m := hum
      have h2 : β u = hD.modAct ρ (hD.modAct ρ⁻¹ (β u)) := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      rw [h2, h1, hD.modAct_apply, hD.modEnd_mk]
      rfl
    have hm' : D.act (ρ * γ * ρ⁻¹) (D.act ρ (m : D.Amb)) ∈ D.sec := hsec _ _ hmρ
    have h3 := hβe (ρ * γ * ρ⁻¹) u ⟨_, hmρ⟩ hu hm' hβu
    show hD.modAct ρ⁻¹ (β ⟨_, hu⟩) = QuotientGroup.mk ⟨D.act γ m, hm⟩
    have h4 : β ⟨_, hu⟩ = QuotientGroup.mk
        (⟨D.act (ρ * γ * ρ⁻¹) (D.act ρ (m : D.Amb)), hm'⟩ : ↥D.sec) := h3
    rw [h4, hD.modAct_apply, hD.modEnd_mk]
    congr 1
    apply Subtype.ext
    show D.act ρ⁻¹ (D.act (ρ * γ * ρ⁻¹) (D.act ρ (m : D.Amb))) = D.act γ m
    rw [← hD.act_mul_act, ← hD.act_mul_act]
    congr 1
    group

theorem symDn_realizesVia_conj {V : Type*} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : Equiv.Perm (Fin n) →* ↥H}
    (h : (FFModel.symDn n).RealizesVia H U Z π) (ρ : Equiv.Perm (Fin n)) :
    (FFModel.symDn n).RealizesVia H U Z (π.comp (MulAut.conj ρ).toMonoidHom) :=
  realizesVia_conj_of_isActionModel (FFModel.symDn_isActionModel n) h ρ

end B69

end CFSG.Quasithin
