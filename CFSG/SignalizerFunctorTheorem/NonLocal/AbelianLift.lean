module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Weights
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open Module Module.End CFSG.SignalizerFunctorTheorem.NonLocal

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {F W G : Type*} [Field F] [AddCommGroup W] [Module F W] [Group G]


@[expose] def IsWeight (ρ : G →* End F W) (A : Subgroup G) (χ : A → F) : Prop :=
  ∃ w : W, w ≠ 0 ∧ ∀ a : A, ρ a w = χ a • w

theorem IsWeight.mul {ρ : G →* End F W} {A : Subgroup G} {χ : A → F} (h : IsWeight ρ A χ)
    (a b : A) : χ (a * b) = χ a * χ b := by
  obtain ⟨w, hw0, hw⟩ := h
  have h1 : ρ ((a * b : A) : G) w = (χ a * χ b) • w := by
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hw b, map_smul, hw a, smul_smul,
      mul_comm]
  have h2 := hw (a * b)
  rw [h1] at h2
  exact (smul_left_injective F hw0 h2).symm

theorem IsWeight.one {ρ : G →* End F W} {A : Subgroup G} {χ : A → F} (h : IsWeight ρ A χ) :
    χ 1 = 1 := by
  obtain ⟨w, hw0, hw⟩ := h
  have := hw 1
  rw [Subgroup.coe_one, map_one, Module.End.one_apply] at this
  have h3 : (1 - χ 1) • w = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h hw0

theorem IsWeight.ne_zero {ρ : G →* End F W} {A : Subgroup G} {χ : A → F} (h : IsWeight ρ A χ)
    (a : A) : χ a ≠ 0 := by
  intro h0
  have := h.mul a a⁻¹
  rw [mul_inv_cancel, h.one, h0, zero_mul] at this
  exact one_ne_zero this

theorem IsWeight.pow {ρ : G →* End F W} {A : Subgroup G} {χ : A → F} (h : IsWeight ρ A χ)
    (a : A) (n : ℕ) : χ (a ^ n) = χ a ^ n := by
  induction n with
  | zero => simp [h.one]
  | succ n ih => rw [pow_succ, h.mul, ih, pow_succ]

theorem IsWeight.inv {ρ : G →* End F W} {A : Subgroup G} {χ : A → F} (h : IsWeight ρ A χ)
    (a : A) : χ a⁻¹ = (χ a)⁻¹ := by
  have := h.mul a a⁻¹
  rw [mul_inv_cancel, h.one] at this
  exact eq_inv_of_mul_eq_one_right this.symm


section Finite

variable [FiniteDimensional F W]

theorem finite_card_weights (ρ : G →* End F W) (A : Subgroup G) (hA : IsMulCommutative A) :
    Finite {χ : A → F // IsWeight ρ A χ} ∧
      Nat.card {χ : A → F // IsWeight ρ A χ} ≤ finrank F W := by
  choose w hw0 hw using fun χ : {χ : A → F // IsWeight ρ A χ} => χ.2
  have hli : LinearIndependent F w :=
    linearIndependent_of_distinct_weights ρ A hA w (fun χ => χ.1) hw0 hw Subtype.val_injective
  have hfin : Finite {χ : A → F // IsWeight ρ A χ} := hli.finite
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite {χ : A → F // IsWeight ρ A χ}
  rw [Nat.card_eq_fintype_card]
  exact hli.fintype_card_le_finrank

variable [IsAlgClosed F]

theorem eq_smul_one_of_weights (ρ : G →* End F W) (A : Subgroup G) (hA : IsMulCommutative A)
    [Finite A] (hinv : (Nat.card A : F) ≠ 0) (g : G) (c : F)
    (hg : ∀ χ : A → F, IsWeight ρ A χ → ∀ w : W, (∀ a : A, ρ a w = χ a • w) → ρ g w = c • w) :
    ρ g = c • 1 := by
  by_contra hne
  have hT : ρ g - c • 1 ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨χ, w, hev, hTw⟩ := exists_jointEigenvector_apply_ne_zero ρ A hA hinv _ hT
  apply hTw
  rw [LinearMap.sub_apply, hg χ ⟨w, ?_, hev⟩ w hev]
  · simp
  · rintro rfl
    exact hTw (map_zero _)

end Finite


section Alpha

variable [FiniteDimensional F W]

omit [Module F W] in
theorem finite_nthRoots (F : Type*) [Field F] (s : ℕ) (hs : 0 < s) :
    Finite {u : F // u ^ s = 1} := by
  classical
  have h1 : {u : F // u ^ s = 1} ≃ (Polynomial.nthRootsFinset s (1 : F)) :=
    Equiv.subtypeEquivRight (fun u => (Polynomial.mem_nthRootsFinset hs (1 : F)).symm)
  exact Finite.of_equiv _ h1.symm

omit [Module F W] in
theorem card_nthRoots_le (F : Type*) [Field F] (s : ℕ) (hs : 0 < s) :
    Nat.card {u : F // u ^ s = 1} ≤ s := by
  classical
  have h1 : {u : F // u ^ s = 1} ≃ (Polynomial.nthRootsFinset s (1 : F)) :=
    Equiv.subtypeEquivRight (fun u => (Polynomial.mem_nthRootsFinset hs (1 : F)).symm)
  rw [Nat.card_congr h1, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

variable [IsAlgClosed F]

theorem card_le_of_abelian_mod_scalars {s : ℕ} (hs : 0 < s)
    (ρ : G →* End F W) (Zs A : Subgroup G) [Finite A] (hA : IsMulCommutative A)
    (hinv : (Nat.card A : F) ≠ 0) (hZA : Zs ≤ A)
    (hZs : ∀ g, g ∈ Zs ↔ ∃ c : F, ρ g = c • 1) (hexp : ∀ a ∈ A, a ^ s ∈ Zs)
    [Nontrivial W] :
    Nat.card A ≤ Nat.card Zs * s ^ (finrank F W - 1) := by
  classical
  obtain ⟨hΨfin, hΨcard⟩ := finite_card_weights ρ A hA
  have : Finite {χ : A → F // IsWeight ρ A χ} := hΨfin
  obtain ⟨χ₀, w₀, hev₀, hTw⟩ := exists_jointEigenvector_apply_ne_zero ρ A hA hinv 1 one_ne_zero
  have hw₀ : w₀ ≠ 0 := by
    rintro rfl
    exact hTw (map_zero _)
  let ψ₀ : {χ : A → F // IsWeight ρ A χ} := ⟨χ₀, w₀, hw₀, hev₀⟩
  let Θ : A → ({χ : A → F // IsWeight ρ A χ} → F) := fun a ψ => ψ.1 a / ψ₀.1 a
  let Zs' : Subgroup A := Zs.subgroupOf A
  have hscalar : ∀ g : A, (g : G) ∈ Zs →
      ∃ c : F, ∀ ψ : {χ : A → F // IsWeight ρ A χ}, ψ.1 g = c := by
    intro g hg
    obtain ⟨c, hc⟩ := (hZs _).mp hg
    refine ⟨c, fun ψ => ?_⟩
    obtain ⟨w, hw0, hw⟩ := ψ.2
    have h1 := hw g
    rw [hc, LinearMap.smul_apply, Module.End.one_apply] at h1
    exact (smul_left_injective F hw0 h1).symm
  have hkey : ∀ a b : A, Θ a = Θ b ↔ (a⁻¹ * b : A) ∈ Zs' := by
    intro a b
    constructor
    · intro h
      have hc : ∀ ψ : {χ : A → F // IsWeight ρ A χ},
          ψ.1 (a⁻¹ * b) = ψ₀.1 (a⁻¹ * b) := by
        intro ψ
        have h1 := congrFun h ψ
        simp only [Θ] at h1
        have hne := ψ.2.ne_zero
        have hne₀ := ψ₀.2.ne_zero
        have h2 : ψ.1 b * ψ₀.1 a = ψ.1 a * ψ₀.1 b := by
          field_simp [hne a, hne b, hne₀ a, hne₀ b] at h1
          rw [mul_comm]
          exact h1.symm
        rw [ψ.2.mul, ψ₀.2.mul, ψ.2.inv, ψ₀.2.inv]
        field_simp [hne a, hne₀ a]
        exact h2
      have h3 : ρ ((a⁻¹ * b : A) : G) = ψ₀.1 (a⁻¹ * b) • 1 :=
        eq_smul_one_of_weights ρ A hA hinv _ _ (fun χ hχ w hw => by
          have := hc ⟨χ, hχ⟩
          simp only at this
          rw [hw, this])
      exact (hZs _).mpr ⟨_, h3⟩
    · intro h
      obtain ⟨c, hc⟩ := hscalar (a⁻¹ * b) h
      funext ψ
      simp only [Θ]
      have hb : b = a * (a⁻¹ * b) := by group
      have e1 : ψ.1 b = ψ.1 a * c := by rw [hb, ψ.2.mul, hc ψ]
      have e2 : ψ₀.1 b = ψ₀.1 a * c := by rw [hb, ψ₀.2.mul, hc ψ₀]
      have hcne : c ≠ 0 := by rw [← hc ψ₀]; exact ψ₀.2.ne_zero _
      rw [e1, e2]
      have := ψ₀.2.ne_zero a
      field_simp
  let Θ' : A ⧸ Zs' → ({χ : A → F // IsWeight ρ A χ} → F) :=
    Quotient.lift Θ (fun a b hab => (hkey a b).mpr (QuotientGroup.leftRel_apply.mp hab))
  have hΘ'inj : Function.Injective Θ' := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hkey a b).mp hxy))
  have hrange : ∀ x, Θ' x ∈ {f : {χ : A → F // IsWeight ρ A χ} → F |
      f ψ₀ = 1 ∧ ∀ ψ, f ψ ^ s = 1} := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
    refine ⟨?_, fun ψ => ?_⟩
    · show ψ₀.1 a / ψ₀.1 a = 1
      exact div_self (ψ₀.2.ne_zero a)
    · show (ψ.1 a / ψ₀.1 a) ^ s = 1
      obtain ⟨c, hc⟩ := hscalar (a ^ s) (by simpa using hexp a a.2)
      have e1 : ψ.1 a ^ s = c := by rw [← ψ.2.pow, hc ψ]
      have e2 : ψ₀.1 a ^ s = c := by rw [← ψ₀.2.pow, hc ψ₀]
      have hcne : c ≠ 0 := by rw [← hc ψ₀]; exact ψ₀.2.ne_zero _
      rw [div_pow, e1, e2, div_self hcne]
  let S : Set ({χ : A → F // IsWeight ρ A χ} → F) :=
    {f | f ψ₀ = 1 ∧ ∀ ψ, f ψ ^ s = 1}
  have : Finite {u : F // u ^ s = 1} := finite_nthRoots F s hs
  let e : S → ({ψ : {χ : A → F // IsWeight ρ A χ} // ψ ≠ ψ₀} → {u : F // u ^ s = 1}) :=
    fun f ψ => ⟨f.1 ψ.1, f.2.2 ψ.1⟩
  have he : Function.Injective e := by
    intro f g hfg
    apply Subtype.ext
    funext ψ
    by_cases h : ψ = ψ₀
    · rw [h, f.2.1, g.2.1]
    · have := congrFun hfg ⟨ψ, h⟩
      exact congrArg Subtype.val this
  have : Finite S := Finite.of_injective e he
  have hS : Nat.card S ≤ s ^ (Nat.card {χ : A → F // IsWeight ρ A χ} - 1) := by
    have h1 : Nat.card S ≤ Nat.card ({ψ : {χ : A → F // IsWeight ρ A χ} // ψ ≠ ψ₀} →
        {u : F // u ^ s = 1}) := Nat.card_le_card_of_injective e he
    have h2 : Nat.card {ψ : {χ : A → F // IsWeight ρ A χ} // ψ ≠ ψ₀} =
        Nat.card {χ : A → F // IsWeight ρ A χ} - 1 := by
      have := Fintype.ofFinite {χ : A → F // IsWeight ρ A χ}
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [Nat.card_fun, h2] at h1
    exact h1.trans (Nat.pow_le_pow_left (card_nthRoots_le F s hs) _)
  have hS' : Nat.card S ≤ s ^ (finrank F W - 1) :=
    hS.trans (Nat.pow_le_pow_right hs (Nat.sub_le_sub_right hΨcard 1))
  have hq : Nat.card (A ⧸ Zs') ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective (fun x => (⟨Θ' x, hrange x⟩ : S)) ?_
    intro x y hxy
    exact hΘ'inj (congrArg Subtype.val hxy)
  have hZ : Nat.card Zs' = Nat.card Zs := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zs', hZ, mul_comm]
  exact Nat.mul_le_mul_left _ (hq.trans hS')

end Alpha


end CFSG.SignalizerFunctorTheorem.NonLocal
