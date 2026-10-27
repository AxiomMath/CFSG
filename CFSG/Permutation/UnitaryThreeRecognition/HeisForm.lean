module

public import CFSG.Permutation.UnitaryThreeRecognition.HeisNumber
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

open Polynomial

theorem card_pow_eq_mul_le {A : Type*} [Field A] [Finite A] (n : ℕ) (hn : 2 ≤ n) (a : A) :
    Nat.card {c : A // c ^ n = a * c} ≤ n := by
  classical
  have : Fintype A := Fintype.ofFinite A
  set P : A[X] := X ^ n - C a * X with hP
  have hdeg : P.natDegree = n := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
    calc (C a * X).natDegree ≤ 1 := (natDegree_C_mul_le a X).trans natDegree_X_le
      _ < n := by omega
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Finset.univ.filter fun c : A => c ^ n = a * c).card ≤ P.natDegree := by
        apply card_le_degree_of_subset_roots
        intro c hc
        rw [Finset.mem_val, Finset.mem_filter] at hc
        rw [mem_roots hP0, IsRoot, hP, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_X,
          hc.2, sub_self]
    _ = n := hdeg

section Form

variable {A : Type*} [Field A] {Z₀ : Type*} [AddCommGroup Z₀]

theorem form_antisymm (β : A →+ A →+ Z₀) (halt : ∀ c, β c c = 0) (c c' : A) :
    β c c' = -β c' c := by
  have h := halt (c + c')
  simp only [map_add, AddMonoidHom.add_apply, halt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)

@[expose] def formTwist (β : A →+ A →+ Z₀) (θ : A) : A →+ A →+ Z₀ :=
  β.comp (AddMonoidHom.mulLeft θ) + (β.flip.comp (AddMonoidHom.mulLeft θ)).flip

theorem formTwist_apply (β : A →+ A →+ Z₀) (θ c c' : A) :
    formTwist β θ c c' = β (θ * c) c' + β c (θ * c') := rfl

variable (p f : ℕ) [Fact p.Prime] [CharP A p]

@[expose] def formSubfield (β : A →+ A →+ Z₀) : Subfield A where
  carrier := {α | ∀ c c', β (α * c) c' = β c (iterateFrobenius A p f α * c')}
  zero_mem' c c' := by simp
  one_mem' c c' := by simp
  add_mem' {α α'} hα hα' c c' := by
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul, map_add, AddMonoidHom.add_apply, hα, hα', map_add, add_mul, map_add]
  neg_mem' {α} hα c c' := by
    simp only [Set.mem_ofPred_eq] at *
    rw [neg_mul, map_neg, AddMonoidHom.neg_apply, hα, map_neg, neg_mul, map_neg]
  mul_mem' {α α'} hα hα' c c' := by
    simp only [Set.mem_ofPred_eq] at *
    rw [mul_assoc, hα, hα', map_mul (iterateFrobenius A p f),
      mul_comm (iterateFrobenius A p f α) (iterateFrobenius A p f α'), mul_assoc]
  inv_mem' α hα c c' := by
    simp only [Set.mem_ofPred_eq] at *
    by_cases h0 : α = 0
    · subst h0; simp
    have hf0 : iterateFrobenius A p f α ≠ 0 := (_root_.map_ne_zero _).mpr h0
    have := hα (α⁻¹ * c) (iterateFrobenius A p f α⁻¹ * c')
    rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ h0, map_one, one_mul] at this
    exact this.symm

theorem mem_formSubfield {β : A →+ A →+ Z₀} {α : A} :
    α ∈ formSubfield p f β ↔ ∀ c c', β (α * c) c' = β c (α ^ p ^ f * c') := Iff.rfl

end Form

section Counting

variable {A : Type*} [Field A] [Finite A]

omit [Finite A] in
theorem card_dvd_card_subfield_sub_one (S : Subfield A) (Ω : Subgroup Aˣ)
    (hle : ∀ ω ∈ Ω, (ω : A) ∈ S) : Nat.card Ω ∣ Nat.card S - 1 := by
  let u : Sˣ →* Aˣ := Units.map S.subtype.toMonoidHom
  have hu : Function.Injective u := by
    intro x y h
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val h
  have hle' : Ω ≤ u.range := by
    intro ω hω
    have h0 : (⟨(ω : A), hle ω hω⟩ : S) ≠ 0 := fun h => Units.ne_zero ω (congrArg Subtype.val h)
    exact ⟨Units.mk0 _ h0, Units.ext rfl⟩
  have h1 := Subgroup.card_dvd_of_le hle'
  rwa [Nat.card_congr (MonoidHom.ofInjective hu).toEquiv.symm, Nat.card_units] at h1

theorem exists_card_subfield_pow (S : Subfield A) : ∃ m, Nat.card S ^ m = Nat.card A := by
  have : Fintype A := Fintype.ofFinite A
  have : Fintype S := Fintype.ofFinite S
  refine ⟨Module.finrank S A, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := S) (V := A)]

theorem mem_of_card_subfield_eq (S : Subfield A) (h : Nat.card S = Nat.card A) (α : A) :
    α ∈ S := by
  obtain ⟨x, hx⟩ :=
    ((Nat.bijective_iff_injective_and_card (Subtype.val : S → A)).mpr
      ⟨Subtype.val_injective, h⟩).2 α
  exact hx ▸ x.2

end Counting

section Invariant

variable {A : Type*} [Field A] [Finite A] {Z₀ : Type*} [AddCommGroup Z₀]
  {p f : ℕ} [Fact p.Prime] [CharP A p]

theorem iterateFrobenius_iterateFrobenius (hA : Nat.card A = (p ^ f) ^ 2) (c : A) :
    iterateFrobenius A p f (iterateFrobenius A p f c) = c := by
  have : Fintype A := Fintype.ofFinite A
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← sq, ← hA,
    Nat.card_eq_fintype_card, FiniteField.pow_card]

omit [Finite A] in
theorem mem_formSubfield_of_mem {β : A →+ A →+ Z₀} {Ω : Subgroup Aˣ}
    (hΩ : Nat.card Ω * Nat.gcd (p ^ f + 1) 3 = p ^ f + 1)
    (hinv : ∀ ω ∈ Ω, ∀ c c', β ((ω : A) * c) ((ω : A) * c') = β c c') {ω : Aˣ} (hω : ω ∈ Ω) :
    (ω : A) ∈ formSubfield p f β := by
  have h1 : ω ^ (p ^ f + 1) = 1 := by
    have h2 : ω ^ Nat.card Ω = 1 := by
      have := pow_card_eq_one' (x := (⟨ω, hω⟩ : Ω))
      rw [Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one] at this
      exact this
    rw [← hΩ, pow_mul, h2, one_pow]
  have h3 : (ω : A) ^ p ^ f = (ω : A)⁻¹ := by
    have : (ω : A) ^ (p ^ f + 1) = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    rw [pow_succ] at this
    exact eq_inv_of_mul_eq_one_left this
  intro c c'
  rw [iterateFrobenius_def, h3]
  have := hinv ω hω c ((ω : A)⁻¹ * c')
  rwa [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero ω), one_mul] at this

theorem mem_formSubfield_of_card_eq_sq (hpodd : p ≠ 2) (hA : Nat.card A = p ^ 2)
    (β : A →+ A →+ Z₀) (halt : ∀ c, β c c = 0) (α : A) : α ∈ formSubfield p 1 β := by
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have hA' : Nat.card A = (p ^ 1) ^ 2 := by rw [pow_one]; exact hA
  set φ := iterateFrobenius A p 1 with hφ
  have hφφ : ∀ c, φ (φ c) = c := iterateFrobenius_iterateFrobenius hA'
  have h2 : (2 : A) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq A p]; exact hpodd)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : A, φ c₀ ≠ c₀ := by
    by_contra h
    push Not at h
    have hcard := card_pow_eq_mul_le p (by omega) (1 : A)
    have : Nat.card {c : A // c ^ p = 1 * c} = Nat.card A :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun c => by
        rw [one_mul]
        have := h c
        rwa [hφ, iterateFrobenius_def, pow_one] at this))
    rw [this, hA] at hcard
    nlinarith
  set θ := c₀ - φ c₀ with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc₀)
  have hφθ : φ θ = -θ := by rw [hθ, map_sub, hφφ, neg_sub]
  let ι : ZMod p →+* A := ZMod.castHom (dvd_refl p) A
  have hιφ : ∀ a, φ (ι a) = ι a := fun a => by
    rw [hφ, iterateFrobenius_def, pow_one, ← map_pow, ZMod.pow_card]
  have hιnat : ∀ a, ι a = (a.val : A) := fun a => by
    simp [ι, ZMod.castHom_apply, ZMod.natCast_val]
  have hθι : ∀ a, θ ≠ ι a := by
    intro a h
    have h1 : φ θ = θ := by rw [h, hιφ]
    rw [hφθ] at h1
    have : (2 : A) * θ = 0 := by linear_combination -h1
    exact hθ0 ((mul_eq_zero.mp this).resolve_left h2)
  have hrep : ∀ γ : A, ∃ a b : ZMod p, γ = ι a + ι b * θ := by
    let F : ZMod p × ZMod p → A := fun x => ι x.1 + ι x.2 * θ
    have hF : Function.Injective F := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      simp only [F] at h
      by_cases hb : b = b'
      · subst hb
        have : ι a = ι a' := by linear_combination h
        exact Prod.ext (ι.injective this) rfl
      · exfalso
        have hb' : ι b - ι b' ≠ 0 := by
          rw [← map_sub]
          exact (_root_.map_ne_zero ι).mpr (sub_ne_zero.mpr hb)
        apply hθι ((a' - a) / (b - b'))
        rw [map_div₀, map_sub, map_sub, eq_div_iff hb']
        linear_combination h
    have hcard : Nat.card (ZMod p × ZMod p) = Nat.card A := by
      rw [Nat.card_prod, Nat.card_zmod, hA, sq]
    intro γ
    obtain ⟨⟨a, b⟩, h⟩ := ((Nat.bijective_iff_injective_and_card F).mpr ⟨hF, hcard⟩).2 γ
    exact ⟨a, b, h.symm⟩
  have hrep' : ∀ γ : A, ∃ n m : ℕ, γ = n • (1 : A) + m • θ := by
    intro γ
    obtain ⟨a, b, h⟩ := hrep γ
    exact ⟨a.val, b.val, by rw [h, hιnat, hιnat, nsmul_one, nsmul_eq_mul]⟩
  obtain ⟨a₀, b₀, hab⟩ := hrep (θ * θ)
  have hb₀ : ι b₀ = 0 := by
    have h1 : φ (θ * θ) = θ * θ := by rw [map_mul, hφθ]; ring
    rw [hab, map_add, map_mul, hιφ, hιφ, hφθ] at h1
    have h3 : (2 : A) * θ * ι b₀ = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact ((mul_eq_zero.mp h4).elim h2 hθ0).elim
    · exact h4
  have hθθ : θ * θ = ((a₀.val : ℕ) : A) := by rw [hab, hb₀, zero_mul, add_zero, hιnat]
  have hanti := form_antisymm β halt
  have hR : ∀ (n : ℕ) (x : A), β x (n : A) = n • β x 1 := fun n x => by
    rw [← nsmul_one, map_nsmul]
  have hL : ∀ (n : ℕ) (x : A), β (n : A) x = n • β 1 x := fun n x => by
    rw [← nsmul_one, map_nsmul, AddMonoidHom.nsmul_apply]
  have C11 : formTwist β θ 1 1 = 0 := by
    rw [formTwist_apply, mul_one, hanti θ 1, neg_add_cancel]
  have C1θ : formTwist β θ 1 θ = 0 := by
    rw [formTwist_apply, mul_one, halt, hθθ, hR, halt, smul_zero, add_zero]
  have Cθ1 : formTwist β θ θ 1 = 0 := by
    rw [formTwist_apply, mul_one, hθθ, hL, halt, halt, smul_zero, add_zero]
  have Cθθ : formTwist β θ θ θ = 0 := by
    rw [formTwist_apply, hθθ, hL, hR, ← smul_add, hanti θ 1, add_neg_cancel, smul_zero]
  have hCall : ∀ x y : A, formTwist β θ x y = 0 := by
    intro x y
    obtain ⟨n, m, rfl⟩ := hrep' x
    obtain ⟨n', m', rfl⟩ := hrep' y
    simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, C11, C1θ,
      Cθ1, Cθθ, smul_zero, add_zero]
  have hθS : θ ∈ formSubfield p 1 β := by
    intro x y
    have := hCall x y
    rw [formTwist_apply] at this
    change β (θ * x) y = β x (φ θ * y)
    rw [hφθ, neg_mul, map_neg]
    exact eq_neg_of_add_eq_zero_left this
  obtain ⟨n, m, rfl⟩ := hrep' α
  exact add_mem (nsmul_mem (one_mem _) n) (nsmul_mem hθS m)

theorem form_eq_conj_mul (hpodd : p ≠ 2) (hf : 1 ≤ f) (hA : Nat.card A = (p ^ f) ^ 2)
    (β : A →+ A →+ Z₀) (halt : ∀ c, β c c = 0) (Ω : Subgroup Aˣ)
    (hΩ : Nat.card Ω * Nat.gcd (p ^ f + 1) 3 = p ^ f + 1)
    (hinv : ∀ ω ∈ Ω, ∀ c c', β ((ω : A) * c) ((ω : A) * c') = β c c') (c c' : A) :
    β c c' = β 1 (c ^ p ^ f * c') := by
  suffices h : c ∈ formSubfield p f β by
    have := h 1 c'
    rwa [mul_one, iterateFrobenius_def] at this
  have hq3 := three_le_prime_pow (Fact.out : p.Prime) hpodd hf
  obtain ⟨m, hm⟩ := exists_card_subfield_pow (formSubfield p f β)
  have hdvd := card_dvd_card_subfield_sub_one _ Ω (fun ω hω => mem_formSubfield_of_mem hΩ hinv hω)
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · rw [pow_zero, hA] at hm
      nlinarith
    · rw [pow_one] at hm
      exact mem_of_card_subfield_eq _ hm c
  · obtain ⟨-, rfl⟩ := eq_five_of_pow_eq_sq (Fact.out : p.Prime) hpodd hf (hm.trans hA) hm2 hΩ hdvd
    exact mem_formSubfield_of_card_eq_sq hpodd (by rw [hA, pow_one]) β halt c

end Invariant

end CFSG.UnitaryThreeRecognition.Heisenberg
