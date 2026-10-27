module

public import CFSG.Quasithin.H13.Sp4SemilinearPower
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter
public import CFSG.Quasithin.H13.NQCatSymplecticFour

public section

namespace CFSG.Quasithin.H13.Sp4

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.Quasithin.H13.NQTerm CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjAut fieldAut fieldSp conjSp
  spSemilinearAutGroup statedSp_le_gsp conjAut_proj fieldAut_proj coe_fieldSp coe_conjSp)
open scoped Pointwise

section Abstract

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem forall_or_forall_of_mem_union (β : A →* A) {H X Y : Subgroup A}
    (h : ∀ a ∈ H, β a ∈ X ∨ β a ∈ Y) : (∀ a ∈ H, β a ∈ X) ∨ (∀ a ∈ H, β a ∈ Y) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨x, hx, hxX⟩, ⟨y, hy, hyY⟩⟩ := hc
  have hxY : β x ∈ Y := (h x hx).resolve_left hxX
  have hyX : β y ∈ X := (h y hy).resolve_right hyY
  rcases h (x * y) (mul_mem hx hy) with hxy | hxy
  · apply hxX
    have : β x = β (x * y) * (β y)⁻¹ := by rw [map_mul]; group
    rw [this]
    exact mul_mem hxy (inv_mem hyX)
  · apply hyY
    have : β y = (β x)⁻¹ * β (x * y) := by rw [map_mul]; group
    rw [this]
    exact mul_mem (inv_mem hxY) hxy

theorem exists_pow_of_eigenpair {k : Type*} [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ a : A, a ^ p = 1) (hnc : ¬ IsCyclic A) (δ : A →* (Fin 2 → kˣ))
    (hδ : Function.Injective δ) (φ : k ≃+* k) {e : ℕ} (hφ : ∀ x, φ x = x ^ e) (β : A →* A)
    (hβ : Function.Injective β) {n : ℕ} (hn : Odd n) (hβn : ∀ a, β^[n] a = a)
    (hrel : ∀ (a : A) (μ : k),
      (μ = δ a 0 ∨ μ = δ a 1 ∨ μ = ((δ a 0 : kˣ) : k)⁻¹ ∨ μ = ((δ a 1 : kˣ) : k)⁻¹) ↔
        (φ μ = δ (β a) 0 ∨ φ μ = δ (β a) 1 ∨ φ μ = ((δ (β a) 0 : kˣ) : k)⁻¹ ∨
          φ μ = ((δ (β a) 1 : kˣ) : k)⁻¹)) :
    ∃ m : ℕ, ∀ a, β a = a ^ m := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => hδ (by rw [map_mul, map_mul, mul_comm])
  set χ₀ : A →* kˣ := (Pi.evalMonoidHom (fun _ : Fin 2 => kˣ) 0).comp δ with hχ₀
  set χ₁ : A →* kˣ := (Pi.evalMonoidHom (fun _ : Fin 2 => kˣ) 1).comp δ with hχ₁
  have hδ0 : ∀ a, δ a 0 = χ₀ a := fun _ => rfl
  have hδ1 : ∀ a, δ a 1 = χ₁ a := fun _ => rfl
  simp only [hδ0, hδ1] at hrel
  set A₀ := χ₁.ker with hA₀
  set A₁ := χ₀.ker with hA₁
  have hχ : ∀ a, χ₀ a = 1 → χ₁ a = 1 → a = 1 := fun a h0 h1 => hδ (by
    rw [map_one]
    funext j
    fin_cases j
    · exact h0
    · exact h1)
  have hA01 : ∀ a, a ∈ A₀ → a ∈ A₁ → a = 1 := fun a h0 h1 =>
    hχ a (MonoidHom.mem_ker.mp h1) (MonoidHom.mem_ker.mp h0)
  have hrange : ∀ χ : A →* kˣ, Nat.card χ.range ≤ p := by
    intro χ
    have hexpR : Monoid.exponent χ.range ∣ p := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      simp [← map_pow, hexp a]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos hexpR
  have hAp : IsPGroup p A := IsPGroup.iff_orderOf.mpr fun a => by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hexp a)) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨m, hm⟩ := hAp.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    apply hnc
    interval_cases m
    · rw [pow_zero] at hm
      have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hm).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hm
      exact isCyclic_of_prime_card hm
  have hcardA : p ^ 2 ≤ Nat.card A := by
    rw [hm]
    exact Nat.pow_le_pow_right hp.pos hm2
  have hcardle : Nat.card A ≤ p ^ 2 := by
    have hinj : Function.Injective fun a : A => (χ₀.rangeRestrict a, χ₁.rangeRestrict a) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      apply hδ
      funext j
      fin_cases j
      · exact congrArg Subtype.val hab.1
      · exact congrArg Subtype.val hab.2
    calc Nat.card A ≤ Nat.card (χ₀.range × χ₁.range) := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card χ₀.range * Nat.card χ₁.range := Nat.card_prod _ _
      _ ≤ p * p := Nat.mul_le_mul (hrange χ₀) (hrange χ₁)
      _ = p ^ 2 := (sq p).symm
  have haxis : ∀ χ : A →* kˣ, p ≤ Nat.card χ.ker := by
    intro χ
    have h1 := Subgroup.card_ker_mul_card_range χ
    have h2 := hrange χ
    have h3 : 0 < Nat.card χ.range := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card χ.ker * Nat.card χ.range < p * p :=
      calc Nat.card χ.ker * Nat.card χ.range < p * Nat.card χ.range :=
            Nat.mul_lt_mul_of_pos_right hlt h3
        _ ≤ p * p := Nat.mul_le_mul_left p h2
    rw [h1] at this
    nlinarith
  have hA₀ne : ∃ a ∈ A₀, a ≠ 1 := by
    by_contra hc
    push Not at hc
    have : A₀ = ⊥ := (eq_bot_iff_forall _).mpr hc
    have h : p ≤ Nat.card A₀ := haxis χ₁
    rw [this, card_bot] at h
    exact absurd h (by have := hp.two_le; omega)
  have hA₁ne : ∃ a ∈ A₁, a ≠ 1 := by
    by_contra hc
    push Not at hc
    have : A₁ = ⊥ := (eq_bot_iff_forall _).mpr hc
    have h : p ≤ Nat.card A₁ := haxis χ₀
    rw [this, card_bot] at h
    exact absurd h (by have := hp.two_le; omega)
  have hprod : ∀ a : A, ∃ a₀ ∈ A₀, ∃ a₁ ∈ A₁, a = a₀ * a₁ := by
    have hinj : Function.Injective fun x : A₀ × A₁ => (x.1 : A) * x.2 := by
      rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ hxy
      simp only at hxy
      have h1 : (y₀ : A)⁻¹ * x₀ = y₁ * (x₁ : A)⁻¹ := by
        calc (y₀ : A)⁻¹ * x₀ = (y₀ : A)⁻¹ * (x₀ * x₁) * (x₁ : A)⁻¹ := by group
          _ = y₁ * (x₁ : A)⁻¹ := by rw [hxy]; group
      have h2 : (y₀ : A)⁻¹ * x₀ = 1 := hA01 _ (mul_mem (inv_mem y₀.2) x₀.2)
        (h1 ▸ mul_mem y₁.2 (inv_mem x₁.2))
      have h3 : (x₀ : A) = y₀ := by
        calc (x₀ : A) = y₀ * ((y₀ : A)⁻¹ * x₀) := by group
          _ = y₀ := by rw [h2, mul_one]
      have h4 : (x₁ : A) = y₁ := by
        have := hxy
        rw [h3] at this
        exact mul_left_cancel this
      exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
    have hbij : Function.Bijective fun x : A₀ × A₁ => (x.1 : A) * x.2 := by
      refine hinj.bijective_of_nat_card_le ?_
      rw [Nat.card_prod]
      calc Nat.card A ≤ p ^ 2 := hcardle
        _ = p * p := sq p
        _ ≤ Nat.card A₀ * Nat.card A₁ := Nat.mul_le_mul (haxis χ₁) (haxis χ₀)
    intro a
    obtain ⟨⟨x₀, x₁⟩, hx⟩ := hbij.2 a
    exact ⟨x₀, x₀.2, x₁, x₁.2, hx.symm⟩
  have hval1 : ∀ u : kˣ, (u : k) = 1 ↔ u = 1 := fun u => Units.val_eq_one
  have hinv1 : ∀ u : kˣ, ((u : k))⁻¹ = 1 ↔ u = 1 := fun u => by rw [inv_eq_one, Units.val_eq_one]
  have hax0 : ∀ a ∈ A₀, β a ∈ A₀ ∨ β a ∈ A₁ := by
    intro a ha
    have h1 : χ₁ a = 1 := MonoidHom.mem_ker.mp ha
    have h2 := (hrel a 1).mp (Or.inr (Or.inl (by rw [h1, Units.val_one])))
    rw [map_one] at h2
    rcases h2 with h | h | h | h
    · exact Or.inr (MonoidHom.mem_ker.mpr ((hval1 _).mp h.symm))
    · exact Or.inl (MonoidHom.mem_ker.mpr ((hval1 _).mp h.symm))
    · exact Or.inr (MonoidHom.mem_ker.mpr ((hinv1 _).mp h.symm))
    · exact Or.inl (MonoidHom.mem_ker.mpr ((hinv1 _).mp h.symm))
  have hax1 : ∀ a ∈ A₁, β a ∈ A₀ ∨ β a ∈ A₁ := by
    intro a ha
    have h1 : χ₀ a = 1 := MonoidHom.mem_ker.mp ha
    have h2 := (hrel a 1).mp (Or.inl (by rw [h1, Units.val_one]))
    rw [map_one] at h2
    rcases h2 with h | h | h | h
    · exact Or.inr (MonoidHom.mem_ker.mpr ((hval1 _).mp h.symm))
    · exact Or.inl (MonoidHom.mem_ker.mpr ((hval1 _).mp h.symm))
    · exact Or.inr (MonoidHom.mem_ker.mpr ((hinv1 _).mp h.symm))
    · exact Or.inl (MonoidHom.mem_ker.mpr ((hinv1 _).mp h.symm))
  have hβs : Function.Surjective β := Finite.injective_iff_surjective.mp hβ
  have hall : ∀ X : Subgroup A, (∀ a ∈ A₀, β a ∈ X) → (∀ a ∈ A₁, β a ∈ X) → ∀ a, a ∈ X := by
    intro X h0 h1 a
    obtain ⟨b, rfl⟩ := hβs a
    obtain ⟨b₀, hb₀, b₁, hb₁, rfl⟩ := hprod b
    rw [map_mul]
    exact mul_mem (h0 b₀ hb₀) (h1 b₁ hb₁)
  have hsq : (∀ a ∈ A₀, β (β a) ∈ A₀) ∧ (∀ a ∈ A₁, β (β a) ∈ A₁) := by
    rcases forall_or_forall_of_mem_union β hax0 with h0 | h0 <;>
      rcases forall_or_forall_of_mem_union β hax1 with h1 | h1
    · exfalso
      obtain ⟨b, hb, hb1⟩ := hA₁ne
      exact hb1 (hA01 b (hall A₀ h0 h1 b) hb)
    · exact ⟨fun a ha => h0 _ (h0 a ha), fun a ha => h1 _ (h1 a ha)⟩
    · exact ⟨fun a ha => h1 _ (h0 a ha), fun a ha => h0 _ (h1 a ha)⟩
    · exfalso
      obtain ⟨b, hb, hb1⟩ := hA₀ne
      exact hb1 (hA01 b hb (hall A₁ h0 h1 b))
  have hinj0 : ∀ x ∈ A₀, ∀ y ∈ A₀, χ₀ x = χ₀ y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ = 1 := hA01 _ (mul_mem hx (inv_mem hy))
      (MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, mul_inv_cancel]))
    exact mul_inv_eq_one.mp h1
  have hinj1 : ∀ x ∈ A₁, ∀ y ∈ A₁, χ₁ x = χ₁ y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ = 1 := hA01 _ (MonoidHom.mem_ker.mpr
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])) (mul_mem hx (inv_mem hy))
    exact mul_inv_eq_one.mp h1
  have hφφ : ∀ x : k, φ (φ x) = x ^ (e * e) := fun x => by rw [hφ, hφ, ← pow_mul]
  have hrel2 : ∀ (a : A) (μ : k),
      (μ = χ₀ a ∨ μ = χ₁ a ∨ μ = ((χ₀ a : kˣ) : k)⁻¹ ∨ μ = ((χ₁ a : kˣ) : k)⁻¹) →
        (φ (φ μ) = χ₀ (β (β a)) ∨ φ (φ μ) = χ₁ (β (β a)) ∨
          φ (φ μ) = ((χ₀ (β (β a)) : kˣ) : k)⁻¹ ∨ φ (φ μ) = ((χ₁ (β (β a)) : kˣ) : k)⁻¹) :=
    fun a μ h => (hrel (β a) (φ μ)).mp ((hrel a μ).mp h)
  have hφne : ∀ u : kˣ, u ≠ 1 → φ (φ (u : k)) ≠ 1 := by
    intro u hu h
    apply hu
    have h1 : φ (φ (u : k)) = φ (φ 1) := by rw [h, map_one, map_one]
    exact (hval1 u).mp (φ.injective (φ.injective h1))
  have hsq0 : ∀ a ∈ A₀, β (β a) = a ^ (e * e) ∨ β (β a) = (a ^ (e * e))⁻¹ := by
    intro a ha
    by_cases ha1 : a = 1
    · left
      rw [ha1, map_one, map_one, one_pow]
    have hu : χ₀ a ≠ 1 := fun h => ha1 (hA01 a ha (MonoidHom.mem_ker.mpr h))
    have hb := hsq.1 a ha
    have hb1 : χ₁ (β (β a)) = 1 := MonoidHom.mem_ker.mp hb
    have h2 := hrel2 a (χ₀ a) (Or.inl rfl)
    rw [hb1, Units.val_one, inv_one] at h2
    have hne := hφne _ hu
    rcases h2 with h | h | h | h
    · left
      refine hinj0 _ hb _ (pow_mem ha _) (Units.ext ?_)
      rw [← h, hφφ, map_pow, Units.val_pow_eq_pow_val]
    · exact absurd h hne
    · right
      refine hinj0 _ hb _ (inv_mem (pow_mem ha _)) (Units.ext ?_)
      rw [map_inv, map_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← hφφ, h,
        inv_inv]
    · exact absurd h hne
  have hsq1 : ∀ a ∈ A₁, β (β a) = a ^ (e * e) ∨ β (β a) = (a ^ (e * e))⁻¹ := by
    intro a ha
    by_cases ha1 : a = 1
    · left
      rw [ha1, map_one, map_one, one_pow]
    have hu : χ₁ a ≠ 1 := fun h => ha1 (hA01 a (MonoidHom.mem_ker.mpr h) ha)
    have hb := hsq.2 a ha
    have hb1 : χ₀ (β (β a)) = 1 := MonoidHom.mem_ker.mp hb
    have h2 := hrel2 a (χ₁ a) (Or.inr (Or.inl rfl))
    rw [hb1, Units.val_one, inv_one] at h2
    have hne := hφne _ hu
    rcases h2 with h | h | h | h
    · exact absurd h hne
    · left
      refine hinj1 _ hb _ (pow_mem ha _) (Units.ext ?_)
      rw [← h, hφφ, map_pow, Units.val_pow_eq_pow_val]
    · exact absurd h hne
    · right
      refine hinj1 _ hb _ (inv_mem (pow_mem ha _)) (Units.ext ?_)
      rw [map_inv, map_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← hφφ, h,
        inv_inv]
  set E := (e * e) * (e * e) with hE
  have hfour_of : ∀ a, (β (β a) = a ^ (e * e) ∨ β (β a) = (a ^ (e * e))⁻¹) →
      β (β (β (β a))) = a ^ E := by
    intro a h
    rcases h with h | h
    · rw [h, map_pow, map_pow, h, ← pow_mul]
    · rw [h, map_inv, map_inv, map_pow, map_pow, h, inv_pow, inv_inv, ← pow_mul]
  have hfour : ∀ a, β^[4] a = a ^ E := by
    intro a
    obtain ⟨a₀, ha₀, a₁, ha₁, rfl⟩ := hprod a
    have e4 : ∀ x, β^[4] x = β (β (β (β x))) := fun _ => rfl
    rw [e4, map_mul, map_mul, map_mul, map_mul, hfour_of a₀ (hsq0 a₀ ha₀),
      hfour_of a₁ (hsq1 a₁ ha₁), (Commute.mul_pow (hcomm a₀ a₁) E)]
  have hfourt : ∀ t a, β^[4 * t] a = a ^ (E ^ t) := by
    intro t
    induction t with
    | zero => intro a; simp
    | succ t ih =>
      intro a
      rw [Nat.mul_succ, Function.iterate_add_apply, hfour, ih, ← pow_mul, ← pow_succ']
  have hfix : ∀ j a, (β^[n])^[j] a = a := fun j a => Function.iterate_fixed (hβn a) j
  obtain ⟨j, rfl⟩ := hn
  rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
  ·
    refine ⟨E ^ (3 * t + 1), fun a => ?_⟩
    have h1 : β^[4 * (3 * t + 1)] a = β (((β^[2 * j + 1])^[3]) a) := by
      rw [← Function.iterate_mul, show 4 * (3 * t + 1) = ((2 * j + 1) * 3).succ by omega,
        Function.iterate_succ_apply']
    rw [← hfourt, h1, hfix]
  ·
    refine ⟨E ^ (t + 1), fun a => ?_⟩
    have h1 : β^[4 * (t + 1)] a = β ((β^[2 * j + 1]) a) := by
      rw [show 4 * (t + 1) = (2 * j + 1).succ by omega, Function.iterate_succ_apply']
    rw [← hfourt, h1, hβn]

end Abstract

variable {k : Type} [Field k]

@[expose] def evSet (g : StatedSp 2 k) : Set k :=
  {μ | (((g : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) -
    μ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)).det = 0}

theorem evSet_conj (g h : StatedSp 2 k) : evSet (h * g * h⁻¹) = evSet g := by
  ext μ
  simp only [evSet, Set.mem_ofPred_eq]
  set H : GL (Fin 2 ⊕ Fin 2) k := (h : GL (Fin 2 ⊕ Fin 2) k) with hH
  have e1 : (((h * g * h⁻¹ : StatedSp 2 k) : GL (Fin 2 ⊕ Fin 2) k) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) -
        μ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) =
      (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) *
        ((((g : GL (Fin 2 ⊕ Fin 2) k)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) -
          μ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)) *
        ((H⁻¹ : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) := by
    have hHH : (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) *
        ((H⁻¹ : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
    simp [hH]
  rw [e1, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem mem_evSet_fieldSp (φ : k ≃+* k) (g : StatedSp 2 k) (μ : k) :
    φ μ ∈ evSet (fieldSp 2 k φ g) ↔ μ ∈ evSet g := by
  simp only [evSet, Set.mem_ofPred_eq, coe_fieldSp]
  have e1 : ((g : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k).map φ -
      φ μ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) =
      (φ : k →+* k).mapMatrix (((g : GL (Fin 2 ⊕ Fin 2) k) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) -
          μ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [e1, ← RingHom.map_det]
  exact map_eq_zero_iff (φ : k →+* k) φ.injective

theorem mem_evSet_of_mem_borel {b : StatedSp 2 k} (hb : b ∈ borelSubgroup 2 k) (μ : k) :
    μ ∈ evSet b ↔ μ = diagEntry b 0 ∨ μ = diagEntry b 1 ∨ μ = (diagEntry b 0)⁻¹ ∨
      μ = (diagEntry b 1)⁻¹ := by
  obtain ⟨A, C, hA, hdet, -, hbA⟩ := mem_borelSubgroup_iff.mp hb
  have hd : ∀ j, diagEntry b j = A j j := fun j => by
    rw [diagEntry, hbA, blockMat, Matrix.fromBlocks_apply₁₁]
  have hAi := isUpperTriangular_inv hA hdet
  have hinv : ∀ j, A⁻¹ j j = (A j j)⁻¹ := fun j =>
    (eq_inv_of_mul_eq_one_right (mul_inv_apply_self_of_isUpperTriangular hA hdet j))
  have hA10 : A 1 0 = 0 := hA (by decide)
  have hAi10 : A⁻¹ 1 0 = 0 := hAi (by decide)
  simp only [evSet, Set.mem_ofPred_eq, hbA, hd]
  have e1 : blockMat A C - μ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) =
      Matrix.fromBlocks (A - μ • 1) (A * C) 0 (A⁻¹ - μ • 1).transpose := by
    ext (i | i) (j | j) <;>
      simp [blockMat, Matrix.one_apply, Matrix.transpose_apply, Matrix.sub_apply, eq_comm]
  rw [e1, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, Matrix.det_fin_two,
    Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.one_apply_ne
      (show (0 : Fin 2) ≠ 1 by decide), mul_zero, sub_zero, hA10, hAi10, hinv]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h <;> rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h).symm
    · exact Or.inr (Or.inl (sub_eq_zero.mp h).symm)
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h).symm))
    · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h).symm))
  · rintro (h | h | h | h) <;> subst h <;> simp

theorem oddOrder_acts_by_pow {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (U : Sylow 2 (StatedProj (StatedSp 2 k)))
    (A : Subgroup (StatedProj (StatedSp 2 k))) (hAexp : ∀ a ∈ A, a ^ p = 1)
    (hAnc : ¬ IsCyclic A)
    (hAU : (A : Set (StatedProj (StatedSp 2 k))) * (U : Set (StatedProj (StatedSp 2 k))) =
      (U : Set (StatedProj (StatedSp 2 k))) * (A : Set (StatedProj (StatedSp 2 k))))
    {α : MulAut (StatedProj (StatedSp 2 k))} {n : ℕ} (hn : Odd n) (hαn : α ^ n = 1)
    (hαA : A.map α.toMonoidHom = A) :
    ∃ m : ℕ, ∀ a ∈ A, α a = a ^ m := by
  classical
  have hleaf := NQCat.evenSymplecticThreeFreeSylowOvergroupsTriangular
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1 hk
  have hAp : IsPGroup p A := IsPGroup.iff_orderOf.mpr fun a => by
    have ha : a ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hAexp a a.2)
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one ha) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨j, hj⟩ := hAp.exists_card_eq
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hAodd : Odd (Nat.card A) := by
    rw [hj]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hA3 : ¬ 3 ∣ Nat.card A := by
    rw [hj]
    intro h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hidx := CFSG.RankThree.PartOne.KCSpComm.index_spSemilinearAutGroup_two (K := k)
  have hαE : α ∈ spSemilinearAutGroup 2 k := by
    obtain ⟨t, ht⟩ := id hn
    have hsq : α * α ∈ spSemilinearAutGroup 2 k := Subgroup.mul_self_mem_of_index_two hidx α
    have h1 : α ^ (2 * t) * α ∈ spSemilinearAutGroup 2 k := by
      rw [← pow_succ, ← ht, hαn]
      exact one_mem _
    rw [pow_mul, sq] at h1
    exact (Subgroup.mul_mem_cancel_left _ (pow_mem hsq t)).mp h1
  obtain ⟨hbij, -, -, hnf, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
      (r := 2) (K := k) hf1 hk
  let π : StatedSp 2 k ≃* StatedProj (StatedSp 2 k) := MulEquiv.ofBijective (proj 2 k) hbij
  have hπ : π.toMonoidHom = proj 2 k := MonoidHom.ext fun _ => rfl
  have hdat₀ := NQCat.threeFreeBorelDatum_of_mulEquiv
    (NQCat.threeFreeBorelDatum_statedSp hleaf k) π
  set U₀ := (unipotent 2 k).map π.toMonoidHom with hU₀
  set B₀ := (borelSubgroup 2 k).map π.toMonoidHom with hB₀
  obtain ⟨-, -, -, -, -, -, ⟨P₀, hP₀⟩, -⟩ :=
    symplectic_higher_order_and_Sylow (K := k) 2 (Nat.card k) rfl (r := 2) (by norm_num)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 k)) P₀ U
  have hUc : (U : Subgroup (StatedProj (StatedSp 2 k))) =
      U₀.map (MulAut.conj c).toMonoidHom := by
    rw [← hc, coe_smul_sylow_eq_map, hP₀, hU₀, hπ]
    rfl
  have hdat := hdat₀.map (MulAut.conj c)
  rw [← hUc] at hdat
  obtain ⟨hAB, hAU', -, -⟩ := hdat.commute_of_permutable A hAodd hA3 hAU
  obtain ⟨⟨g, φ⟩, hαgφ, -⟩ := hnf α hαE
  obtain ⟨i, hi⟩ := exists_ringEquiv_eq_pow φ
  set γ := fieldAut 2 k φ with hγ
  have hα' : ∀ x, α x = proj 2 k g * γ x * (proj 2 k g)⁻¹ := fun x => by
    rw [hαgφ, MulAut.mul_apply, conjAut_apply_eq]
  have hγπ : ∀ y : StatedSp 2 k, γ (π y) = π (fieldSp 2 k φ y) := fun y => fieldAut_proj φ y
  set EV : StatedProj (StatedSp 2 k) → Set k := fun x => evSet (π.symm x) with hEV
  have hEVconj : ∀ x y, EV (y * x * y⁻¹) = EV x := fun x y => by
    simp only [hEV, map_mul, map_inv]
    exact evSet_conj _ _
  have hEVγ : ∀ x μ, φ μ ∈ EV (γ x) ↔ μ ∈ EV x := fun x μ => by
    have h1 : π.symm (γ x) = fieldSp 2 k φ (π.symm x) := by
      apply π.injective
      rw [MulEquiv.apply_symm_apply, ← hγπ, MulEquiv.apply_symm_apply]
    simp only [hEV, h1]
    exact mem_evSet_fieldSp φ _ μ
  have hEVα : ∀ x μ, φ μ ∈ EV (α x) ↔ μ ∈ EV x := fun x μ => by
    rw [hα', hEVconj]
    exact hEVγ x μ
  have hBmem : ∀ x ∈ B₀, π.symm x ∈ borelSubgroup 2 k := by
    rintro _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hb
  have hAB' : ∀ a ∈ A, c⁻¹ * a * c ∈ B₀ := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := hAB ha
    have hb' : c⁻¹ * a * c = b := by
      rw [← hba]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hb']
    exact hb
  let bA : A →* borelSubgroup 2 k :=
    { toFun := fun a => ⟨π.symm (c⁻¹ * a * c), hBmem _ (hAB' a a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change π.symm (c⁻¹ * ((a : StatedProj (StatedSp 2 k)) * b) * c) =
          π.symm (c⁻¹ * a * c) * π.symm (c⁻¹ * b * c)
        rw [← map_mul]
        congr 1
        group) }
  let δ : A →* (Fin 2 → kˣ) := (diagHom 2 k).comp bA
  have hδ : ∀ (a : A) (jj : Fin 2), ((δ a jj : kˣ) : k) = diagEntry (π.symm (c⁻¹ * a * c)) jj :=
    fun _ _ => rfl
  have hEVA : ∀ (a : A) (μ : k), μ ∈ EV a ↔
      (μ = δ a 0 ∨ μ = δ a 1 ∨ μ = ((δ a 0 : kˣ) : k)⁻¹ ∨ μ = ((δ a 1 : kˣ) : k)⁻¹) := by
    intro a μ
    have h1 : EV a = EV (c⁻¹ * a * c⁻¹⁻¹) := (hEVconj _ _).symm
    rw [inv_inv] at h1
    rw [h1, hδ, hδ]
    exact mem_evSet_of_mem_borel (hBmem _ (hAB' a a.2)) μ
  have hδinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : bA a ∈ (unipotent 2 k).subgroupOf (borelSubgroup 2 k) := by
      rw [← ker_diagHom]
      exact ha
    rw [mem_subgroupOf] at h1
    have h2 : c⁻¹ * (a : StatedProj (StatedSp 2 k)) * c ∈ U₀ :=
      ⟨_, h1, by rw [MulEquiv.coe_toMonoidHom]; exact MulEquiv.apply_symm_apply π _⟩
    have h3 : (a : StatedProj (StatedSp 2 k)) ∈ (U : Subgroup (StatedProj (StatedSp 2 k))) := by
      rw [hUc]
      refine ⟨_, h2, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h4 : (a : StatedProj (StatedSp 2 k)) ∈ A ⊓ (U : Subgroup _) := ⟨a.2, h3⟩
    rw [hAU', mem_bot] at h4
    exact Subtype.ext h4
  have hαmem : ∀ a ∈ A, α a ∈ A := fun a ha => by
    rw [← hαA]
    exact ⟨a, ha, rfl⟩
  let β : A →* A :=
    { toFun := fun a => ⟨α (a : StatedProj (StatedSp 2 k)), hαmem a a.2⟩
      map_one' := Subtype.ext (map_one α)
      map_mul' := fun a b => Subtype.ext (map_mul α (a : StatedProj (StatedSp 2 k)) b) }
  have hβv : ∀ a : A, ((β a : A) : StatedProj (StatedSp 2 k)) =
      α (a : StatedProj (StatedSp 2 k)) := fun _ => rfl
  have hβinj : Function.Injective β := fun a b hab =>
    Subtype.ext (α.injective (congrArg Subtype.val hab))
  have hβpow : ∀ (t : ℕ) (a : A), ((β^[t] a : A) : StatedProj (StatedSp 2 k)) =
      (α ^ t) (a : StatedProj (StatedSp 2 k)) := by
    intro t
    induction t with
    | zero => intro a; rfl
    | succ t ih =>
      intro a
      rw [Function.iterate_succ_apply', hβv, ih, pow_succ', MulAut.mul_apply]
  have hβn : ∀ a, β^[n] a = a := fun a => Subtype.ext (by rw [hβpow, hαn, MulAut.one_apply])
  have hrel : ∀ (a : A) (μ : k),
      (μ = δ a 0 ∨ μ = δ a 1 ∨ μ = ((δ a 0 : kˣ) : k)⁻¹ ∨ μ = ((δ a 1 : kˣ) : k)⁻¹) ↔
        (φ μ = δ (β a) 0 ∨ φ μ = δ (β a) 1 ∨ φ μ = ((δ (β a) 0 : kˣ) : k)⁻¹ ∨
          φ μ = ((δ (β a) 1 : kˣ) : k)⁻¹) := by
    intro a μ
    rw [← hEVA, ← hEVA, hβv, hEVα]
  have hexp : ∀ a : A, a ^ p = 1 := fun a =>
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hAexp a a.2)
  obtain ⟨m, hm⟩ := exists_pow_of_eigenpair hp hexp hAnc δ hδinj φ hi β hβinj hn hβn hrel
  exact ⟨m, fun a ha => by
    have := congrArg Subtype.val (hm ⟨a, ha⟩)
    rwa [hβv, SubgroupClass.coe_pow] at this⟩

end CFSG.Quasithin.H13.Sp4
