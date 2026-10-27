module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher

namespace S35.B5

namespace GLY

open MulAction

variable {A : Type} [Group A] [Finite A]

def fixSub (P : Subgroup (MulAut A)) : Subgroup A where
  carrier := {a | ∀ σ ∈ P, σ a = a}
  mul_mem' := fun ha hb σ hσ => by simp [map_mul, ha σ hσ, hb σ hσ]
  one_mem' := fun σ _ => map_one σ
  inv_mem' := fun ha σ hσ => by simp [map_inv, ha σ hσ]

theorem card_modEq_fixSub (p : ℕ) [Fact p.Prime] (P : Subgroup (MulAut A)) (hP : IsPGroup p P)
    (S : Subgroup A) (hS : ∀ σ ∈ P, ∀ a ∈ S, σ a ∈ S) :
    Nat.card S ≡ Nat.card ↥(S ⊓ fixSub P) [MOD p] := by
  let T : SubMulAction P A := { carrier := S, smul_mem' := fun σ a ha => hS σ σ.2 a ha }
  have h := hP.card_modEq_card_fixedPoints ↥T
  have e : MulAction.fixedPoints P ↥T ≃ ↥(S ⊓ fixSub P) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, fun σ hσ => congrArg Subtype.val (x.2 ⟨σ, hσ⟩)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun σ => Subtype.ext (x.2.2 σ σ.2)⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e] at h
  have e2 : ↥T ≃ ↥S := Equiv.refl _
  rwa [Nat.card_congr e2] at h

def stabC (C : Subgroup A) : Subgroup (MulAut A) where
  carrier := {σ | ∀ a, σ a ∈ C ↔ a ∈ C}
  mul_mem' := fun {σ τ} hσ hτ a => by
    show σ (τ a) ∈ C ↔ a ∈ C
    rw [hσ, hτ]
  one_mem' := fun a => Iff.rfl
  inv_mem' := fun {σ} hσ a => by
    have := hσ (σ⁻¹ a)
    simpa using this.symm

theorem arith_aux (j d : ℕ) (hj : j ≤ 4) (hd : d ∣ 2 ^ j) (hm : d ≡ 2 ^ j [MOD 5])
    (h1 : d ≠ 1 ∨ j ≤ 3) : d = 2 ^ j := by
  have hle : d ≤ 2 ^ j := Nat.le_of_dvd (by positivity) hd
  interval_cases j <;> interval_cases d <;> simp_all [Nat.ModEq] 

theorem eq_one_of_pow_five (σ : MulAut A) (h5 : σ ^ 5 = 1) (hA : ∀ a : A, a * a = 1)
    (hcard : Nat.card A ≤ 16) (C : Subgroup A) (hC : σ ∈ stabC C) (hC1 : C ≠ ⊥)
    (hC2 : C ≠ ⊤) : σ = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup (MulAut A) := Subgroup.zpowers σ with hPdef
  have hP5 : IsPGroup 5 P := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    show (g : MulAut A) ^ 5 ^ 1 = 1
    rw [← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5, one_zpow]
  have hPle : P ≤ stabC C := (Subgroup.zpowers_le).mpr hC
  have hA2 : IsPGroup 2 A := fun a => ⟨1, by simpa [sq] using hA a⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hA2
  have hj4 : j ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hj ▸ Subgroup.card_subgroup_dvd_card C)
  have hij : i < j := by
    rcases hi.lt_or_eq with h | h
    · exact h
    · exact absurd ((Subgroup.card_eq_iff_eq_top C).mp (by rw [hCi, hj, h])) hC2
  have hmodC := card_modEq_fixSub 5 P hP5 C (fun τ hτ a ha => (hPle hτ a).mpr ha)
  have hdvdC := Subgroup.card_dvd_of_le (inf_le_left : C ⊓ fixSub P ≤ C)
  have hCfix : C ≤ fixSub P := by
    have h1 := arith_aux i _ (by omega) (hCi ▸ hdvdC) (hCi ▸ hmodC.symm) (Or.inr (by omega))
    have h2 : C ⊓ fixSub P = C := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hCi])
    exact h2 ▸ inf_le_right
  have hmodA := card_modEq_fixSub 5 P hP5 ⊤ (fun _ _ _ _ => trivial)
  have hdvdA := Subgroup.card_dvd_of_le (inf_le_left : (⊤ : Subgroup A) ⊓ fixSub P ≤ ⊤)
  have hTop : Nat.card (⊤ : Subgroup A) = 2 ^ j := by rw [Subgroup.card_top, hj]
  have hne : Nat.card ↥((⊤ : Subgroup A) ⊓ fixSub P) ≠ 1 := by
    intro h
    have := Subgroup.card_eq_one.mp h
    apply hC1
    rw [eq_bot_iff]
    intro a ha
    have : a ∈ (⊤ : Subgroup A) ⊓ fixSub P := ⟨trivial, hCfix ha⟩
    rwa [‹(⊤ : Subgroup A) ⊓ fixSub P = ⊥›] at this
  have h3 := arith_aux j _ hj4 (hTop ▸ hdvdA) (hTop ▸ hmodA.symm) (Or.inl hne)
  have h4 : (⊤ : Subgroup A) ⊓ fixSub P = ⊤ :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hTop])
  have h5' : ∀ a : A, σ a = a := fun a => by
    have : a ∈ (⊤ : Subgroup A) ⊓ fixSub P := h4.ge (Subgroup.mem_top a)
    exact this.2 σ (Subgroup.mem_zpowers σ)
  exact MulEquiv.ext h5'

theorem coprime_stabC (hA : ∀ a : A, a * a = 1) (hcard : Nat.card A ≤ 16) (C : Subgroup A)
    (hC1 : C ≠ ⊥) (hC2 : C ≠ ⊤) : Nat.Coprime 5 (Nat.card (stabC C)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := stabC C) 5 hdvd
  have h5 : ((x : MulAut A)) ^ 5 = 1 := by
    have : x ^ 5 = 1 := hx ▸ pow_orderOf_eq_one x
    simpa using congrArg Subtype.val this
  have h1 := eq_one_of_pow_five (x : MulAut A) h5 hA hcard C x.2 hC1 hC2
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  omega

theorem acts_trivial {L : Type} [Group L]
    (hhom5 : ∀ (F : Type) [Group F] [Finite F], Nat.Coprime 5 (Nat.card F) →
      ∀ φ : L →* F, φ = 1)
    (ρ : L →* MulAut A) (hA : ∀ a : A, a * a = 1) (hcard : Nat.card A ≤ 16)
    (K : Subgroup L) (hKn : K.Normal) (hK : ∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n = 1)
    (hk : ∃ k ∈ K, ρ k ≠ 1) : ρ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k0, hk0K, hk0⟩ := hk
  have hKp : IsPGroup 2 K := fun g => by
    obtain ⟨n, hn⟩ := hK g g.2
    exact ⟨n, Subtype.ext hn⟩
  have hP2 : IsPGroup 2 (K.map ρ) := hKp.map ρ
  set C : Subgroup A := fixSub (K.map ρ) with hCdef
  have key : ∀ (l : L) b, b ∈ C → ρ l b ∈ C := by
    intro l b hb σ hσ
    obtain ⟨k, hkK, rfl⟩ := hσ
    have hk' : l⁻¹ * k * l ∈ K := by
      have := hKn.conj_mem k hkK l⁻¹
      simpa using this
    have h := hb (ρ (l⁻¹ * k * l)) ⟨_, hk', rfl⟩
    have h2 : (ρ l⁻¹) ((ρ k) ((ρ l) b)) = b := by
      simpa [map_mul] using h
    have h3 := congrArg (ρ l) h2
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h3
    simpa using h3
  have hCstab : ∀ l : L, ρ l ∈ stabC C := by
    intro l a
    refine ⟨fun h => ?_, key l a⟩
    have := key l⁻¹ _ h
    simpa [← MulAut.mul_apply, ← map_mul] using this
  have hCtop : C ≠ ⊤ := by
    intro h
    apply hk0
    refine MulEquiv.ext fun a => ?_
    have : a ∈ C := h ▸ Subgroup.mem_top a
    exact this (ρ k0) ⟨k0, hk0K, rfl⟩
  have hnt : ∃ a : A, ρ k0 a ≠ a := by
    by_contra hcon
    exact hk0 (MulEquiv.ext fun a => by by_contra h; exact hcon ⟨a, h⟩)
  have hCbot : C ≠ ⊥ := by
    intro hb
    obtain ⟨a, ha⟩ := hnt
    have hA2 : IsPGroup 2 A := fun a => ⟨1, by simpa [sq] using hA a⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hA2
    have hmod := card_modEq_fixSub 2 (K.map ρ) hP2 ⊤ (fun _ _ _ _ => trivial)
    have h1 : Nat.card ↥((⊤ : Subgroup A) ⊓ C) = 1 := by
      simp [hb]
    have hTop : Nat.card (⊤ : Subgroup A) = 2 ^ j := by rw [Subgroup.card_top, hj]
    rw [h1, hTop] at hmod
    have hj0 : j ≠ 0 := by
      rintro rfl
      have : Nat.card A = 1 := by simpa using hj
      have := (Nat.card_eq_one_iff_unique.mp this).1
      exact ha (Subsingleton.elim (α := A) _ _)
    have h2 : 2 ∣ 2 ^ j := dvd_pow_self 2 hj0
    unfold Nat.ModEq at hmod
    generalize 2 ^ j = m at h2 hmod
    omega
  have hcop := coprime_stabC hA hcard C hCbot hCtop
  have hho := hhom5 (stabC C) hcop (ρ.codRestrict (stabC C) hCstab)
  refine MonoidHom.ext fun l => ?_
  have := congrArg (fun φ => (φ l : MulAut A)) hho
  simpa using this

end GLY

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
