module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.NormNum.Basic

public section

namespace CFSG.StandardType

namespace D4Inner

variable {A : Type*} [CommGroup A] [Finite A]

omit [Finite A] in
abbrev sigmaSub (σ : A →* A) : A →* A := σ / MonoidHom.id A

omit [Finite A] in
theorem sigmaSub_apply (σ : A →* A) (a : A) : sigmaSub σ a = σ a * a⁻¹ := by
  rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv]

omit [Finite A] in
theorem sigmaSub_sigmaSub_apply (hA3 : ∀ a : A, a ^ 3 = 1) (σ : A →* A) (a : A) :
    sigmaSub σ (sigmaSub σ a) = a * σ a * σ (σ a) := by
  have h' : (σ a)⁻¹ = σ a * σ a := by rw [inv_eq_iff_mul_eq_one, ← hA3 (σ a), pow_three]
  calc sigmaSub σ (sigmaSub σ a) = σ (σ a) * (σ a)⁻¹ * (a * (σ a)⁻¹) := by
        rw [sigmaSub_apply, sigmaSub_apply, map_mul, map_inv, mul_inv_rev, inv_inv]
    _ = a * σ a * σ (σ a) * (σ a * (σ a * σ a)) := by rw [h']; ac_rfl
    _ = a * σ a * σ (σ a) := by rw [← pow_three, hA3, mul_one]

theorem le_card_sup (hcard : Nat.card A = 3 ^ 4) {D P : Subgroup A} (hD : Nat.card D = 3 ^ 2)
    (hP : Nat.card P = 3 ^ 2) (hDP : Nat.card ↥(D ⊓ P) = 3) : 3 ^ 3 ≤ Nat.card ↥(D ⊔ P) := by
  have h1 : Nat.card D ∣ Nat.card ↥(D ⊔ P) := Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card ↥(D ⊔ P) ∣ 3 ^ 4 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
  rw [hk', hD] at h1
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | h3
  · exfalso
    have hle : D ⊔ P ≤ D := (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk', hD])).ge
    have hPD : P ≤ D := le_sup_right.trans hle
    rw [inf_eq_right.2 hPD, hP] at hDP
    norm_num at hDP
  · rw [hk']; exact Nat.pow_le_pow_right (by norm_num) h3

theorem mem_sup_of_norm_eq_one (hA3 : ∀ a : A, a ^ 3 = 1) (hcard : Nat.card A = 3 ^ 4)
    (σ : A →* A) {D P : Subgroup A} (hD : Nat.card D = 3 ^ 2) (hP : Nat.card P = 3 ^ 2)
    (hDP : Nat.card ↥(D ⊓ P) = 3) (hDfix : ∀ d ∈ D, σ d = d)
    (hfix : ∀ E : Subgroup A, (∀ e ∈ E, σ e = e) → Nat.card E ≤ 3 ^ 2)
    (hδ : ∀ a, σ a * a⁻¹ ∈ P) (hPN : ∀ p ∈ P, p * σ p * σ (σ p) = 1)
    {u : A} (hu : u * σ u * σ (σ u) = 1) : u ∈ D ⊔ P := by
  set δ := sigmaSub σ with hδdef
  have hkerfix : ∀ e ∈ δ.ker, σ e = e := fun e he => by
    rw [MonoidHom.mem_ker, sigmaSub_apply, mul_inv_eq_one] at he; exact he
  have hDker : D ≤ δ.ker := fun d hd => by
    rw [MonoidHom.mem_ker, sigmaSub_apply, hDfix d hd, mul_inv_cancel]
  have hker : δ.ker = D :=
    (Subgroup.eq_of_le_of_card_ge hDker (by rw [hD]; exact hfix _ hkerfix)).symm
  have hrangeP : δ.range ≤ P := by
    rintro _ ⟨a, rfl⟩; rw [sigmaSub_apply]; exact hδ a
  have hcardrange : Nat.card δ.range = 3 ^ 2 := by
    have := Subgroup.card_ker_mul_card_range δ
    rw [hker, hD, hcard] at this
    omega
  have hrange : δ.range = P :=
    Subgroup.eq_of_le_of_card_ge hrangeP (by rw [hP, hcardrange])
  have hcardP : Nat.card (δ.comp P.subtype).range = 3 := by
    have h := Subgroup.card_ker_mul_card_range (δ.comp P.subtype)
    have hk : Nat.card (δ.comp P.subtype).ker = 3 := by
      rw [← MonoidHom.comap_ker, hker, ← hDP, ← Subgroup.subgroupOf_map_subtype,
        Subgroup.card_map_of_injective P.subtype_injective]
      rfl
    rw [hk, hP] at h
    omega
  have hcard2 : Nat.card (δ.comp δ).ker = 3 ^ 3 := by
    have h := Subgroup.card_ker_mul_card_range (δ.comp δ)
    have hr : (δ.comp δ).range = (δ.comp P.subtype).range := by
      rw [MonoidHom.range_comp, hrange, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr, hcardP, hcard] at h
    omega
  have hle : D ⊔ P ≤ (δ.comp δ).ker := by
    refine sup_le (fun d hd => ?_) (fun p hp => ?_)
    · have hd' : d ∈ δ.ker := hker.symm ▸ hd
      rw [MonoidHom.mem_ker] at hd'
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hd', map_one]
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hδdef, sigmaSub_sigmaSub_apply hA3]
      exact hPN p hp
  have heq : D ⊔ P = (δ.comp δ).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2]; exact le_card_sup hcard hD hP hDP)
  rw [heq, MonoidHom.mem_ker, MonoidHom.comp_apply, hδdef, sigmaSub_sigmaSub_apply hA3]
  exact hu

end D4Inner

end CFSG.StandardType

end
