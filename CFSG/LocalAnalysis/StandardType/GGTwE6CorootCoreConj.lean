module

public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.StandardType.TwE6CorootCore

open Subgroup

section Conj

variable {G : Type*} [Group G] {C I : Subgroup G}

theorem exists_core_of_conj {c t : G} (hc : c ∈ I) (φ : C ≃* C)
    (hφ : ∀ x : C, (φ x : G) = c⁻¹ * x * c) {q : ℕ}
    (h : ∃ X D : Subgroup C, (centralizer ({c * t * c⁻¹} : Set G)).subgroupOf C = X ⊔ D ∧
      IsCyclic X ∧ Odd (Nat.card X) ∧ X ≤ centralizer (D : Set C) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ 7 ∣ Nat.card D ∧ q ^ 15 ∣ Nat.card D ∧
      ∀ s ∈ I, s * (c * t * c⁻¹) = c * t * c⁻¹ * s →
        (∀ d ∈ D, s * (d : G) = (d : G) * s) → s ∈ X.map C.subtype) :
    ∃ X D : Subgroup C, (centralizer ({t} : Set G)).subgroupOf C = X ⊔ D ∧
      IsCyclic X ∧ Odd (Nat.card X) ∧ X ≤ centralizer (D : Set C) ∧ CFSG.IsQuasisimple D ∧
      center D = ⊥ ∧ 7 ∣ Nat.card D ∧ q ^ 15 ∣ Nat.card D ∧
      ∀ s ∈ I, s * t = t * s →
        (∀ d ∈ D, s * (d : G) = (d : G) * s) → s ∈ X.map C.subtype := by
  obtain ⟨X, D, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hφs : ∀ x : C, (φ.symm x : G) = c * x * c⁻¹ := fun x => by
    have e := hφ (φ.symm x)
    rw [MulEquiv.apply_symm_apply] at e
    rw [e]
    group
  have hφ' : ∀ x : C, (φ.toMonoidHom x : G) = c⁻¹ * x * c := hφ
  have eD := equivMapOfInjective D φ.toMonoidHom φ.injective
  refine ⟨X.map φ.toMonoidHom, D.map φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, ← h1]
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hφs]
    constructor
    · intro hx
      calc c * (x : G) * c⁻¹ * (c * t * c⁻¹) = c * ((x : G) * t) * c⁻¹ := by group
        _ = c * (t * (x : G)) * c⁻¹ := by rw [hx]
        _ = c * t * c⁻¹ * (c * (x : G) * c⁻¹) := by group
    · intro hx
      calc (x : G) * t = c⁻¹ * (c * (x : G) * c⁻¹ * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹ * (c * (x : G) * c⁻¹)) * c := by rw [hx]
        _ = t * (x : G) := by group
  · have eX := equivMapOfInjective X φ.toMonoidHom φ.injective
    exact isCyclic_of_surjective eX eX.surjective
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h3
  · rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    have e := Subgroup.mem_centralizer_iff.1 (h4 hx) d hd
    rw [← map_mul, ← map_mul, e]
  · exact CFSG.IsQuasisimple.of_mulEquiv eD.symm h5
  · rw [← Subgroup.map_center_eq eD, h6, Subgroup.map_bot]
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h7
  · rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact h8
  · intro s hs hst hsD
    have hst' : c * s * c⁻¹ * (c * t * c⁻¹) = c * t * c⁻¹ * (c * s * c⁻¹) := by
      calc c * s * c⁻¹ * (c * t * c⁻¹) = c * (s * t) * c⁻¹ := by group
        _ = c * (t * s) * c⁻¹ := by rw [hst]
        _ = c * t * c⁻¹ * (c * s * c⁻¹) := by group
    have hsD' : ∀ d ∈ D, c * s * c⁻¹ * (d : G) = (d : G) * (c * s * c⁻¹) := by
      intro d hd
      have e := hsD _ (Subgroup.mem_map_of_mem φ.toMonoidHom hd)
      rw [hφ'] at e
      calc c * s * c⁻¹ * (d : G) = c * (s * (c⁻¹ * (d : G) * c)) * c⁻¹ := by group
        _ = c * (c⁻¹ * (d : G) * c * s) * c⁻¹ := by rw [e]
        _ = (d : G) * (c * s * c⁻¹) := by group
    obtain ⟨x, hx, hxs⟩ :=
      Subgroup.mem_map.1 (h9 _ (mul_mem (mul_mem hc hs) (inv_mem hc)) hst' hsD')
    refine Subgroup.mem_map.2 ⟨φ x, Subgroup.mem_map_of_mem φ.toMonoidHom hx, ?_⟩
    show (φ x : G) = s
    rw [hφ, show (x : G) = c * s * c⁻¹ from hxs]
    group

end Conj

theorem seven_and_pow_dvd_ordTwistedA_five {f : ℕ} (hf : 1 ≤ f) :
    7 ∣ CFSG.Open.ordTwistedA 5 (2 ^ f) ∧ (2 ^ f) ^ 15 ∣ CFSG.Open.ordTwistedA 5 (2 ^ f) := by
  have h7 : 7 ∣ CFSG.Open.ordTwistedA 5 (2 ^ f) := by
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [CFSG.Open.ordTwistedA]
    have hF : ∀ {i : ℕ}, 2 ≤ i → i ≤ 6 → Even i → (2 ^ f) ^ i - 1 ∣
        ∏ j ∈ Finset.Icc 2 (5 + 1), (((2 ^ f : ℕ) : ℤ) ^ j - (-1) ^ j).toNat := by
      intro i h2 h6 he
      rw [← CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq he]
      exact Finset.dvd_prod_of_mem (fun j => (((2 ^ f : ℕ) : ℤ) ^ j - (-1) ^ j).toNat)
        (Finset.mem_Icc.2 ⟨h2, h6⟩)
    refine Nat.dvd_div_of_mul_dvd (Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) (by decide)) ?_ ?_)
    · refine Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
        (Dvd.dvd.trans ?_ (hF le_rfl (by norm_num) (by decide)))) _
      exact ⟨2 ^ f - 1, by have h := Nat.sq_sub_sq (2 ^ f) 1; rwa [one_pow] at h⟩
    · refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (hF (by norm_num) le_rfl (by decide))) _
      rw [← pow_mul, mul_comm, pow_mul]
      exact (by decide : 7 ∣ 2 ^ 6 - 1).trans (Nat.sub_one_dvd_pow_sub_one _ _)
  obtain ⟨r, -, hr⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 5) (g := f) (by norm_num) hf).two
  refine ⟨h7, ?_⟩
  rw [hr, ← pow_mul, show 5 * (5 + 1) / 2 = 15 from rfl]
  exact dvd_mul_right _ _

end CFSG.StandardType.TwE6CorootCore

end
