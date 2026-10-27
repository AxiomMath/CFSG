module

public import CFSG.RankThree.GF2n.Parrott.CaseIIF1Data

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

private theorem mem_commutator_centralizer_of_commute {G : Type*} [Group G] {z y p q : G}
    (hpz : p * z = z * p) (hpy : p * y = y * p)
    (hqz : q * z = z * q) (hqy : q * y = y * q)
    (hpq : p * q * p⁻¹ * q⁻¹ = z) :
    z ∈ ⁅centralizer ({z} : Set G) ⊓ centralizer {y},
      centralizer ({z} : Set G) ⊓ centralizer {y}⁆ := by
  have hp : p ∈ centralizer ({z} : Set G) ⊓ centralizer {y} :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hpz,
        Subgroup.mem_centralizer_singleton_iff.mpr hpy⟩
  have hq : q ∈ centralizer ({z} : Set G) ⊓ centralizer {y} :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hqz,
        Subgroup.mem_centralizer_singleton_iff.mpr hqy⟩
  have hmem : ⁅p, q⁆ ∈ ⁅centralizer ({z} : Set G) ⊓ centralizer {y},
      centralizer ({z} : Set G) ⊓ centralizer {y}⁆ :=
    Subgroup.commutator_mem_commutator hp hq
  rwa [commutatorElement_def, hpq] at hmem

private theorem commute_of_conj_eq {G : Type*} [Group G] {y j : G}
    (h : y * j * y⁻¹ = j) : j * y = y * j := by
  calc j * y = (y * j * y⁻¹) * y := by rw [h]
    _ = y * j := by group

private theorem mul_twist_commute {G : Type*} [Group G] {y z j k : G}
    (hzz : z * z = 1) (hzj : j * z = z * j) (hzk : z * k = k * z)
    (hyj : y * j * y⁻¹ = j * z) (hyk : y * k * y⁻¹ = k * z) :
    (j * k) * y = y * (j * k) ∧ (j * k) * z = z * (j * k) := by
  have hconj : y * (j * k) * y⁻¹ = j * k := by
    calc y * (j * k) * y⁻¹ = (y * j * y⁻¹) * (y * k * y⁻¹) := by group
      _ = (j * z) * (k * z) := by rw [hyj, hyk]
      _ = j * (z * k) * z := by group
      _ = j * (k * z) * z := by rw [hzk]
      _ = j * k * (z * z) := by group
      _ = j * k := by rw [hzz, mul_one]
  have hz : (j * k) * z = z * (j * k) := by
    calc (j * k) * z = j * (k * z) := by group
      _ = j * (z * k) := by rw [← hzk]
      _ = (j * z) * k := by group
      _ = (z * j) * k := by rw [hzj]
      _ = z * (j * k) := by group
  refine ⟨?_, hz⟩
  calc (j * k) * y = (y * (j * k) * y⁻¹) * y := by rw [hconj]
    _ = y * (j * k) := by group

private theorem commutatorElement_mul_left_of_commute {G : Type*} [Group G] {a b k : G}
    (hb : b * k = k * b) : ⁅a * k, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc (a * k) * b * (a * k)⁻¹ * b⁻¹
      = a * (k * b) * k⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * k) * k⁻¹ * a⁻¹ * b⁻¹ := by rw [← hb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutatorElement_mul_right_of_commute {G : Type*} [Group G] {a b k : G}
    (ha : a * k = k * a) : ⁅a, b * k⁆ = ⁅a, b⁆ := by
  have hak : k * a⁻¹ = a⁻¹ * k := by
    have h1 : a * k * a⁻¹ = k := by rw [ha, mul_inv_cancel_right]
    calc k * a⁻¹ = (a⁻¹ * a) * k * a⁻¹ := by group
      _ = a⁻¹ * (a * k * a⁻¹) := by group
      _ = a⁻¹ * k := by rw [h1]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * k) * a⁻¹ * (b * k)⁻¹
      = a * b * (k * a⁻¹) * k⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * k) * k⁻¹ * b⁻¹ := by rw [hak]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {a b k : G}
    (ha : a * k = k * a) (hb : b * k = k * b) : ⁅a * k, b * k⁆ = ⁅a, b⁆ := by
  have hbk : (b * k) * k = k * (b * k) := by
    calc (b * k) * k = (k * b) * k := by rw [hb]
      _ = k * (b * k) := by group
  calc ⁅a * k, b * k⁆ = ⁅a, b * k⁆ := commutatorElement_mul_left_of_commute hbk
    _ = ⁅a, b⁆ := commutatorElement_mul_right_of_commute ha

private theorem mem_commutator_of_twist {G : Type*} [Group G] {z y j₁ j₂ k : G}
    (hzz : z * z = 1)
    (hz₁ : j₁ * z = z * j₁) (hz₂ : j₂ * z = z * j₂) (hzk : z * k = k * z)
    (hy₁ : y * j₁ * y⁻¹ = j₁ ∨ y * j₁ * y⁻¹ = j₁ * z)
    (hy₂ : y * j₂ * y⁻¹ = j₂ ∨ y * j₂ * y⁻¹ = j₂ * z)
    (hyk : y * k * y⁻¹ = k * z)
    (hk₁ : j₁ * k = k * j₁) (hk₂ : j₂ * k = k * j₂)
    (h₁₂ : j₁ * j₂ * j₁⁻¹ * j₂⁻¹ = z) :
    z ∈ ⁅centralizer ({z} : Set G) ⊓ centralizer {y},
      centralizer ({z} : Set G) ⊓ centralizer {y}⁆ := by
  rcases hy₁ with h1 | h1
  · rcases hy₂ with h2 | h2
    · exact mem_commutator_centralizer_of_commute hz₁ (commute_of_conj_eq h1) hz₂
        (commute_of_conj_eq h2) h₁₂
    · have hq := mul_twist_commute hzz hz₂ hzk h2 hyk
      have hpq : j₁ * (j₂ * k) * j₁⁻¹ * (j₂ * k)⁻¹ = z := by
        have e : ⁅j₁, j₂ * k⁆ = ⁅j₁, j₂⁆ :=
          commutatorElement_mul_right_of_commute (a := j₁) (b := j₂) (k := k) hk₁
        rw [commutatorElement_def] at e
        exact e.trans h₁₂
      exact mem_commutator_centralizer_of_commute hz₁ (commute_of_conj_eq h1) hq.2 hq.1 hpq
  · have hp := mul_twist_commute hzz hz₁ hzk h1 hyk
    rcases hy₂ with h2 | h2
    · have hpq : (j₁ * k) * j₂ * (j₁ * k)⁻¹ * j₂⁻¹ = z := by
        have e : ⁅j₁ * k, j₂⁆ = ⁅j₁, j₂⁆ :=
          commutatorElement_mul_left_of_commute (a := j₁) (b := j₂) (k := k) hk₂
        rw [commutatorElement_def] at e
        exact e.trans h₁₂
      exact mem_commutator_centralizer_of_commute hp.2 hp.1 hz₂ (commute_of_conj_eq h2) hpq
    · have hq := mul_twist_commute hzz hz₂ hzk h2 hyk
      have hpq : (j₁ * k) * (j₂ * k) * (j₁ * k)⁻¹ * (j₂ * k)⁻¹ = z := by
        have e : ⁅j₁ * k, j₂ * k⁆ = ⁅j₁, j₂⁆ :=
          commutatorElement_mul_mul_of_commute (a := j₁) (b := j₂) (k := k) hk₁ hk₂
        rw [commutatorElement_def] at e
        exact e.trans h₁₂
      exact mem_commutator_centralizer_of_commute hp.2 hp.1 hq.2 hq.1 hpq

theorem z_mem_commutator_centralizer_of_four {G : Type*} [Group G] {z y j₁ j₂ j₃ j₄ : G}
    (hzz : z * z = 1)
    (hz₁ : j₁ * z = z * j₁) (hz₂ : j₂ * z = z * j₂) (hz₃ : j₃ * z = z * j₃)
    (hz₄ : j₄ * z = z * j₄)
    (hy₁ : y * j₁ * y⁻¹ = j₁ ∨ y * j₁ * y⁻¹ = j₁ * z)
    (hy₂ : y * j₂ * y⁻¹ = j₂ ∨ y * j₂ * y⁻¹ = j₂ * z)
    (hy₃ : y * j₃ * y⁻¹ = j₃ ∨ y * j₃ * y⁻¹ = j₃ * z)
    (hy₄ : y * j₄ * y⁻¹ = j₄ ∨ y * j₄ * y⁻¹ = j₄ * z)
    (h₁₂ : j₁ * j₂ * j₁⁻¹ * j₂⁻¹ = z) (h₃₄ : j₃ * j₄ * j₃⁻¹ * j₄⁻¹ = z)
    (h₁₃ : j₁ * j₃ = j₃ * j₁) (h₁₄ : j₁ * j₄ = j₄ * j₁) (h₂₃ : j₂ * j₃ = j₃ * j₂)
    (h₂₄ : j₂ * j₄ = j₄ * j₂) :
    z ∈ ⁅centralizer ({z} : Set G) ⊓ centralizer {y},
      centralizer ({z} : Set G) ⊓ centralizer {y}⁆ := by
  rcases hy₃ with h3 | h3
  · rcases hy₄ with h4 | h4
    · exact mem_commutator_centralizer_of_commute hz₃ (commute_of_conj_eq h3) hz₄
        (commute_of_conj_eq h4) h₃₄
    · exact mem_commutator_of_twist hzz hz₁ hz₂ hz₄.symm hy₁ hy₂ h4 h₁₄ h₂₄ h₁₂
  · exact mem_commutator_of_twist hzz hz₁ hz₂ hz₃.symm hy₁ hy₂ h3 h₁₃ h₂₃ h₁₂

variable {G : Type} [Group G] [Finite G] {z : G}

theorem IsSpinCoord.z_mem_commutator_centralizer_of_fixed {ψ : ↥(H z) →* A45} {κ : G → V}
    (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1) {y : G} (hy : y ∈ H z) {u₁ u₂ u₃ u₄ : V}
    (hu₁ : ((rhoA (ψ ⟨y, hy⟩) : GL8) : Mat8) *ᵥ u₁ = u₁)
    (hu₂ : ((rhoA (ψ ⟨y, hy⟩) : GL8) : Mat8) *ᵥ u₂ = u₂)
    (hu₃ : ((rhoA (ψ ⟨y, hy⟩) : GL8) : Mat8) *ᵥ u₃ = u₃)
    (hu₄ : ((rhoA (ψ ⟨y, hy⟩) : GL8) : Mat8) *ᵥ u₄ = u₄)
    (h₁₂ : b u₁ u₂ ≠ 0) (h₃₄ : b u₃ u₄ ≠ 0) (h₁₃ : b u₁ u₃ = 0) (h₁₄ : b u₁ u₄ = 0)
    (h₂₃ : b u₂ u₃ = 0) (h₂₄ : b u₂ u₄ = 0) :
    z ∈ ⁅centralizer ({z} : Set G) ⊓ centralizer {y},
      centralizer ({z} : Set G) ⊓ centralizer {y}⁆ := by
  obtain ⟨j₁, hj₁, hκ₁⟩ := hκ.surj u₁
  obtain ⟨j₂, hj₂, hκ₂⟩ := hκ.surj u₂
  obtain ⟨j₃, hj₃, hκ₃⟩ := hκ.surj u₃
  obtain ⟨j₄, hj₄, hκ₄⟩ := hκ.surj u₄
  have hz : ∀ j ∈ J z, j * z = z * j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mp (J_le_H hj)
  have hf : ∀ j ∈ J z, ((rhoA (ψ ⟨y, hy⟩) : GL8) : Mat8) *ᵥ κ j = κ j →
      y * j * y⁻¹ = j ∨ y * j * y⁻¹ = j * z := by
    intro j hj hfix
    have hc : y * j * y⁻¹ ∈ J z :=
      (mem_normalizer_iff.mp ((normal_subgroupOf_iff_le_normalizer J_le_H).mp
        (J_subgroupOf_normal z) hy) j).mp hj
    refine (hκ.kappa_eq_iff hj hc).mp ?_
    rw [hκ.act y hy j hj, hfix]
  have hne : ∀ j ∈ J z, ∀ k ∈ J z, b (κ j) (κ k) ≠ 0 → j * k * j⁻¹ * k⁻¹ = z := by
    intro j hj k hk hb
    have h := hκ.comm j hj k hk
    rw [if_neg hb] at h
    exact h
  have hcomm : ∀ j ∈ J z, ∀ k ∈ J z, b (κ j) (κ k) = 0 → j * k = k * j := by
    intro j hj k hk hb
    have h := hκ.comm j hj k hk
    rw [if_pos hb] at h
    calc j * k = (j * k * j⁻¹ * k⁻¹) * (k * j) := by group
      _ = k * j := by rw [h, one_mul]
  exact z_mem_commutator_centralizer_of_four hzz (hz j₁ hj₁) (hz j₂ hj₂) (hz j₃ hj₃)
    (hz j₄ hj₄) (hf j₁ hj₁ (by rw [hκ₁]; exact hu₁)) (hf j₂ hj₂ (by rw [hκ₂]; exact hu₂))
    (hf j₃ hj₃ (by rw [hκ₃]; exact hu₃)) (hf j₄ hj₄ (by rw [hκ₄]; exact hu₄))
    (hne j₁ hj₁ j₂ hj₂ (by rw [hκ₁, hκ₂]; exact h₁₂))
    (hne j₃ hj₃ j₄ hj₄ (by rw [hκ₃, hκ₄]; exact h₃₄))
    (hcomm j₁ hj₁ j₃ hj₃ (by rw [hκ₁, hκ₃]; exact h₁₃))
    (hcomm j₁ hj₁ j₄ hj₄ (by rw [hκ₁, hκ₄]; exact h₁₄))
    (hcomm j₂ hj₂ j₃ hj₃ (by rw [hκ₂, hκ₃]; exact h₂₃))
    (hcomm j₂ hj₂ j₄ hj₄ (by rw [hκ₂, hκ₄]; exact h₂₄))

end CFSG.RankThree.GF2n.Parrott
