module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped commutatorElement

private lemma exists_c_zpow {G : Type} [Group G] {H U : Subgroup G} {σ : G}
    (hUn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (hσH : σ ∈ H)
    {y : G} (_hyH : y ∈ H) (hyσ : y * σ * y⁻¹ * σ⁻¹ ∈ U) (k : ℤ) :
    ∃ c ∈ U, y * σ ^ k * y⁻¹ = c * σ ^ k := by
  induction k using Int.induction_on with
  | zero =>
    exact ⟨1, U.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc_mem, hc_eq⟩ := ih
    have hσnH : σ ^ (n : ℤ) ∈ H := H.zpow_mem hσH n
    have hc1_mem : y * σ * y⁻¹ * σ⁻¹ ∈ U := hyσ
    have h_conj_mem : σ ^ (n : ℤ) * (y * σ * y⁻¹ * σ⁻¹) * (σ ^ (n : ℤ))⁻¹ ∈ U :=
      hUn (σ ^ (n : ℤ)) hσnH _ hc1_mem
    refine ⟨c * (σ ^ (n : ℤ) * (y * σ * y⁻¹ * σ⁻¹) * (σ ^ (n : ℤ))⁻¹),
      U.mul_mem hc_mem h_conj_mem, ?_⟩
    calc
      y * σ ^ ((n : ℤ) + 1) * y⁻¹ = y * σ ^ (n : ℤ) * σ * y⁻¹ := by
        rw [zpow_add_one]; group
      _ = (y * σ ^ (n : ℤ) * y⁻¹) * (y * σ * y⁻¹) := by group
      _ = (c * σ ^ (n : ℤ)) * ((y * σ * y⁻¹ * σ⁻¹) * σ) := by
        rw [hc_eq]; group
      _ = c * (σ ^ (n : ℤ) * (y * σ * y⁻¹ * σ⁻¹) * (σ ^ (n : ℤ))⁻¹) *
            σ ^ ((n : ℤ) + 1) := by
        rw [zpow_add_one]
        group
  | pred n ih =>
    obtain ⟨c, hc_mem, hc_eq⟩ := ih
    have hσn1H : σ ^ (-(n : ℤ) - 1) ∈ H := H.zpow_mem hσH (-(n : ℤ) - 1)
    have hc1_inv_mem : (y * σ * y⁻¹ * σ⁻¹)⁻¹ ∈ U := U.inv_mem hyσ
    have h_conj_mem :
        σ ^ (-(n : ℤ) - 1) * (y * σ * y⁻¹ * σ⁻¹)⁻¹ * (σ ^ (-(n : ℤ) - 1))⁻¹ ∈ U :=
      hUn (σ ^ (-(n : ℤ) - 1)) hσn1H _ hc1_inv_mem
    refine ⟨c * (σ ^ (-(n : ℤ) - 1) * (y * σ * y⁻¹ * σ⁻¹)⁻¹ *
        (σ ^ (-(n : ℤ) - 1))⁻¹), U.mul_mem hc_mem h_conj_mem, ?_⟩
    calc
      y * σ ^ (-(n : ℤ) - 1) * y⁻¹ = y * σ ^ (-(n : ℤ)) * σ⁻¹ * y⁻¹ := by
        rw [show -(n : ℤ) - 1 = -(n : ℤ) + (-1) by ring, zpow_add, zpow_neg_one]
        group
      _ = (y * σ ^ (-(n : ℤ)) * y⁻¹) * (y * σ⁻¹ * y⁻¹) := by group
      _ = (c * σ ^ (-(n : ℤ))) * (σ⁻¹ * (y * σ * y⁻¹ * σ⁻¹)⁻¹) := by
        rw [hc_eq]
        rw [show y * σ⁻¹ * y⁻¹ = (y * σ * y⁻¹)⁻¹ by group]
        rw [show y * σ * y⁻¹ = (y * σ * y⁻¹ * σ⁻¹) * σ by group]
        rw [mul_inv_rev]
        group
      _ = c * (σ ^ (-(n : ℤ) - 1) * (y * σ * y⁻¹ * σ⁻¹)⁻¹ *
            (σ ^ (-(n : ℤ) - 1))⁻¹) * σ ^ (-(n : ℤ) - 1) := by
        have h1 : (σ ^ (-(n : ℤ) - 1))⁻¹ = σ ^ ((n : ℤ) + 1) := by
          rw [show -(n : ℤ) - 1 = -((n : ℤ) + 1) by ring, zpow_neg, inv_inv]
        have h2 : σ ^ (-(n : ℤ) - 1) = (σ ^ ((n : ℤ) + 1))⁻¹ := by
          rw [show -(n : ℤ) - 1 = -((n : ℤ) + 1) by ring, zpow_neg]
        have hσ : σ ^ (-(n : ℤ)) * σ⁻¹ = σ ^ (-(n : ℤ) - 1) := by
          rw [← zpow_neg_one, ← zpow_add]
          rfl
        rw [show c * σ ^ (-(n : ℤ)) * (σ⁻¹ * (y * σ * y⁻¹ * σ⁻¹)⁻¹) =
                 c * (σ ^ (-(n : ℤ)) * σ⁻¹) * (y * σ * y⁻¹ * σ⁻¹)⁻¹ by group]
        rw [hσ, h1, h2]
        group

theorem mem_normalizer_commutator_sup {G : Type} [Group G] {H U : Subgroup G} {t₀ σ : G}
    (hUn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (ht₀U : t₀ ∈ U)
    (ht₀H : ∀ h ∈ H, h * t₀ = t₀ * h)
    (hUU : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers t₀) (hσH : σ ∈ H)
    {x : G} (hxH : x ∈ H) (hxσ : x * σ * x⁻¹ * σ⁻¹ ∈ U) :
    x ∈ Subgroup.normalizer (modW U t₀ σ : Set G) := by
  have := ht₀U
  let W₀ : Subgroup G := ⁅U, Subgroup.zpowers σ⁆
  let Z : Subgroup G := Subgroup.zpowers t₀
  let W : Subgroup G := modW U t₀ σ
  have hconj_W : ∀ y ∈ H, y * σ * y⁻¹ * σ⁻¹ ∈ U →
      W ≤ W.comap (MulAut.conj y).toMonoidHom := by
    intro y hyH hyσ
    change W₀ ⊔ Z ≤ W.comap (MulAut.conj y).toMonoidHom
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro u hu w hw
      change y * ⁅u, w⁆ * y⁻¹ ∈ W
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [conjugate_commutatorElement]
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_c_zpow hUn hσH hyH hyσ k
      rw [hc_eq]
      let u' : G := y * u * y⁻¹
      let v : G := σ ^ k * u'⁻¹ * σ ^ (-k)
      change ⁅u', c * σ ^ k⁆ ∈ W
      have hu'_mem : u' ∈ U := hUn y hyH u hu
      have hv_mem : v ∈ U := by
        change σ ^ k * u'⁻¹ * σ ^ (-k) ∈ U
        have hσkH : σ ^ k ∈ H := H.zpow_mem hσH k
        have h_eq_neg : σ ^ (-k) = (σ ^ k)⁻¹ := by rw [zpow_neg]
        rw [h_eq_neg]
        exact hUn (σ ^ k) hσkH u'⁻¹ (U.inv_mem hu'_mem)
      have h_comm1 : ⁅u', σ ^ k⁆ ∈ W₀ :=
        Subgroup.commutator_mem_commutator hu'_mem (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
      have h_comm2 : ⁅v⁻¹, c⁆ ∈ Z := hUU v⁻¹ (U.inv_mem hv_mem) c hc_mem
      have h_eq_expr : ⁅u', c * σ ^ k⁆ = ⁅u', σ ^ k⁆ * ⁅v⁻¹, c⁆ := by
        simp only [commutatorElement_def, u', v]
        rw [zpow_neg]
        group
      rw [h_eq_expr]
      exact Subgroup.mul_mem_sup h_comm1 h_comm2
    · intro z hz
      change y * z * y⁻¹ ∈ W
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have h_comm : Commute y t₀ := ht₀H y hyH
      have h_eq : y * t₀ ^ k * y⁻¹ = t₀ ^ k := by
        have h := (h_comm.zpow_right k).eq
        rw [h, mul_inv_cancel_right]
      rw [h_eq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have hx_inv_H : x⁻¹ ∈ H := H.inv_mem hxH
  have hx_inv_sigma : x⁻¹ * σ * (x⁻¹)⁻¹ * σ⁻¹ ∈ U := by
    have h_eq : x⁻¹ * σ * (x⁻¹)⁻¹ * σ⁻¹ = x⁻¹ * ⁅x, σ⁆⁻¹ * x := by
      rw [commutatorElement_def]
      group
    rw [h_eq]
    simpa [commutatorElement_def] using hUn x⁻¹ hx_inv_H _ (U.inv_mem hxσ)
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact hconj_W x hxH hxσ hw
  · intro hw
    have h := hconj_W x⁻¹ hx_inv_H hx_inv_sigma hw
    rw [Subgroup.mem_comap] at h
    change (MulAut.conj x⁻¹) (x * w * x⁻¹) ∈ W at h
    rwa [MulAut.conj_apply, show x⁻¹ * (x * w * x⁻¹) * (x⁻¹)⁻¹ = w by group] at h

end CFSG.StandardType.FrameRoute.FS81

end
