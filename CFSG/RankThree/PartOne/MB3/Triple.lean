module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly.RankThreeEven

variable {G : Type} [Group G]

structure Triple (K : Subgroup G) (x : G) : Prop where
  c01 : ∀ k ∈ K, ∀ k' ∈ conjBy x K, k * k' = k' * k
  c02 : ∀ k ∈ K, ∀ k' ∈ conjBy x (conjBy x K), k * k' = k' * k
  c12 : ∀ k ∈ conjBy x K, ∀ k' ∈ conjBy x (conjBy x K), k * k' = k' * k

theorem le_normalizer_of_commute {H N : Subgroup G} (h : ∀ g ∈ H, ∀ n ∈ N, g * n = n * g) :
    H ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
  Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun n hn => (h g hg n hn).symm)

theorem mem_normalizer_of_commute {g : G} {N : Subgroup G} (h : ∀ n ∈ N, g * n = n * g) :
    g ∈ Subgroup.normalizer (N : Set G) :=
  Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun n hn => (h n hn).symm)

theorem mem_normalizer_sup {g : G} {U V : Subgroup G} (hU : g ∈ Subgroup.normalizer (U : Set G))
    (hV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hU hV ⊢
  rw [Subgroup.map_sup, hU, hV]

@[expose] def U₃ (U : Subgroup G) (x : G) : Subgroup G :=
  U ⊔ conjBy x U ⊔ conjBy x (conjBy x U)

theorem U₃_ne_bot {U : Subgroup G} {x : G} (hU0 : U ≠ ⊥) : U₃ U x ≠ ⊥ := fun h => hU0 (by
  rw [eq_bot_iff]
  calc U ≤ U₃ U x := le_sup_left.trans le_sup_left
    _ = ⊥ := h
    _ ≤ ⊥ := le_rfl)

namespace Triple

variable {K : Subgroup G} {x : G} (T : Triple K x) {U : Subgroup G} (hUK : U ≤ K)

include T hUK

theorem U₃_comm01 : ∀ u ∈ U, ∀ v ∈ conjBy x U, u * v = v * u := fun u hu v hv =>
  T.c01 u (hUK hu) v (Subgroup.map_mono hUK hv)

theorem U₃_comm02 : ∀ u ∈ U, ∀ v ∈ conjBy x (conjBy x U), u * v = v * u := fun u hu v hv =>
  T.c02 u (hUK hu) v (Subgroup.map_mono (Subgroup.map_mono hUK) hv)

theorem U₃_comm12 : ∀ u ∈ conjBy x U, ∀ v ∈ conjBy x (conjBy x U), u * v = v * u :=
  fun u hu v hv => T.c12 u (Subgroup.map_mono hUK hu) v (Subgroup.map_mono
    (Subgroup.map_mono hUK) hv)

theorem isPGroup_U₃ (hU2 : IsPGroup 2 U) : IsPGroup 2 (U₃ U x) := by
  have hU1 : IsPGroup 2 (conjBy x U) := hU2.map _
  have hU2' : IsPGroup 2 (conjBy x (conjBy x U)) := hU1.map _
  have h1 : IsPGroup 2 (U ⊔ conjBy x U : Subgroup G) :=
    hU2.to_sup_of_normal_right' hU1 (le_normalizer_of_commute (T.U₃_comm01 hUK))
  refine h1.to_sup_of_normal_right' hU2' ?_
  refine (sup_le ?_ ?_ : U ⊔ conjBy x U ≤ Subgroup.centralizer
    ((conjBy x (conjBy x U) : Subgroup G) : Set G)).trans (Subgroup.centralizer_le_normalizer _)
  · exact fun g hg => Subgroup.mem_centralizer_iff.mpr fun n hn =>
      (T.U₃_comm02 hUK g hg n hn).symm
  · exact fun g hg => Subgroup.mem_centralizer_iff.mpr fun n hn =>
      (T.U₃_comm12 hUK g hg n hn).symm

end Triple

theorem mem_normalizer_U₃ {x g : G} {U : Subgroup G}
    (h₀ : g ∈ Subgroup.normalizer (U : Set G))
    (h₁ : g ∈ Subgroup.normalizer ((conjBy x U : Subgroup G) : Set G))
    (h₂ : g ∈ Subgroup.normalizer ((conjBy x (conjBy x U) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((U₃ U x : Subgroup G) : Set G) :=
  mem_normalizer_sup (mem_normalizer_sup h₀ h₁) h₂

theorem central_of_prod_eq_one {K₀ K₁ K₂ : Subgroup G} {y₀ y₁ y₂ w : G}
    (c01 : ∀ k ∈ K₀, ∀ k' ∈ K₁, k * k' = k' * k)
    (c02 : ∀ k ∈ K₀, ∀ k' ∈ K₂, k * k' = k' * k)
    (c12 : ∀ k ∈ K₁, ∀ k' ∈ K₂, k * k' = k' * k)
    (hy₀ : y₀ ∈ K₀) (hy₁ : y₁ ∈ K₁) (hy₂ : y₂ ∈ K₂)
    (hw₀ : ∀ k ∈ K₀, w * k = k * w) (hw₁ : ∀ k ∈ K₁, w * k = k * w)
    (hw₂ : ∀ k ∈ K₂, w * k = k * w) (h : y₀ * y₁ * y₂ * w = 1) :
    (∀ k ∈ K₀, y₀ * k = k * y₀) ∧ (∀ k ∈ K₁, y₁ * k = k * y₁) ∧
      (∀ k ∈ K₂, y₂ * k = k * y₂) := by
  have h01 : Commute y₀ y₁ := c01 y₀ hy₀ y₁ hy₁
  have h02 : Commute y₀ y₂ := c02 y₀ hy₀ y₂ hy₂
  have h12 : Commute y₁ y₂ := c12 y₁ hy₁ y₂ hy₂
  have e0 : y₀ = (y₁ * y₂ * w)⁻¹ := eq_inv_of_mul_eq_one_left (by
    rw [← h]
    simp only [mul_assoc])
  have e1 : y₁ = (y₀ * y₂ * w)⁻¹ := eq_inv_of_mul_eq_one_left (by
    calc y₁ * (y₀ * y₂ * w) = (y₁ * y₀) * y₂ * w := by simp only [mul_assoc]
      _ = (y₀ * y₁) * y₂ * w := by rw [h01.symm.eq]
      _ = 1 := h)
  have e2 : y₂ = (y₀ * y₁ * w)⁻¹ := eq_inv_of_mul_eq_one_left (by
    have hc : Commute y₂ (y₀ * y₁) := h02.symm.mul_right h12.symm
    calc y₂ * (y₀ * y₁ * w) = (y₂ * (y₀ * y₁)) * w := by simp only [mul_assoc]
      _ = ((y₀ * y₁) * y₂) * w := by rw [hc.eq]
      _ = 1 := h)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have a1 : Commute y₁ k := (c01 k hk y₁ hy₁).symm
    have a2 : Commute y₂ k := (c02 k hk y₂ hy₂).symm
    have hc : Commute (y₁ * y₂ * w) k := (a1.mul_left a2).mul_left (hw₀ k hk : Commute w k)
    rw [e0]
    exact hc.inv_left.eq
  · have a1 : Commute y₀ k := c01 y₀ hy₀ k hk
    have a2 : Commute y₂ k := (c12 k hk y₂ hy₂).symm
    have hc : Commute (y₀ * y₂ * w) k := (a1.mul_left a2).mul_left (hw₁ k hk : Commute w k)
    rw [e1]
    exact hc.inv_left.eq
  · have a1 : Commute y₀ k := c02 y₀ hy₀ k hk
    have a2 : Commute y₁ k := c12 y₁ hy₁ k hk
    have hc : Commute (y₀ * y₁ * w) k := (a1.mul_left a2).mul_left (hw₂ k hk : Commute w k)
    rw [e2]
    exact hc.inv_left.eq

end CFSG.RankThree.PartOne.MB3
