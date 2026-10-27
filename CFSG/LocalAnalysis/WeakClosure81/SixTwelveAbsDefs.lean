module

public import CFSG.RankThree.GF2n.Basic
public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {X : Type} [Group X]

@[expose] def conjSubgroupOrbit (Y T : Subgroup X) : Set (Subgroup X) :=
  {W | ∃ y ∈ Y, W = conjSubgroup y T}

structure Abs612 (T T₁ Z E : Subgroup X) : Prop where
  elem : IsElemAbelian 2 T
  elem₁ : IsElemAbelian 2 T₁
  ne_bot : T ≠ ⊥
  four_le : 4 ≤ Nat.card T
  card_eq : Nat.card T₁ = Nat.card T
  sup : T ⊔ T₁ = ⊤
  central : Z ≤ Subgroup.center X
  inf_Z : T ⊓ Z = ⊥
  inf_Z₁ : T₁ ⊓ Z = ⊥
  closed : ∀ x y : X, ∀ a ∈ conjSubgroup x T, a ≠ 1 → ∀ b ∈ conjSubgroup y T, b ≠ 1 →
    ⁅a, b⁆ ∈ Z → conjSubgroup x T = conjSubgroup y T
  closed₁ : ∀ x y : X, ∀ a ∈ conjSubgroup x T₁, a ≠ 1 → ∀ b ∈ conjSubgroup y T₁, b ≠ 1 →
    ⁅a, b⁆ ∈ Z → conjSubgroup x T₁ = conjSubgroup y T₁
  inf_normalizer : ∀ s ∈ T₁, s ∈ Subgroup.normalizer (T : Set X) → s = 1
  le_E₁ : T₁ ≤ E
  le_E : ∀ s ∈ T₁, s ≠ 1 → ∀ x : X, s ∈ Subgroup.normalizer (conjSubgroup x T : Set X) →
    conjSubgroup x T ≤ E
  comm_E : ∀ e ∈ E, ∀ e' ∈ E, ⁅e, e'⁆ ∈ Z
  mem_Z : ∀ e ∈ E, (∀ t ∈ T, e * t = t * e) → e ∈ Z

namespace Abs612

variable {T T₁ Z E : Subgroup X}

theorem ne_bot₁ (h : Abs612 T T₁ Z E) : T₁ ≠ ⊥ := by
  intro hbot
  have h1 := h.card_eq
  rw [hbot, Subgroup.card_bot] at h1
  have h2 := h.four_le
  omega

theorem elem_conj (h : Abs612 T T₁ Z E) (x : X) : IsElemAbelian 2 (conjSubgroup x T) :=
  IsElemAbelian.map h.elem (MulAut.conj x).toMonoidHom

theorem inf_Z_conj (h : Abs612 T T₁ Z E) (x : X) : conjSubgroup x T ⊓ Z = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwT, hwZ⟩ := Subgroup.mem_inf.1 hw
  have hcen := Subgroup.mem_center_iff.1 (h.central hwZ) x⁻¹
  have hxw : x⁻¹ * w * x = w := by
    rw [hcen, mul_assoc, inv_mul_cancel, mul_one]
  have hwT' : w ∈ T := by
    have h1 := mem_conjSubgroup.1 hwT
    rwa [hxw] at h1
  have h2 : w ∈ T ⊓ Z := Subgroup.mem_inf.2 ⟨hwT', hwZ⟩
  rw [h.inf_Z] at h2
  exact h2

theorem strongWC₁ (h : Abs612 T T₁ Z E) : StrongWC T₁ := by
  refine ⟨h.elem₁, fun t ht ht1 a ha g hg => ?_⟩
  by_cases hu1 : g⁻¹ * a * g = 1
  · rw [hu1]
    exact T₁.one_mem
  have hmem : g⁻¹ * a * g ∈ conjSubgroup g⁻¹ T₁ := by
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
    exact ha
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hcomm : ⁅g⁻¹ * a * g, t⁆ ∈ Z := by
    rw [(commutatorElement_eq_one_iff_mul_comm).2 hg]
    exact Z.one_mem
  have htT : t ∈ conjSubgroup 1 T₁ := by
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_one]
    exact ht
  have h1 := h.closed₁ g⁻¹ 1 _ hmem hu1 t htT ht1 hcomm
  rw [CFSG.CGT.Timmesfeld75.conjSubgroup_one] at h1
  rw [← h1]
  exact hmem

end Abs612

end CFSG.LocalAnalysis.WeakClosure81
