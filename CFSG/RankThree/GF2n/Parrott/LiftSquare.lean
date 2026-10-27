module

public import CFSG.GroupTheory.LiftSquareHalf
public import CFSG.RankThree.GF2n.Parrott.FixDim

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem H_conj_mem_J (g : ↥(H z)) {x : G} (hx : x ∈ J z) : (g : G) * x * (g : G)⁻¹ ∈ J z := by
  have h1 := (conjJ' z g ⟨x, hx⟩).2
  rwa [conjJ'_apply_coe] at h1

theorem conjV_pi_conj (h : Tim79a.ParrottHyp z) (g : ↥(H z)) {x : G} (hx : x ∈ J z) :
    conjV h g (QuotientV.pi z ⟨x, hx⟩) =
      QuotientV.pi z ⟨(g : G) * x * (g : G)⁻¹, H_conj_mem_J g hx⟩ := by
  rw [conjV_mk]
  congr 1

theorem pi_eq_one_iff_mem_centerIn {x : G} (hx : x ∈ J z) :
    QuotientV.pi z ⟨x, hx⟩ = 1 ↔ x ∈ centerIn (J z) := by
  rw [← MonoidHom.mem_ker, QuotientV.pi_ker, Subgroup.mem_subgroupOf]

theorem exists_conj_mul_centerIn_of_fixDimV_eq_four (h : Tim79a.ParrottHyp z) {y₁ y₂ : G}
    (hy₁ : y₁ ∈ H z) (hc : y₁⁻¹ * y₂ ∈ J z) (hdim : fixDimV h ⟨y₁, hy₁⟩ = 4)
    (h₁ : y₁ * y₁ ∈ centerIn (J z)) (h₂ : y₂ * y₂ ∈ centerIn (J z)) :
    ∃ k ∈ J z, ∃ e ∈ centerIn (J z), k * y₂ * k⁻¹ = y₁ * e := by
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  refine exists_conj_mul_mem_of_card_fix_sq (J := J z) (Z := centerIn (J z))
    (fun a ha b hb => commutator_mem_centerIn_J h ha hb) (fun j hj => sq_mem_centerIn_J h hj)
    (hHN hy₁) ((inf_le_left : centerIn (J z) ≤ J z) h₁)
    (σ := conjV h ⟨y₁, hy₁⟩) (fun j hj => conjV_pi_conj h ⟨y₁, hy₁⟩ hj) ?_
    (by simp) hc h₁ h₂
  rw [card_fix h ⟨y₁, hy₁⟩, hdim, QuotientV.card_V h]
  norm_num

theorem mul_self_eq_of_fixDimV_eq_four (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {y₁ y₂ : G} (hy₁ : y₁ ∈ H z)
    (hc : y₁⁻¹ * y₂ ∈ J z) (hdim : fixDimV h ⟨y₁, hy₁⟩ = 4)
    (h₁ : y₁ * y₁ ∈ centerIn (J z)) (h₂ : y₂ * y₂ ∈ centerIn (J z)) :
    y₁ * y₁ = y₂ * y₂ := by
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  refine mul_self_eq_of_card_fix_sq (J := J z) (Z := centerIn (J z))
    (fun c hc' j hj => Subgroup.mem_centralizer_iff.mp hc'.2 j hj)
    (fun c hc' => centerIn_J_sq h hc')
    (fun a ha b hb => commutator_mem_centerIn_J h ha hb) (fun j hj => sq_mem_centerIn_J h hj)
    (hHN hy₁) (fun c hc' => Subgroup.mem_centralizer_iff.mp (hZ ▸ hc').2 y₁ hy₁)
    ((inf_le_left : centerIn (J z) ≤ J z) h₁)
    (σ := conjV h ⟨y₁, hy₁⟩) (fun j hj => conjV_pi_conj h ⟨y₁, hy₁⟩ hj) ?_
    (by simp) hc h₁ h₂
  rw [card_fix h ⟨y₁, hy₁⟩, hdim, QuotientV.card_V h]
  norm_num

end CFSG.RankThree.GF2n.Parrott
