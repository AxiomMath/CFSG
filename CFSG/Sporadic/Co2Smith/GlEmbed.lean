module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
import Mathlib.Tactic.Group

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.ShultStronglyClosedTI.InvolutionCounting

section Fusion

variable {G : Type*} [Group G] {G' : Subgroup G}

theorem centralizer_conj_le {w h : G} (hh : h ∈ G')
    (hw : Subgroup.centralizer {w} ≤ G') : Subgroup.centralizer {h * w * h⁻¹} ≤ G' := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : h⁻¹ * c * h ∈ Subgroup.centralizer {w} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * c * h * w = h⁻¹ * (c * (h * w * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * w * h⁻¹) * c) * h := by rw [hc]
      _ = w * (h⁻¹ * c * h) := by group
  have hm := G'.mul_mem (G'.mul_mem hh (hw hc')) (G'.inv_mem hh)
  rwa [show h * (h⁻¹ * c * h) * h⁻¹ = c by group] at hm

theorem isConj_of_not_mem [Finite G]
    (hC : ∀ t ∈ G', orderOf t = 2 → Subgroup.centralizer {t} ≤ G') {a s : G} (ha : a ∈ G')
    (ha2 : orderOf a = 2) (hs2 : orderOf s = 2) (hs : s ∉ G') : IsConj a s := by
  have haa := mul_self_eq_one_of_orderOf_eq_two ha2
  have hss := mul_self_eq_one_of_orderOf_eq_two hs2
  by_contra hne
  obtain ⟨d, hd0, hd⟩ := exists_orderOf_mul_eq_two_mul haa hss hne
  have hx2 : orderOf ((a * s) ^ d) = 2 := orderOf_pow_half hd hd0
  have hxx := mul_self_eq_one_of_orderOf_eq_two hx2
  have hmem : (a * s) ^ d ∈ Subgroup.zpowers (a * s) := Subgroup.npow_mem_zpowers _ d
  have hax : Commute a ((a * s) ^ d) :=
    commute_of_mem_zpowers (conj_mul_left_eq_inv haa hss) hmem hxx
  have hsx : Commute s ((a * s) ^ d) :=
    commute_of_mem_zpowers (conj_mul_right_eq_inv haa hss) hmem hxx
  have hxG : (a * s) ^ d ∈ G' :=
    hC a ha ha2 (Subgroup.mem_centralizer_singleton_iff.2 hax.eq.symm)
  exact hs (hC _ hxG hx2 (Subgroup.mem_centralizer_singleton_iff.2 hsx.eq))

theorem mem_of_orderOf_eq_two [Finite G]
    (hC : ∀ t ∈ G', orderOf t = 2 → Subgroup.centralizer {t} ≤ G') {w₁ w₂ : G} (hw₁ : w₁ ∈ G')
    (hw₂ : w₂ ∈ G') (h₁ : orderOf w₁ = 2) (h₂ : orderOf w₂ = 2) (h₁₂ : ¬ IsConj w₁ w₂) {s : G}
    (hs : orderOf s = 2) : s ∈ G' := by
  by_contra hsG
  exact h₁₂ ((isConj_of_not_mem hC hw₁ h₁ hs hsG).trans
    (isConj_of_not_mem hC hw₂ h₂ hs hsG).symm)

theorem exists_conj_not_conj_of_ne_top {w : G} (hw : Subgroup.centralizer {w} ≤ G')
    (hG' : G' ≠ ⊤) : ∃ g : G, ∀ h ∈ G', h * w * h⁻¹ ≠ g * w * g⁻¹ := by
  by_contra hall
  push Not at hall
  refine hG' (eq_top_iff.2 fun g _ => ?_)
  obtain ⟨h, hh, e⟩ := hall g
  have hc : h⁻¹ * g ∈ Subgroup.centralizer {w} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * g * w = h⁻¹ * (g * w * g⁻¹) * g := by group
      _ = h⁻¹ * (h * w * h⁻¹) * g := by rw [e]
      _ = w * (h⁻¹ * g) := by group
  have hm := G'.mul_mem hh (hw hc)
  rwa [mul_inv_cancel_left] at hm

theorem eq_top_of_three_classes [Finite G] {w₁ w₂ w₃ : G} (h₁ : orderOf w₁ = 2)
    (h₂ : orderOf w₂ = 2) (h₁₂ : ¬ IsConj w₁ w₂) (hC₁ : Subgroup.centralizer {w₁} ≤ G')
    (hC₂ : Subgroup.centralizer {w₂} ≤ G') (hC₃ : Subgroup.centralizer {w₃} ≤ G')
    (hcls : ∀ t ∈ G', orderOf t = 2 →
      (∃ h ∈ G', h * w₁ * h⁻¹ = t) ∨ (∃ h ∈ G', h * w₂ * h⁻¹ = t) ∨
        ∃ h ∈ G', h * w₃ * h⁻¹ = t) : G' = ⊤ := by
  have hC : ∀ t ∈ G', orderOf t = 2 → Subgroup.centralizer {t} ≤ G' := by
    intro t ht ht2
    rcases hcls t ht ht2 with ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
    exacts [centralizer_conj_le hh hC₁, centralizer_conj_le hh hC₂, centralizer_conj_le hh hC₃]
  have hw₁ : w₁ ∈ G' := hC₁ (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hw₂ : w₂ ∈ G' := hC₂ (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hconj : ∀ {a b : G}, (∃ h ∈ G', h * a * h⁻¹ = b) → IsConj a b := fun ⟨h, _, e⟩ =>
    isConj_iff.2 ⟨h, e⟩
  by_contra hne
  have key : ∀ {w : G}, orderOf w = 2 → Subgroup.centralizer {w} ≤ G' →
      (∀ t ∈ G', IsConj w t → orderOf t = 2 → (∃ h ∈ G', h * w * h⁻¹ = t) ∨
        ∃ h ∈ G', h * w₃ * h⁻¹ = t) → IsConj w w₃ := by
    intro w hw2 hCw hcl
    obtain ⟨g, hg⟩ := exists_conj_not_conj_of_ne_top hCw hne
    have hwg : IsConj w (g * w * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
    have hg2 : orderOf (g * w * g⁻¹) = 2 := (orderOf_eq_of_isConj hwg).symm.trans hw2
    rcases hcl _ (mem_of_orderOf_eq_two hC hw₁ hw₂ h₁ h₂ h₁₂ hg2) hwg hg2 with
      ⟨h, hh, e⟩ | e
    · exact absurd e (hg h hh)
    · exact hwg.trans (hconj e).symm
  have k₁ : IsConj w₁ w₃ := key h₁ hC₁ fun t ht hct ht2 => by
    rcases hcls t ht ht2 with e | e | e
    · exact Or.inl e
    · exact absurd (hct.trans (hconj e).symm) h₁₂
    · exact Or.inr e
  have k₂ : IsConj w₂ w₃ := key h₂ hC₂ fun t ht hct ht2 => by
    rcases hcls t ht ht2 with e | e | e
    · exact absurd ((hconj e).trans hct.symm) h₁₂
    · exact Or.inl e
    · exact Or.inr e
  exact h₁₂ (k₁.trans k₂.symm)

end Fusion

section Centralizer

variable {G : Type*} [Group G] {G' : Subgroup G}

theorem centralizer_subgroup_eq (t : G') :
    Subgroup.centralizer ({t} : Set G') =
      (Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf G' := by
  ext c
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]

@[expose] def centralizerEquivOfLe {t : G'}
    (ht : Subgroup.centralizer ({(t : G)} : Set G) ≤ G') :
    Subgroup.centralizer ({t} : Set G') ≃* Subgroup.centralizer ({(t : G)} : Set G) :=
  (MulEquiv.subgroupCongr (centralizer_subgroup_eq t)).trans (Subgroup.subgroupOfEquivOfLe ht)

theorem centralizer_le_of_natCard_eq [Finite G] {t : G'}
    (h : Nat.card (Subgroup.centralizer ({t} : Set G')) =
      Nat.card (Subgroup.centralizer ({(t : G)} : Set G))) :
    Subgroup.centralizer ({(t : G)} : Set G) ≤ G' := by
  have hle : (Subgroup.centralizer ({t} : Set G')).map G'.subtype ≤
      Subgroup.centralizer ({(t : G)} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hc
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective G'.subtype_injective, h])
  rw [← heq]
  exact Subgroup.map_subtype_le _

end Centralizer

end CFSG.Sporadic.Co2Smith
