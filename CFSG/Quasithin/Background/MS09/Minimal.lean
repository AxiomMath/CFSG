module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.MS09

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B6

variable {G : Type*} [Group G]

@[expose] def IsUniqueMaxSub (H X L₀ : Subgroup G) : Prop :=
  X ≤ L₀ ∧ L₀ < H ∧ ∀ K : Subgroup G, X ≤ K → K < H → K ≤ L₀

namespace IsUniqueMaxSub

variable {H X L₀ : Subgroup G}

theorem le (h : IsUniqueMaxSub H X L₀) : X ≤ L₀ := h.1

theorem lt (h : IsUniqueMaxSub H X L₀) : L₀ < H := h.2.1

theorem le_of_lt (h : IsUniqueMaxSub H X L₀) {K : Subgroup G} (hXK : X ≤ K) (hK : K < H) :
    K ≤ L₀ :=
  h.2.2 K hXK hK

theorem eq_of_not_le (h : IsUniqueMaxSub H X L₀) {K : Subgroup G} (hXK : X ≤ K) (hKH : K ≤ H)
    (hK : ¬ K ≤ L₀) : K = H := by
  by_contra hne
  exact hK (h.le_of_lt hXK (lt_of_le_of_ne hKH hne))

theorem lt_top (h : IsUniqueMaxSub H X L₀) : X < H := lt_of_le_of_lt h.le h.lt

theorem X_le (h : IsUniqueMaxSub H X L₀) : X ≤ H := h.lt_top.le

theorem conjSub (h : IsUniqueMaxSub H X L₀) (g : G) :
    IsUniqueMaxSub (B6.conjSub g H) (B6.conjSub g X) (B6.conjSub g L₀) := by
  refine ⟨(B6.conjSub g).le_iff_le.mpr h.le, (B6.conjSub g).lt_iff_lt.mpr h.lt, fun K hK hKH => ?_⟩
  have h1 : (B6.conjSub g).symm K < H := by
    rw [← (B6.conjSub g).lt_iff_lt, OrderIso.apply_symm_apply]
    exact hKH
  have h2 : X ≤ (B6.conjSub g).symm K := by
    rw [← (B6.conjSub g).le_iff_le, OrderIso.apply_symm_apply]
    exact hK
  have h3 := h.le_of_lt h2 h1
  rw [← (B6.conjSub g).le_iff_le, OrderIso.apply_symm_apply] at h3
  exact h3

variable [Finite G]

theorem dichotomy (h : IsUniqueMaxSub H X L₀) {S N : Subgroup G} (hS : IsSylowTwoOf S H)
    (hXS : X ≤ S) (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    X ⊔ N = H ∨ S ⊓ N ≤ pCoreOf 2 H := by
  by_cases h1 : X ⊔ N = H
  · exact Or.inl h1
  right
  have hSN : IsSylowTwoOf (S ⊓ N) N := isSylowTwoOf_inf_normal hS hNH hHN
  have hfr := frattini_two hNH hHN hSN
  have hSnorm : S ≤ Subgroup.normalizer ((S ⊓ N : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hHN (hS.1 hs)⟩
  have hK : H ⊓ Subgroup.normalizer ((S ⊓ N : Subgroup G) : Set G) = H := by
    by_contra hne
    have hXK : X ≤ H ⊓ Subgroup.normalizer ((S ⊓ N : Subgroup G) : Set G) :=
      le_inf (hXS.trans hS.1) (hXS.trans hSnorm)
    have hK0 := h.le_of_lt hXK (lt_of_le_of_ne inf_le_left hne)
    have hN0 : N ≤ L₀ :=
      le_sup_right.trans (h.le_of_lt le_sup_left (lt_of_le_of_ne (sup_le h.X_le hNH) h1))
    exact absurd (hfr.trans (sup_le hN0 hK0)) (not_le_of_gt h.lt)
  have hHn : H ≤ Subgroup.normalizer ((S ⊓ N : Subgroup G) : Set G) := by
    rw [← hK]
    exact inf_le_right
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans hNH) hHn
    (hS.2.1.to_le inf_le_left)

theorem inf_kerIn_le (h : IsUniqueMaxSub H X L₀) {S : Subgroup G} (hS : IsSylowTwoOf S H)
    (hXS : X ≤ S) : S ⊓ kerIn L₀ H ≤ pCoreOf 2 H := by
  rcases h.dichotomy hS hXS (kerIn_le.trans h.lt.le) (le_normalizer_kerIn L₀ H) with h1 | h1
  · exact absurd (h1 ▸ sup_le h.le kerIn_le) (not_le_of_gt h.lt)
  · exact h1

theorem exists_not_mem_conjSub (h : IsUniqueMaxSub H X L₀) {S : Subgroup G}
    (hS : IsSylowTwoOf S H) (hXS : X ≤ S) {c : G} (hcS : c ∈ S) (hc : c ∉ pCoreOf 2 H) :
    ∃ g ∈ H, c ∉ B6.conjSub g L₀ := by
  have hck : c ∉ kerIn L₀ H := fun hk => hc (h.inf_kerIn_le hS hXS ⟨hcS, hk⟩)
  rw [mem_kerIn] at hck
  push Not at hck
  obtain ⟨b, hb, hbc⟩ := hck
  refine ⟨b⁻¹, H.inv_mem hb, fun hmem => hbc ?_⟩
  rw [mem_conjSub, inv_inv] at hmem
  exact hmem

end IsUniqueMaxSub

theorem MinParabolic.isUniqueMaxSub [Finite G] {H T M : Subgroup G} (h : MinParabolic H T M) :
    IsUniqueMaxSub H T M := by
  refine ⟨h.le, h.maximal.1, fun K hTK hKH => ?_⟩
  obtain ⟨N, hN, hKN⟩ := exists_isMaxSubgroupIn hKH
  rw [h.eq_of_maximal hN (hTK.trans hKN)] at hKN
  exact hKN

theorem pCoreOf_conjSub (H : Subgroup G) (g : G) :
    pCoreOf 2 (B6.conjSub g H) = B6.conjSub g (pCoreOf 2 H) :=
  CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) H

end CFSG.Quasithin.MS09

end
