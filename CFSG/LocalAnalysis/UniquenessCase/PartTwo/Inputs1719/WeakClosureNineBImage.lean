module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBPhi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBBeta

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open Subgroup CFSG.Quasithin

variable {X : Type} [Group X]

theorem beta_conj_congr {L : Subgroup X} (β : MulAut L →* Equiv.Perm (Fin 8)) {a b : X}
    (ha : a ∈ L) (hb : b ∈ L) (h : a = b) :
    β (MulAut.conj ⟨a, ha⟩) = β (MulAut.conj ⟨b, hb⟩) := by
  subst h
  rfl

theorem blk_mem_TD {d : Equiv.Perm (Fin 8)} (hd : d ∈ D) : blk (d, 1) ∈ TD := by
  have h1 : D.map (blk.comp (MonoidHom.inl _ _)) ≤ TD := by
    rw [D, map_closure_list, closure_le]
    intro x hx
    simp only [List.map_cons, List.map_nil, MonoidHom.comp_apply, MonoidHom.inl_apply, blk_pu,
      blk_pv, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact subset_closure (by simp)
  exact h1 (mem_map_of_mem _ hd)

theorem rhoB_mem_D16 {L Tb : Subgroup X} {β : MulAut L →* Equiv.Perm (Fin 8)}
    (hβ : IsBeta L (Tb ⊓ L) β) {t : X} (ht : t ∈ Tb)
    (htN : t ∈ normalizer (L : Set X)) : rhoB L β t ∈ D16 := by
  have key : ∀ d ∈ D, rhoB L β t * d * (rhoB L β t)⁻¹ ∈ D := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := hβ.sylSurj d hd
    rw [rhoB_conj htN]
    refine hβ.syl _ ⟨?_, (conjAut L htN s).2⟩
    rw [conjAut_apply]
    exact Tb.mul_mem (Tb.mul_mem ht hs.1) (Tb.inv_mem ht)
  refine mem_D16_of_normalizes ?_ (key _ (subset_closure (by simp)))
    (key _ (subset_closure (by simp)))
  rw [rhoB_of_mem htN]
  exact hβ.mem _

namespace Setting

variable {L L' Tb : Subgroup X} {t₀ : X} (hS : Setting L L' Tb t₀)
  {β : MulAut L →* Equiv.Perm (Fin 8)}
include hS

theorem map_phi_L {S : Subgroup X} (hβ : IsBeta L S β) : L.map (hS.phi β) = L01 := by
  rw [L01_eq]
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [hS.phi_of_mem_L hl]
    exact ⟨_, hβ.inn ⟨l, hl⟩, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨⟨l, hl⟩, hlh⟩ := hβ.innSurj h hh
    refine ⟨l, hl, ?_⟩
    rw [hS.phi_of_mem_L hl, hlh]
    rfl

theorem map_phi_L' {S : Subgroup X} (hβ : IsBeta L S β) : L'.map (hS.phi β) = L02 := by
  rw [L02_eq]
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [hS.phi_of_mem_L' hl]
    exact ⟨_, hβ.inn _, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨⟨l, hl⟩, hlh⟩ := hβ.innSurj h hh
    refine ⟨t₀ * l * t₀⁻¹, hS.mem_L'_of_mem_conj hl, ?_⟩
    rw [hS.phi_of_mem_L' (hS.mem_L'_of_mem_conj hl), beta_conj_congr β _ hl (by group), hlh]
    rfl

theorem mem_D16_conj (hβ : IsBeta L (Tb ⊓ L) β) {t : X} (ht : t ∈ Tb)
    (htN : t ∈ normalizer (L : Set X)) : rhoB L β (t₀⁻¹ * t * t₀) ∈ D16 :=
  rhoB_mem_D16 hβ (Tb.mul_mem (Tb.mul_mem (Tb.inv_mem hS.t₀_mem) ht) hS.t₀_mem)
    (hS.conj_mem htN)

theorem phi_mem_TB3 (hβ : IsBeta L (Tb ⊓ L) β) {t : X} (ht : t ∈ Tb) : hS.phi β t ∈ TB 3 := by
  rw [phi_apply]
  by_cases htN : t ∈ normalizer (L : Set X)
  · rw [phiFun_of_mem htN]
    exact blk_mem_TB3 (rhoB_mem_D16 hβ ht htN) (hS.mem_D16_conj hβ ht htN)
  · rw [phiFun_of_not_mem htN]
    refine mul_mem (blk_mem_TB3 ?_ ?_) (mem_TB (by simp [bGens]))
    · exact rhoB_mem_D16 hβ (Tb.mul_mem ht hS.t₀_mem) (hS.mul_t₀_mem htN)
    · exact rhoB_mem_D16 hβ (Tb.mul_mem (Tb.inv_mem hS.t₀_mem) ht) (hS.inv_mul_mem htN)

theorem TD_le_map_phi (hβ : IsBeta L (Tb ⊓ L) β) : TD ≤ Tb.map (hS.phi β) := by
  have h1 : ∀ d ∈ D, blk (d, 1) ∈ Tb.map (hS.phi β) := by
    intro d hd
    obtain ⟨⟨s, hsL⟩, hs, rfl⟩ := hβ.sylSurj d hd
    exact ⟨s, hs.1, by rw [hS.phi_of_mem_L hsL]⟩
  have h2 : ∀ d ∈ D, blk (1, d) ∈ Tb.map (hS.phi β) := by
    intro d hd
    obtain ⟨⟨s, hsL⟩, hs, rfl⟩ := hβ.sylSurj d hd
    refine ⟨t₀ * s * t₀⁻¹, Tb.mul_mem (Tb.mul_mem hS.t₀_mem hs.1) (Tb.inv_mem hS.t₀_mem), ?_⟩
    rw [hS.phi_of_mem_L' (hS.mem_L'_of_mem_conj hsL), beta_conj_congr β _ hsL (by group)]
  rw [TD, closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [← blk_pu]
    exact h1 _ (subset_closure (by simp))
  · rw [← blk_pv]
    exact h1 _ (subset_closure (by simp))
  · rw [← blk_pu']
    exact h2 _ (subset_closure (by simp))
  · rw [← blk_pv']
    exact h2 _ (subset_closure (by simp))

theorem sig_or_d1sig (hβ : IsBeta L (Tb ⊓ L) β) :
    sig ∈ Tb.map (hS.phi β) ∨ d1 * sig ∈ Tb.map (hS.phi β) := by
  have hTD := hS.TD_le_map_phi hβ
  have ht₀ : hS.phi β t₀ = blk (rhoB L β (t₀ * t₀), 1) * sig := by
    rw [phi_apply, phiFun_of_not_mem hS.t₀_not_mem, inv_mul_cancel, rhoB_one]
  have hmem : hS.phi β t₀ ∈ Tb.map (hS.phi β) := mem_map_of_mem _ hS.t₀_mem
  have hD16 := rhoB_mem_D16 hβ (Tb.mul_mem hS.t₀_mem hS.t₀_mem) (hS.mul_t₀_mem hS.t₀_not_mem)
  rcases D16_split hD16 with hd | ⟨d, hd, hdeq⟩
  · left
    have h1 : blk (rhoB L β (t₀ * t₀), 1) ∈ Tb.map (hS.phi β) := hTD (blk_mem_TD hd)
    have e : sig = (blk (rhoB L β (t₀ * t₀), 1))⁻¹ * hS.phi β t₀ := by
      rw [ht₀]
      group
    rw [e]
    exact mul_mem (inv_mem h1) hmem
  · right
    have h1 : blk (d, 1) ∈ Tb.map (hS.phi β) := hTD (blk_mem_TD hd)
    have e1 : blk (d * NFF7.g2, 1) = blk (d, 1) * d1 := by
      rw [← blk_g2, blk_mul_blk, mul_one]
    have e : d1 * sig = (blk (d, 1))⁻¹ * hS.phi β t₀ := by
      rw [ht₀, hdeq, e1]
      group
    rw [e]
    exact mul_mem (inv_mem h1) hmem

end Setting

end CFSG.LocalAnalysis.WeakClosure81.NGM
