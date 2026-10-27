module

public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenDist
public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenSyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem conjSubgroup_sup_aux (A B : Subgroup G) (t : G) :
    conjSubgroup (A ⊔ B) t = conjSubgroup A t ⊔ conjSubgroup B t := by
  unfold conjSubgroup
  exact Subgroup.map_sup _ _ _

theorem pairSub_conjSubgroup_conj (A : Subgroup G) (k t : G) :
    pairSub (conjSubgroup A t) (t⁻¹ * k * t) = conjSubgroup (pairSub A k) t := by
  unfold pairSub
  have h1 : conjSubgroup (conjSubgroup A t) (t⁻¹ * k * t) =
      conjSubgroup (conjSubgroup A k) t := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [h1, conjSubgroup_sup_aux]

namespace Conf196

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G} {g : G} {K : Subgroup G}

theorem exists_normalized (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    (hc : Conf196 D V X g K) {k : G} (hk : k ∈ K)
    (hL : ¬ IsPGroup 2 ↥(pairSub (conjSubgroup V g) k)) :
    ∃ (g' : G) (K' : Subgroup G) (k' : G), Conf196 D V X g' K' ∧ k' ∈ K' ∧
      X ⊓ K' = X ⊓ K ∧ ¬ IsPGroup 2 ↥(pairSub (conjSubgroup V g') k') ∧
      X ⊓ K ≤ pairSub (conjSubgroup V g') k' := by
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  set Q := pCoreOf 2 (X ⊔ D.T) with hQ
  set L := pairSub (conjSubgroup V g) k with hLdef
  have hLK : L ≤ K := hc.pairSub_le_K c hk
  obtain ⟨x, hxL, hxo⟩ := c.hyp.exists_orderOf_of_not_isPGroup (hLK.trans hc.le_H) hL
  have hxPQ : x ∈ (X ⊓ K) ⊔ Q := hc.mem_inf_K_sup_pCoreOf c h162 h763 (hLK hxL) hxo
  have hPcard : Nat.card ↥(X ⊓ K) = p := hc.card_inf_K c h162 h763
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ D.T)
  have hPQ : X ⊓ K ≤ normalizer (Q : Set G) :=
    inf_le_left.trans (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  obtain ⟨q, hqQ, hxq⟩ := exists_conj_zpowers_eq c.hyp.odd hPcard hQ2 hPQ hxo hxPQ
  have hqT : q⁻¹ ∈ D.T := D.T.inv_mem (Hyp193.pCoreOf_le_T c.hyp hqQ)
  have hc' : Conf196 D V X (g * q⁻¹) (conjSubgroup K q⁻¹) := hc.conj_T hqT
  have hk' : q⁻¹⁻¹ * k * q⁻¹ ∈ conjSubgroup K q⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have e : q⁻¹ * (q⁻¹⁻¹ * k * q⁻¹) * q⁻¹⁻¹ = k := by group
    rw [e]
    exact hk
  have hL' : pairSub (conjSubgroup V (g * q⁻¹)) (q⁻¹⁻¹ * k * q⁻¹) = conjSubgroup L q⁻¹ := by
    rw [← conjSubgroup_conjSubgroup V g q⁻¹]
    exact pairSub_conjSubgroup_conj (conjSubgroup V g) k q⁻¹
  have hPL : X ⊓ K ≤ conjSubgroup L q⁻¹ := by
    have h1 : conjSubgroup (X ⊓ K) q ≤ L := by
      rw [← hxq]
      exact Subgroup.zpowers_le.2 hxL
    have h2 := E3.conjSubgroup_mono_left q⁻¹ h1
    rwa [conjSubgroup_conjSubgroup_inv] at h2
  refine ⟨g * q⁻¹, conjSubgroup K q⁻¹, q⁻¹⁻¹ * k * q⁻¹, hc', hk', ?_, ?_, ?_⟩
  · have hle : X ⊓ K ≤ X ⊓ conjSubgroup K q⁻¹ := by
      refine le_inf inf_le_left ?_
      have h3 := hc'.pairSub_le_K c hk'
      rw [hL'] at h3
      exact hPL.trans h3
    exact (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hc'.card_inf_K c h162 h763, hPcard])).symm
  · rw [hL']
    intro h
    apply hL
    have := E3.isPGroup_conjSubgroup h q⁻¹⁻¹
    rwa [inv_inv, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
  · rw [hL']
    exact hPL

end Conf196

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem exists_pair (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V') :
    ∃ (g₁ g₂ : G) (K₁ K₂ : Subgroup G) (k₁ k₂ : G),
      Conf196 D V X g₁ K₁ ∧ Conf196 D V X g₂ K₂ ∧ k₁ ∈ K₁ ∧ k₂ ∈ K₂ ∧
      ¬ IsPGroup 2 ↥(pairSub (conjSubgroup V g₁) k₁) ∧
      ¬ IsPGroup 2 ↥(pairSub (conjSubgroup V g₂) k₂) ∧
      X ⊓ K₁ ≠ X ⊓ K₂ ∧ X ⊓ K₁ ≤ pairSub (conjSubgroup V g₁) k₁ ∧
      X ⊓ K₂ ≤ pairSub (conjSubgroup V g₂) k₂ := by
  obtain ⟨g₁, g₂, K₁, K₂, h₁, h₂, hne⟩ := c.exists_inf_ne h162 h763
  obtain ⟨k₁, hk₁, hL₁⟩ := h₁.exists_k c
  obtain ⟨k₂, hk₂, hL₂⟩ := h₂.exists_k c
  obtain ⟨g₁', K₁', k₁', h₁', hk₁', he₁, hL₁', hP₁⟩ := h₁.exists_normalized c h162 h763 hk₁ hL₁
  obtain ⟨g₂', K₂', k₂', h₂', hk₂', he₂, hL₂', hP₂⟩ := h₂.exists_normalized c h162 h763 hk₂ hL₂
  refine ⟨g₁', g₂', K₁', K₂', k₁', k₂', h₁', h₂', hk₁', hk₂', hL₁', hL₂', ?_, ?_, ?_⟩
  · rw [he₁, he₂]
    exact hne
  · rw [he₁]
    exact hP₁
  · rw [he₂]
    exact hP₂

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
