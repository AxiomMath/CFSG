module

public import CFSG.Quasithin.Vol2.Ch11SecB24Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

section General

variable {G : Type} [Group G]

theorem conjSubgroup_inf_centralizer (V B : Subgroup G) (g : G) :
    conjSubgroup (V ⊓ Subgroup.centralizer (B : Set G)) g =
      conjSubgroup V g ⊓ Subgroup.centralizer (conjSubgroup B g : Set G) := by
  rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]

theorem card_eq_relIndex_mul_card {H K : Subgroup G} (h : H ≤ K) :
    Nat.card K = H.relIndex K * Nat.card H := by
  rw [← Subgroup.relIndex_mul_card (H := H) (K := K), inf_eq_left.mpr h]

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem claim24 (hI : In24) {V₁ V₂ : Subgroup G} (h : Hyp24 T L I n V₁ V₂) {g : G}
    (hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥) {W : Subgroup G} (hWV : W ≤ fsuV T I)
    (h1 : ⁅W, conjSubgroup (fsuV T I) g⁆ ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₁)
    (h2 : E3.mQuot (conjSubgroup (fsuV T I) g)
      (conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (W : Set G)) = n)
    (h3 : E3.mQuot W (W ⊓ Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G)) = n) :
    False := by
  have hfl := h.flag hI
  set V := fsuV T I with hVdef
  set A := conjSubgroup V g with hAdef
  set CV := V ⊓ Subgroup.centralizer (L : Set G) with hCVdef
  have hWN : W ≤ Subgroup.normalizer (A : Set G) := by
    have hC := centralizer_le_normalizer_of_lt (V := V)
      (B := A ⊓ Subgroup.centralizer (W : Set G)) (g := g) inf_le_left
      (by rw [h2]; exact h.lt_rParam hI)
    refine le_trans (fun w hw => ?_) hC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx.2 w hw).symm
  have hAV : conjSubgroup A g⁻¹ = V := E3.conjSubgroup_conj_inv V g
  set E := conjSubgroup W g⁻¹ with hEdef
  have hEN : E ≤ ⊤ ⊓ Subgroup.normalizer (V : Set G) := by
    refine le_inf le_top ?_
    have := E3.conjSubgroup_mono_left g⁻¹ hWN
    rwa [E3.conjSubgroup_normalizer, hAV] at this
  have hEel : IsElemAbelian 2 E :=
    E3.isElemAbelian_conjSubgroup (B2F.isElemAbelian_mono hWV hfl.elem) g⁻¹
  have hE2 : E3.mQuot V (V ⊓ Subgroup.centralizer (E : Set G)) = n := by
    have := E3.mQuot_conjSubgroup A (A ⊓ Subgroup.centralizer (W : Set G)) g⁻¹
    rw [conjSubgroup_inf_centralizer, hAV, h2] at this
    exact this
  have hE3 : E3.mQuot E (E ⊓ Subgroup.centralizer (V : Set G)) = n := by
    have := E3.mQuot_conjSubgroup W (W ⊓ Subgroup.centralizer (A : Set G)) g⁻¹
    rw [conjSubgroup_inf_centralizer, hAV, h3] at this
    exact this
  have hcomm : ⁅V, E⁆ = conjSubgroup ⁅A, W⁆ g⁻¹ := by
    rw [E3.conjSubgroup_commutator, hAV]
  have hWA : ⁅W, A⁆ ≤ V₁ := h1 ▸ le_sup_left
  have hcardV₁ : Nat.card V₁ = 2 ^ n * Nat.card CV := by
    rw [card_eq_relIndex_mul_card hfl.cV_le, hfl.index₁]
  have hcard : Nat.card ↥⁅V, E⁆ ≤ 2 ^ n * Nat.card CV := by
    rw [hcomm, E3.card_conjSubgroup, Subgroup.commutator_comm, ← hcardV₁]
    exact Subgroup.card_le_of_le hWA
  obtain ⟨hCle, hst, hidx⟩ :=
    hI.facts.rootPoint G L V ⊤ T V₁ V₂ n hfl E hEN hEel hE2 hE3 hcard
  obtain ⟨l, hlL, hl⟩ := hI.facts.pointTrans G L V ⊤ T V₁ V₂ n hfl ⁅V, E⁆ hCle
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hEN.trans inf_le_right)) hst hidx
  have hcardWA : Nat.card ↥⁅W, A⁆ = Nat.card V₁ := by
    rw [hcardV₁, ← hidx, ← card_eq_relIndex_mul_card hCle, hcomm, E3.card_conjSubgroup,
      Subgroup.commutator_comm]
  have hWAeq : ⁅W, A⁆ = V₁ := Subgroup.eq_of_le_of_card_ge hWA (le_of_eq hcardWA.symm)
  have hP : ⁅V, E⁆ = conjSubgroup V₁ l⁻¹ := by
    rw [← hl, E3.conjSubgroup_conj_inv]
  have hV₁g : conjSubgroup V₁ (l⁻¹ * g) = V₁ := by
    rw [← conjSubgroup_conjSubgroup, ← hP, hcomm, E3.conjSubgroup_inv_conj,
      Subgroup.commutator_comm, hWAeq]
  have hmem : l⁻¹ * g ∈ Subgroup.normalizer (V₁ : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp hV₁g
  have hVconj : conjSubgroup V (l⁻¹ * g) = A := by
    rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr
      (Subgroup.inv_mem _ (hfl.le_normalizer hlL))]
  exact not_mem_normalizer_of_ne_bot h.abelian (g := l⁻¹ * g) (by rw [hVconj]; exact hnc) hmem

end CFSG.Quasithin.Vol2.Ch11.SecB
