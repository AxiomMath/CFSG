module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Crit
public import CFSG.Quasithin.Recognition.F112WLocal2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem IsNaturalAt.inf_centralizer_eq_zpowers (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) :
    V ⊓ Subgroup.centralizer ((G₁ ⊓ G₂ : Subgroup D) : Set D) = Subgroup.zpowers z := by
  have hcard := F112W.card_inf_centralizer_T (h.amalgamHypV hn) hn.natural
  have hle : Subgroup.zpowers z ≤
      V ⊓ Subgroup.centralizer ((G₁ ⊓ G₂ : Subgroup D) : Set D) :=
    Subgroup.zpowers_le.mpr ⟨hn.z_mem_V, hn.z_mem.2⟩
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hn.z_sq hn.z_ne
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hz2])).symm

theorem IsNaturalAt.normalizes_inf_centralizer (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) (hzG₂ : ∀ y ∈ G₂, y * z * y⁻¹ = z) :
    G₂ ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer ((G₁ ⊓ G₂ : Subgroup D) : Set D) : Subgroup D) : Set D) := by
  rw [hn.inf_centralizer_eq_zpowers h]
  intro y hy
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hc : Commute y z := mul_eq_of_conj_eq (hzG₂ y hy)
  exact (hc.zpow_right k).symm.eq

theorem critDist_dichotomy (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) (hVQ : V ≤ pCoreOf 2 G₂) :
    critDist (G₁ ⊔ G₂) G₁ G₂ V = 2 ∨
      (3 ≤ critDist (G₁ ⊔ G₂) G₁ G₂ V ∧ IsElemAbelian 2 (conjClosure V G₂)) := by
  have hyp := h.amalgamHypV hn
  have hV : V ≠ ⊥ := hn.natural.ne_bot
  have h2 := two_le_critDist_of_le_pCoreOf hyp hV hVQ
  by_cases hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2
  · exact Or.inl hb
  · refine Or.inr ⟨by omega, ?_⟩
    have := isElemAbelian_Vv_γ₁ hyp hV (by omega)
    rwa [Vv_γ₁ hyp.le₂ hyp.normalizes] at this

theorem labelled_two_structure (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) (hzG₂ : ∀ y ∈ G₂, y * z * y⁻¹ = z)
    (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) :
    ⁅V, G₁ ⊓ G₂⁆ = Subgroup.zpowers z ∧ ⁅V, pCoreOf 2 G₂⁆ = Subgroup.zpowers z ∧
      ⁅conjClosure V G₂, pCoreOf 2 G₂⁆ = Subgroup.zpowers z ∧
      ⁅conjClosure V G₂, conjClosure V G₂⁆ = Subgroup.zpowers z := by
  have hyp := h.amalgamHypV hn
  have hZ := hn.normalizes_inf_centralizer h hzG₂
  have hZeq := hn.inf_centralizer_eq_zpowers h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hZeq]; exact F112W.commutator_V_T hyp hn.natural hb
  · rw [← hZeq]; exact F112W.commutator_V_pCoreOf hyp hn.natural hb
  · rw [← hZeq]; exact F112W.commutator_conjClosure_pCoreOf hyp hn.natural hb hZ
  · rw [← hZeq]; exact F112W.commutator_conjClosure_self hyp hn.natural hb hZ

end GoldAmL

end F6

end CFSG.Quasithin
