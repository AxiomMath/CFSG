module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneNine

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

namespace L128P

theorem le_normalizer_w128 (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    T ≤ Subgroup.normalizer (w128 V V₁ V₂ : Set G) := by
  have hUT : T ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
    (hs.almostSpecial h1222 h12213).G22_three.2
  have hCT : T ≤ Subgroup.normalizer (Subgroup.centralizer (V₂ : Set G) : Set G) :=
    hs.v2.2.2.trans (normalizer_le_normalizer_centralizer'' V₂)
  exact fun t ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨hUT ht, hCT ht⟩

theorem w128_eq_inf_pCoreOf (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) :
    w128 V V₁ V₂ = u128 V V₁ ⊓ pCoreOf 2 (i128 T L V V₁) := by
  rw [← i128_inf_centralizer h1222 h12213 hs, ← inf_assoc,
    inf_eq_left.mpr (le_conjClosure (u128 V V₁) (p128 T L V))]

theorem pCoreOf_i128_eq (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) {T L V : Subgroup G}
    {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂) {g : G}
    (hg : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    pCoreOf 2 (i128 T L V V₁) = w128 V V₁ V₂ ⊔ CFSG.conjugate (w128 V V₁ V₂) g := by
  have hA2 := almostSpecialL2Hyp h1222 h12213 hs
  have hUT : T ≤ Subgroup.normalizer (u128 V V₁ : Set G) :=
    (hs.almostSpecial h1222 h12213).G22_three.2
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hs.hyp hs.v1 hg hgN
  have hI : i128 T L V V₁ = u128 V V₁ ⊔ rconj (u128 V V₁) k := by
    rw [i128_eq_sup_conjugate h1222 h12213 hs hg hgN, hkY _ hUT]
    rfl
  have h3 := hA2.G23_three (lemma12_8_8_six h1222 hs) hk hkN hI rfl
    (w128_eq_inf_pCoreOf h1222 h12213 hs)
  rw [hkY _ (le_normalizer_w128 h1222 h12213 hs)]
  exact h3.1

end L128P

@[expose] def Lemma12_8_9W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      i128 T L V V₁ = u128 V V₁ ⊔ CFSG.conjugate (u128 V V₁) g ∧
      Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (i128 T L V V₁ : Set G) ∧
      pCoreOf 2 (i128 T L V V₁) = w128 V V₁ V₂ ⊔ CFSG.conjugate (w128 V V₁ V₂) g

theorem lemma12_8_9W_holds (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) : Lemma12_8_9W := by
  intro G _ _ T L V n V₁ V₂ hs g hg hgN
  have h1 := L128P.lemma12_8_9_one h1222 h12213 hs hg hgN
  exact ⟨h1.1.2, h1.2.2.2, L128P.pCoreOf_i128_eq h1222 h12213 hs hg hgN⟩

end CFSG.Quasithin.H13

end
