module

public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

section Alpha

variable [Finite G] {V R : Subgroup G} (hV : IsElemAbelian 2 V)

theorem card_eq_of_not_strong' (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hc : ∀ A, ¬ IsStrongFFOffender hV R A) {A : Subgroup G}
    (hA : IsMaxElemAbelian R A) (hAC : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  have hnot : ¬ IsStrongFFOffender hV R A := hc A
  have h := B2_8_card_eq hV hVR hRN ⟨hA, hAC⟩ hnot
  have h1 : Nat.card (IntMod V hV) = Nat.card V := rfl
  rw [h1, card_autI_eq hV (hA.1.trans hRN), card_fixV_autI hV (hA.1.trans hRN)] at h
  exact h

theorem alpha_facts' (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hc : ∀ A, ¬ IsStrongFFOffender hV R A) :
    (∀ D, IsMaxElemAbelian (R ⊓ Subgroup.centralizer (V : Set G)) D → IsMaxElemAbelian R D) ∧
    V ≤ omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ∧
    omegaOneCenterOf (thompsonJ R) ≤
      omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ∧
    (∀ A, IsMaxElemAbelian R A →
      omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) ≤
        (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
  set Q := R ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := le_centralizer_self hV
  have hVQ : V ≤ Q := le_inf hVR hVC
  have hsub : ∀ D, IsMaxElemAbelian Q D → IsMaxElemAbelian R D := by
    by_cases hex : ∃ A, IsMaxElemAbelian R A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G)
    · obtain ⟨A, hA, hAC⟩ := hex
      exact (B24_three hV hVR hA (card_eq_of_not_strong' hV hVR hRN hc hA hAC)).2.2.1
    · push Not at hex
      obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian R
      have hA₀Q : A₀ ≤ Q := le_inf hA₀.1 (hex A₀ hA₀)
      intro D hD
      refine ⟨hD.1.trans inf_le_left, hD.2.1, fun B hBR hB => ?_⟩
      exact (hA₀.2.2 B hBR hB).trans (hD.2.2 A₀ hA₀Q hA₀.2.1)
  have hVD : ∀ D, IsMaxElemAbelian Q D → V ≤ D := by
    intro D hD
    have hDC : D ≤ Subgroup.centralizer (V : Set G) := hD.1.trans inf_le_right
    have hE : IsElemAbelian 2 (D ⊔ V) :=
      isElemAbelian_sup_of_commute hD.2.1 hV fun d hd v hv =>
        (Subgroup.mem_centralizer_iff.1 (hDC hd) v hv).symm
    have hEQ : D ⊔ V ≤ Q := sup_le hD.1 hVQ
    have h := Subgroup.eq_of_le_of_card_ge (le_sup_left : D ≤ D ⊔ V) (hD.2.2 _ hEQ hE)
    exact le_sup_right.trans (le_of_eq h.symm)
  have hE : ∀ A, IsMaxElemAbelian R A →
      IsMaxElemAbelian Q ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
    intro A hA
    have hEe : IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
      isElemAbelian_sup_of_commute (isElemAbelian_mono inf_le_left hA.2.1) hV
        fun a ha v hv => (Subgroup.mem_centralizer_iff.1 ha.2 v hv).symm
    have hEQ : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ Q :=
      sup_le (le_inf (inf_le_left.trans hA.1) inf_le_right) hVQ
    refine ⟨hEQ, hEe, fun B hBQ hB => ?_⟩
    by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
    · have hAE : A ≤ (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V :=
        le_sup_of_le_left (le_inf le_rfl hAC)
      exact (hA.2.2 B (hBQ.trans inf_le_left) hB).trans (Subgroup.card_le_of_le hAE)
    · have hmax := (B24_three hV hVR hA (card_eq_of_not_strong' hV hVR hRN hc hA hAC)).1
      exact hmax.2.2 B (hBQ.trans inf_le_left) hB
  refine ⟨hsub, ?_, ?_, fun A hA => ?_⟩
  · rw [(omegaOne_centralizer_thompsonJ Q).2]
    exact le_iInf₂ fun D hD => hVD D hD
  · rw [(omegaOne_centralizer_thompsonJ R).2, (omegaOne_centralizer_thompsonJ Q).2]
    exact le_iInf₂ fun D hD => iInf₂_le D (hsub D hD)
  · rw [(omegaOne_centralizer_thompsonJ Q).2]
    exact iInf₂_le _ (hE A hA)

end Alpha

end B2F

end CFSG.Quasithin
