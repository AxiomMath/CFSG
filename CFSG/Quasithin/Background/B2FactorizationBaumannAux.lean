module

public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

theorem cjSub_mul (a b : G) (X : Subgroup G) : cjSub (a * b) X = cjSub a (cjSub b X) := by
  ext x
  simp only [mem_cjSub, mul_inv_rev, mul_assoc]

theorem cjSub_eq_of_mem_normalizer {g : G} {K : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : cjSub g K = K :=
  mem_normalizer_iff_cjSub_eq.1 hg

theorem cjSub_centralizer (g : G) (A : Subgroup G) :
    cjSub g (Subgroup.centralizer (A : Set G)) = Subgroup.centralizer (cjSub g A : Set G) :=
  centralizer_map_mulEquiv (MulAut.conj g) A

theorem cjSub_inf (g : G) (A B : Subgroup G) : cjSub g (A ⊓ B) = cjSub g A ⊓ cjSub g B :=
  Subgroup.map_inf A B _ (MulAut.conj g).injective

theorem le_normalizer_of_cjSub_le {K : Subgroup G} {g : G} (h : cjSub g K ≤ K)
    (h' : cjSub g⁻¹ K ≤ K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_cjSub_eq]
  refine le_antisymm h ?_
  have := cjSub_mono (g := g) h'
  rwa [cjSub_cjSub_inv] at this

theorem rk_cjSub (g : G) (H : Subgroup G) : rk ↥(cjSub g H) = rk ↥H := by
  unfold rk
  rw [card_cjSub]

theorem rk_sup_add_rk_inf_of_commute [Finite G] {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    rk ↥(A ⊔ B) + rk ↥(A ⊓ B) = rk ↥A + rk ↥B := by
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne',
    ← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_sup_mul_card_inf_of_commute h]

theorem eq_of_le_of_rk_le_of_isPGroup {H K : Subgroup G} [Finite G] (hK : IsPGroup 2 K)
    (hHK : H ≤ K) (h : rk ↥K ≤ rk ↥H) : H = K := by
  refine Subgroup.eq_of_le_of_card_ge hHK ?_
  rw [card_eq_two_pow_of_isPGroup hK, card_eq_two_pow_of_isPGroup (hK.to_le hHK)]
  exact Nat.pow_le_pow_right (by norm_num) h

theorem rkIdx_fixV_autI [Finite G] {U Y : Subgroup G} (hU : IsElemAbelian 2 U)
    (hY : Y ≤ Subgroup.normalizer (U : Set G)) :
    rkIdx (fixV (autI hU Y)) + rk ↥(U ⊓ Subgroup.centralizer (Y : Set G)) = rk ↥U := by
  have h1 := rk_add_rkIdx (fixV (autI hU Y))
  have h2 : rk ↥(fixV (autI hU Y)) = rk ↥(U ⊓ Subgroup.centralizer (Y : Set G)) := by
    unfold rk
    rw [card_fixV_autI hU hY]
  have h3 : rk (IntMod U hU) = rk ↥U := rfl
  omega

theorem rk_inf_centralizer_cjSub {U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) (Y : Subgroup G) :
    rk ↥(U ⊓ Subgroup.centralizer (cjSub g Y : Set G)) =
      rk ↥(U ⊓ Subgroup.centralizer (Y : Set G)) := by
  rw [← rk_cjSub g (U ⊓ Subgroup.centralizer (Y : Set G)), cjSub_inf, cjSub_centralizer,
    cjSub_eq_of_mem_normalizer hg]

theorem pRank_cjSub (g : G) (X : Subgroup G) [Finite G] : Open.pRank 2 (cjSub g X) = Open.pRank 2 X := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian X
  have hA' : IsMaxElemAbelian (cjSub g X) (cjSub g A) :=
    (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).2 hA
  have h1 := (isMaxElemAbelian_iff_corank_zero.1 hA).2.2
  have h2 := (isMaxElemAbelian_iff_corank_zero.1 hA').2.2
  rw [card_cjSub] at h2
  rw [h1] at h2
  simpa using h2.symm

theorem thompsonJ_le_thompsonJ_of_pRank_eq [Finite G] {Y R : Subgroup G} (hYR : Y ≤ R)
    (h : Open.pRank 2 Y = Open.pRank 2 R) : thompsonJ Y ≤ thompsonJ R := by
  refine iSup_le fun A => iSup_le fun hA => ?_
  have h1 := (isMaxElemAbelian_iff_corank_zero.1 hA).2.2
  have hA' : IsMaxElemAbelian R A :=
    isMaxElemAbelian_iff_corank_zero.2 ⟨hA.1.trans hYR, hA.2.1, by rw [← h]; exact h1⟩
  exact le_iSup₂_of_le A hA' le_rfl

theorem cjSub_le_thompsonJ [Finite G] {X R : Subgroup G} {l : G} (hX : X = thompsonJ X)
    (hr : Open.pRank 2 X = Open.pRank 2 R) (hl : cjSub l X ≤ R) : cjSub l X ≤ thompsonJ R := by
  have h1 : cjSub l X = thompsonJ (cjSub l X) := by
    conv_lhs => rw [hX]
    exact thompsonJ_map_mulEquiv (MulAut.conj l) X
  rw [h1]
  exact thompsonJ_le_thompsonJ_of_pRank_eq (h1 ▸ hl) (by rw [pRank_cjSub, hr])

theorem isElemAbelian_omegaOneCenterOf (X : Subgroup G) :
    IsElemAbelian 2 (omegaOneCenterOf X) := by
  unfold omegaOneCenterOf omegaOneOf
  refine isElemAbelian_closure ?_ ?_
  · rintro a ⟨ha, -⟩ b ⟨hb, -⟩
    exact Subgroup.mem_centralizer_iff.1 hb.2 a ha.1
  · rintro a ⟨-, ha2⟩
    exact ha2

section Alpha

variable [Finite G] {V R : Subgroup G} (hV : IsElemAbelian 2 V)

theorem card_eq_of_not_strong (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hc : ∀ B, ¬ IsStrongFFStarOffender (autI hV R) B) {A : Subgroup G}
    (hA : IsMaxElemAbelian R A) (hAC : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  have hnot : ¬ IsStrongFFOffender hV R A := fun h => hc _ h.2
  have h := B2_8_card_eq hV hVR hRN ⟨hA, hAC⟩ hnot
  have h1 : Nat.card (IntMod V hV) = Nat.card V := rfl
  rw [h1, card_autI_eq hV (hA.1.trans hRN), card_fixV_autI hV (hA.1.trans hRN)] at h
  exact h

theorem alpha_facts (hVR : V ≤ R) (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hc : ∀ B, ¬ IsStrongFFStarOffender (autI hV R) B) :
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
      exact (B24_three hV hVR hA (card_eq_of_not_strong hV hVR hRN hc hA hAC)).2.2.1
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
    · have hmax := (B24_three hV hVR hA (card_eq_of_not_strong hV hVR hRN hc hA hAC)).1
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
