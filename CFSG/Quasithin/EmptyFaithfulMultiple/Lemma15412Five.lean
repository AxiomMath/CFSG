module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Omega

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace Setup

variable (h : Setup T M) {Y : Subgroup G}
include h

theorem commutator_inf_centralizer_thompsonJ (hYM : Y ≤ M) :
    ⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G) =
      ⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (baum T : Set G) := by
  apply le_antisymm
  · rintro x ⟨hxU, hxC⟩
    refine ⟨hxU, ?_⟩
    change x ∈ Subgroup.centralizer (baum T : Set G)
    have hxE : x ∈ omegaOneCenterOf (thompsonJ T) :=
      inf_centralizer_thompsonJ_le (h.isElemAbelian_commutator hYM) (h.commutator_le_T hYM)
        ⟨hxU, hxC⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp hs.2 x hxE).symm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (thompsonJ_le_baum T))

theorem five (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    IsSylowTwoOf (baum T) (Y ⊔ baum T) ∧
      (twoReducedJoin (Y ⊔ T) = ⁅VZ T M, Y⁆ ⊔ eYOf T Y ∧ ⁅VZ T M, Y⁆ ⊓ eYOf T Y = ⊥ ∧
        eOf T = eCentOf T Y ⊔ (⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (baum T : Set G)) ∧
        eCentOf T Y ⊓ (⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (baum T : Set G)) = ⊥) := by
  have hmin := h.minParabolic hY hYM
  have hsolv := h.solv_sup hYM
  have hrank := h.rank_sup hYM
  have hK := h.twoResidual_eq hY
  have hUred := h.isTwoReducedIn_commutator hY hYM
  have hUJ := h.not_thompsonJ_le hY hYM
  obtain ⟨-, -, hsyl, hE, -⟩ := E2_3_two_of_isSolvable hUred.2.2.1 hmin hsolv hrank hUred hUJ
  rw [hK] at hsyl hE
  have hWred := h.isTwoReducedIn_omega hYM
  have hWJ := h.not_thompsonJ_le_omega hY hYM
  obtain ⟨𝓗', I', B'⟩ := E2.exists_blocks hWred.2.2.1 hWred hsolv hmin.isSylow hWJ
  have hWdec := B'.eq_commutator_sup hmin hsolv (hrank 3 Nat.prime_three (by norm_num)) hWred hWJ
  rw [hK, h.commutator_omega_eq hY hYM] at hWdec
  have hCU := h.commutator_inf_centralizer hY hYM
  refine ⟨hsyl, ?_, ?_, ?_, ?_⟩
  · rw [h.twoReducedJoin_eq hYM]
    exact hWdec
  · exact le_bot_iff.1 ((inf_le_inf_left _ inf_le_right).trans hCU.le)
  · have e : eOf T = omegaOneCenterOf (thompsonJ T) := rfl
    rw [e, hE, h.commutator_inf_centralizer_thompsonJ hYM, sup_comm]
    rfl
  · refine le_bot_iff.1 (le_trans ?_ hCU.le)
    rintro x ⟨⟨-, hxY⟩, hxU, -⟩
    exact ⟨hxU, hxY⟩

theorem relIndex_eCentOf (hY : IsYFamily T Y) (hYM : Y ≤ M) {s : ℕ}
    (hs : Nat.card ↥(⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G)) = 2 ^ s) :
    (eCentOf T Y).relIndex (eOf T) = 2 ^ s := by
  obtain ⟨-, -, -, hE, hinf⟩ := h.five hY hYM
  set A := eCentOf T Y with hA
  set B := ⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (baum T : Set G) with hB
  have hEel : IsElemAbelian 2 (eOf T) := isElemAbelian_omegaOneCenterOf _
  have hAE : A ≤ eOf T := inf_le_left
  have hBE : B ≤ eOf T := hE ▸ le_sup_right
  have hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    isElemAbelian_comm hEel (hAE ha) (hBE hb)
  have h1 := card_sup_mul_card_inf_of_commute hc
  rw [← hE, hinf, Subgroup.card_bot, mul_one] at h1
  have h2 := Subgroup.relIndex_mul_card A (eOf T)
  rw [inf_eq_left.2 hAE, h1] at h2
  have hBc : Nat.card B = 2 ^ s := by
    rw [hB, ← h.commutator_inf_centralizer_thompsonJ hYM, hs]
  have hpos : 0 < Nat.card A := Nat.card_pos
  rw [← hBc]
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h2, mul_comm])

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
