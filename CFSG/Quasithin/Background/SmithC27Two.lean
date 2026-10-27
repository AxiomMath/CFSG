module

public import CFSG.Quasithin.Background.SmithC27One
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

omit [Finite G] in
theorem normalizer_le_normalizer_thompsonJ (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have e : B6.conjSub g S = S := B6.conjSub_eq_self hg
  have := B6.thompsonJ_conjSub S g
  rw [e] at this
  exact this.symm

namespace Hyp27

theorem omegaOneCenterOf_le_R (h : Hyp27 H R M K) :
    omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) ≤ R :=
  (A4.omegaOneCenterOf_le _).trans h.pCoreOf_sup_le

theorem le_of_thompsonJ_le (h : Hyp27 H R M K) (hJ : thompsonJ R ≤ pCoreOf 2 (K ⊔ R)) :
    K ≤ M := by
  have heq : thompsonJ (pCoreOf 2 (K ⊔ R)) = thompsonJ R :=
    B6.thompsonJ_eq_of_le hJ h.pCoreOf_sup_le
  have hJne : thompsonJ R ≠ ⊥ := CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot h.isPGroup h.R_ne_bot
  have hXJ : K ⊔ R ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
    rw [← heq]
    exact (le_normalizer_pCoreOf 2 (K ⊔ R)).trans (normalizer_le_normalizer_thompsonJ _)
  intro x hx
  refine h.hyp.cgs ?_
  exact inf_normalizer_le_cgsIn_of_char (B6.thompsonJ_le R) hJne
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ R)
    ⟨h.K_le hx, hXJ (Subgroup.mem_sup_left hx)⟩

theorem not_thompsonJ_le (h : Hyp27 H R M K) :
    ¬ thompsonJ R ≤ thompsonJ (pCoreOf 2 (K ⊔ R)) := fun hJ =>
  h.not_le (h.le_of_thompsonJ_le (hJ.trans (B6.thompsonJ_le _)))

theorem exists_isMaxElemAbelian_not_le_centralizer (h : Hyp27 H R M K) :
    ∃ A : Subgroup G, IsMaxElemAbelian R A ∧
      ¬ A ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) := by
  by_contra hne
  push Not at hne
  apply h.not_le
  apply h.le_of_thompsonJ_le
  refine h.le_pCoreOf_of_le_inf_centralizer (le_inf ?_ ?_)
    (h.isPGroup.to_le (B6.thompsonJ_le R))
  · exact (B6.thompsonJ_le R).trans le_sup_right
  · exact iSup₂_le fun A hA => hne A hA

theorem isFFModule_and_offender (h : Hyp27 H R M K) :
    @IsFFModule (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))
        (commGroupOfElemAbelian (isElemAbelian_omegaOneCenterOf _))
        (autOn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ∧
      ∃ A : Subgroup (MulAut ↥(omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))),
        A ≤ autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ∧
        @IsFFStarOffender (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))
          (commGroupOfElemAbelian (isElemAbelian_omegaOneCenterOf _))
          (autOn (K ⊔ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) A := by
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hVdef
  have hV : IsElemAbelian 2 V := isElemAbelian_omegaOneCenterOf _
  obtain ⟨A, hA, hAc⟩ := h.exists_isMaxElemAbelian_not_le_centralizer
  have hAX : A ≤ K ⊔ R := hA.1.trans le_sup_right
  have hXV : K ⊔ R ≤ Subgroup.normalizer (V : Set G) := le_normalizer_omegaOneCenterOf_pCoreOf _
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := hAX.trans hXV
  have hVR : V ≤ R := h.omegaOneCenterOf_le_R
  refine ⟨isFFModule_autOn hV hVR hXV hAX hA hAc, ?_⟩
  let _ : CommGroup V := commGroupOfElemAbelian hV
  have hA2 : IsA2 (autOn (K ⊔ R) V) (autOn A V) :=
    ⟨autOn_le_autOn V hAX, autOn_ne_bot_of_not_le_centralizer hAn hAc,
      isElemAbelian2_autOn hV hA.2.1 hAn⟩
  have hcard : Nat.card V + 0 ≤ Nat.card (autOn A V) * Nat.card (fixV (autOn A V)) := by
    rw [add_zero, card_autOn_eq_relIndex hAn, card_fixV_autOn_eq hV hAn]
    exact card_le_relIndex_mul_card hV hVR hA
  obtain ⟨B, hBA, hB, -⟩ := B1.exists_offender_below hA2 0 hcard
  exact ⟨B, hBA.trans (autOn_le_autOn V hA.1), hB⟩

end Hyp27

theorem c27_two (h : Hyp27 H R M K) : C27Two R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
  ⟨h.not_thompsonJ_le, isElemAbelian_omegaOneCenterOf _, h.isFFModule_and_offender⟩

end CFSG.Quasithin.SmithC27
