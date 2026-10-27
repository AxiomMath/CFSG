module

public import CFSG.Quasithin.EmptyFaithful.S152L16
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S152UGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Inputs152 (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I : Subgroup G) : Prop where
  m_eq : ∀ M₁ : Subgroup G, InM T M₁ ↔ (M₁ = M ∨ M₁ = Mc)
  h159 : Lemma1519Concl T Mc M
  h13 : Lemma15213Concl T Mc M H
  h14 : Lemma15214Concl T Mc M B₀
  h11 : ∀ B ∈ sigmaPrime T H (V154 T Mc M), Lemma15211Concl T Mc M H B
  hN : Notation15209Concl T Mc M H
  h16 : Lemma15216Concl T Mc M H B₀ I
  h17 : (Nonempty (↥(autOn M (V154 T Mc M)) ≃* ↥(CFSG.Open.Sz 0)) ∨
      IsOmegaFourPlusOn M (V154 T Mc M)) ∧
    Nat.card (quasithinOmegaOneCenter T) = 2 ∧ (sOf152 T Mc M B₀).relIndex T = 2

section Basic

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem T_le_M152 (hs : Setting152 T Mc M) : T ≤ M := hs.mf.1.1.2

theorem isMaxTwoLocal_M152 (hs : Setting152 T Mc M) : quasithinIsMaxTwoLocal M := hs.mf.1.1.1

theorem T_ne_bot152 (hs : Setting152 T Mc M) : T ≠ ⊥ := by
  intro hT
  apply hs.qtfe.omegaOneCenter_ne_bot
  rw [eq_bot_iff]
  intro z hz
  have := (quasithinOmegaOneCenter_le_center T hz).1
  rw [hT] at this
  exact this

theorem zS_le_V152 (hs : Setting152 T Mc M) (B₀ : Subgroup (MulAut (V154 T Mc M))) :
    zSOf T Mc M B₀ ≤ V154 T Mc M :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    (((preOn_le _ _ _).trans (T_le_M152 hs)).trans (le_normalizer_V154 T Mc M))

theorem S_le_T152 : sOf152 T Mc M B₀ ≤ T := inf_le_left

theorem cv_le_inf152 (hs : Setting152 T Mc M) (hD : Inputs152 T Mc M H B₀ I) :
    M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ Mc ⊓ I := by
  intro x hx
  have hxZ : x ∈ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (zS_le_V152 hs B₀)) hx.2
  have h1 : x ∈ Mc ⊓ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
    rw [← hD.h16.centralizer_eq]
    exact hxZ
  exact hD.h16.centralizer_le h1

theorem S_le_inf152 (hD : Inputs152 T Mc M H B₀ I) : sOf152 T Mc M B₀ ≤ Mc ⊓ I :=
  le_sup_right.trans hD.h16.KS_le

theorem K_le_inf152 (hD : Inputs152 T Mc M H B₀ I) : oTwoUpper H ≤ Mc ⊓ I :=
  le_sup_left.trans hD.h16.KS_le

theorem S_le_I152 (hD : Inputs152 T Mc M H B₀ I) : sOf152 T Mc M B₀ ≤ I :=
  (S_le_inf152 hD).trans inf_le_right

theorem H_eq152 (hs : Setting152 T Mc M) (hH : IsHStar T M H) : H = oTwoUpper H ⊔ T :=
  eq_oTwoUpper_sup_of_isSylowTwoOf (isSylowTwoOf_of_le151 hs.qtfe.sylow hH.1.1)

theorem not_T_le_I152 (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hI : Hyp15215 T Mc M B₀ I) (hD : Inputs152 T Mc M H B₀ I) : ¬ T ≤ I := by
  intro hTI
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hI.inH.2
  have hTM' : InM T M' := ⟨hM'.1, hTI.trans hM'.2⟩
  rcases (hD.m_eq M').mp hTM' with hMM | hMM
  · have hKI : oTwoUpper H ≤ I := (K_le_inf152 hD).trans inf_le_right
    have hH' : H ≤ M := by
      rw [H_eq152 hs hH]
      refine sup_le ?_ (T_le_M152 hs)
      exact (hKI.trans hM'.2).trans hMM.le
    exact hH.2.1 hH'
  · exact hI.not_le (hM'.2.trans hMM.le)

theorem inf_T_I152 (hs : Setting152 T Mc M) (hH : IsHStar T M H) (hI : Hyp15215 T Mc M B₀ I)
    (hD : Inputs152 T Mc M H B₀ I) : T ⊓ I = sOf152 T Mc M B₀ := by
  have hS_le : sOf152 T Mc M B₀ ≤ T ⊓ I := le_inf S_le_T152 (S_le_I152 hD)
  rcases eq_or_eq_of_relIndex_two hS_le inf_le_left hD.h17.2.2 with h | h
  · exact h
  · exfalso
    apply not_T_le_I152 hs hH hI hD
    have := inf_le_right (a := T) (b := I)
    rwa [h] at this

theorem normalizer_S_le_M152 (hs : Setting152 T Mc M) (hD : Inputs152 T Mc M H B₀ I) :
    Subgroup.normalizer (sOf152 T Mc M B₀ : Set G) ≤ M := by
  have hbaum : baum T = baum (sOf152 T Mc M B₀) := baum_eq_of_le hD.h14.baum_le S_le_T152
  have hne : baum T ≠ ⊥ := C1GN.baum_ne_bot hs.qtfe.sylow.1 (T_ne_bot152 hs)
  intro x hx
  have h1 : x ∈ Subgroup.normalizer (baum (sOf152 T Mc M B₀) : Set G) :=
    normalizer_le_normalizer_baum _ hx
  rw [← hbaum] at h1
  have h2 : x ∈ CGS (baum T) := by
    have := inf_normalizer_le_cgsIn (H := (⊤ : Subgroup G)) (S := baum T) hne
    rw [top_inf_eq, cgsIn_top] at this
    exact this h1
  exact hD.h159.one_cgs h2

theorem card_zS152 (hB₀ : IsB0 T Mc M B₀) (hD : Inputs152 T Mc M H B₀ I) :
    Nat.card (zSOf T Mc M B₀) = 4 ∧ IsElemAbelian 2 (zSOf T Mc M B₀) := by
  obtain ⟨B, hB⟩ := hD.hN.sigmaPrime_nonempty
  have hZ := commutator_eq_zSOf hD.h13 hB₀ hB
  have h11 := hD.h11 B hB
  rw [← hZ]
  exact ⟨h11.card, h11.elemAbelian⟩

end Basic

end CFSG.Quasithin
