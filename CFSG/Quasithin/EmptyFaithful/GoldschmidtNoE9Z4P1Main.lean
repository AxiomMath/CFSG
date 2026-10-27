module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Cen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Off
public import CFSG.Quasithin.EmptyFaithful.S14612GB0a
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Pl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Dat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9z4_lemma_14_6_13 (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) :
    ∃ g : G, g ∉ mcOf T ∧ conjClosure (VZ T M) H ≤ conjSub g⁻¹ H ∧
      conjSub g⁻¹ (conjClosure (VZ T M) H) ≤ H ∧
      ∀ R : Subgroup G, IsPlaneSub T M H PQ R →
        conjSub g⁻¹ (conjClosure (VZ T M) H) ≤ Subgroup.normalizer (uHi T M H R : Set G) ∧
          ¬ ⁅uHi T M H R, conjSub g⁻¹ (uK T M H)⁆ ≤ quasithinOmegaOneCenter T := by
  classical
  have hcls : ClassAutShapeStmt := classAutShapeStmt
  have hH : IsHTM T M H := hred.isHTM
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  obtain ⟨hF81, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  obtain ⟨γ, γ', g₀, hs⟩ := F8.exists_F8Setup hF81
  have hlt := Dγ_lt_Uγ_of_shape hcls h35 S hred hshape hs
  obtain ⟨δ, δ', k, sk, -, -, hQ⟩ := h98.lemma_14_5_18_four hs hlt
  obtain ⟨hUkH, hUle⟩ := S.le_of_setup hH sk
  have hkg := S.g_not_mem_of_setup hH sk
  have hZZ : conjSub (k : G) (quasithinOmegaOneCenter T) ⊓ quasithinOmegaOneCenter T = ⊥ := by
    rw [inf_comm]
    exact F8.F87_5b hF81 sk
  obtain ⟨hsplit, -, -⟩ := shape_splitting h35 S hred h98
  have hstr := e9z4Str_of_shape hcls h35 S hred hshape h98
  have hUkH' : conjSub (k : G) (conjClosure (VZ T M) H) ≤ H := hUkH
  obtain ⟨x, hxUk, hx2, hall⟩ :=
    exists_involution_of_autOn_Qset hcls h35 S hred hshape h98 hUkH' hQ
  have hbx : orderOf (resBeta (rhoH h98.toHypF91) x) = 2 := (orderOf_resBeta_eq hsplit x).trans hx2
  refine ⟨(k : G)⁻¹, fun hmem => hkg (by simpa using (mcOf T).inv_mem hmem), ?_, ?_, ?_⟩
  · rw [inv_inv]
    exact hUle
  · rw [inv_inv]
    exact hUkH
  intro R hR
  obtain ⟨Q, hQP, hQ3, hrk, rfl⟩ := hR.exists_HLb S hred h98 hsplit
  have hQrange : Q ≤ (resBeta (rhoH h98.toHypF91)).range := hQP.trans (Subgroup.map_le_range _ _)
  rw [inv_inv]
  refine ⟨fun y hy => ?_, fun hcontra => ?_⟩
  · have hyH : y ∈ H := hUkH hy
    rcases hall ⟨y, hyH⟩ hy with h1 | h1
    · have hβ : resBeta (rhoH h98.toHypF91) ⟨y, hyH⟩ = 1 := by
        rw [← map_one (resBeta (rhoH h98.toHypF91))]
        exact resBeta_eq_of_rhoH_eq hsplit (by rw [h1, map_one])
      exact mem_normalizer_uHi_HLb S hH h98.toHypF91 (y := ⟨y, hyH⟩) (by rw [hβ, conjBy_one])
    · have hβ := resBeta_eq_of_rhoH_eq hsplit h1
      exact mem_normalizer_uHi_HLb S hH h98.toHypF91 (y := ⟨y, hyH⟩)
        (by rw [hβ]; exact hstr.conjBy_eq_of_involution ⟨x, rfl⟩ hbx hQP)
  · obtain ⟨k₀, hk₀, hmove⟩ := exists_move_plane_rho hsplit hstr hx2 hQP hQ3 hrk
    obtain ⟨u, hu, hnc⟩ := exists_comm_not_mem_Z h98.toHypF91 hsplit hQrange hk₀ hmove
    have hK : conjSub (k : G) (uK T M H) ≤
        centralizerMod (quasithinOmegaOneCenter T) H
          (uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q)) := by
      intro w hw
      have hwH : w ∈ H :=
        hUkH (conjSub_mono (k : G) (le_sup_left.trans (uK_sup_Z_le_conjClosure T M H)) hw)
      refine ⟨hwH, hHN hwH, fun b hb => ?_⟩
      have h1 : ⁅b, w⁆ ∈ quasithinOmegaOneCenter T :=
        hcontra (Subgroup.commutator_mem_commutator hb hw)
      have e : w * b * w⁻¹ * b⁻¹ = (⁅b, w⁆)⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact (quasithinOmegaOneCenter T).inv_mem h1
    have hU := conjSub_U_le_centralizerMod hcls h35 S hred hshape h98 hUkH' hUle hZZ
      (uHi_le_conjClosure (HLb_le Q)) hK
    exact hnc ((hU hxUk).2.2 u hu)

end CFSG.Quasithin
