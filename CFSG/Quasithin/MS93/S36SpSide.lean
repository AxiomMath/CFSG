module

public import CFSG.Quasithin.MS93.S36SpQP
public import CFSG.Quasithin.MS93.S36Sp5c

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}

theorem relIndex_le_of_idx' (d : SpFrame h) {χ : MulAut ↥T}
    (hcrit : ¬ tImage χ (Z0q M T) ≤ pCoreOf 2 M)
    (hidx' : (tImage χ (pCoreOf 2 M)).relIndex (Z0q M T) ≤ 2 ^ d.k) :
    (pCoreOf 2 M).relIndex (tImage χ (Z0q M T)) ≤ 2 ^ d.k := by
  have hEM : tImage χ (Z0q M T) ≤ M := tImage_le_M h χ _
  have hE := actsMat_E_of (d := d) hidx'
  have hV4 := d.card_V4_eq hEM hE
  set r := Module.finrank d.F (fixSp (d.img _ hEM hE)) with hr
  have hfix : Nat.card (fixSp (d.img _ hEM hE)) = (2 ^ d.k) ^ r := by
    rw [card_fixSp, d.card_F]
  rw [card_V4, d.card_F, hfix] at hV4
  have hq : 1 < 2 ^ d.k := Nat.one_lt_two_pow (by have := d.one_le; omega)
  have hr3 : 3 ≤ r := by
    have h1 : (2 ^ d.k) ^ 4 ≤ (2 ^ d.k) ^ (r + 1) :=
      calc (2 ^ d.k) ^ 4 = (2 ^ d.k) ^ r *
            (Subgroup.centralizer (tImage χ (Z0q M T) : Set G)).relIndex (Uq M T L) := hV4
        _ ≤ (2 ^ d.k) ^ r * 2 ^ d.k :=
            Nat.mul_le_mul_left _ (relIndex_centralizer_le_of hidx')
        _ = (2 ^ d.k) ^ (r + 1) := by rw [pow_succ]
    have := (Nat.pow_le_pow_iff_right hq).1 h1
    omega
  have hr4 : r ≤ 4 := by
    have := Submodule.finrank_le (fixSp (d.img _ hEM hE))
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
  have hne : d.img _ hEM hE ≠ ⊥ := by
    intro hb
    apply hcrit
    have h1 := d.card_img hEM hE (tImage_le χ _)
    rw [hb, Subgroup.card_bot, eq_comm, Subgroup.relIndex_eq_one] at h1
    exact h1
  have hr' : r = 3 := by
    rcases (show r = 3 ∨ r = 4 by omega) with h3 | h4
    · exact h3
    · exfalso
      apply hne
      apply fixSp_eq_top_iff.1
      apply Submodule.eq_top_of_finrank_eq
      rw [← hr, h4, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨p, hp, -, hle⟩ := exists_point_of_finrank_fixSp_three hr'
  rw [← d.card_img hEM hE (tImage_le χ _), ← d.card_F, ← card_xPoint hp]
  exact Subgroup.card_le_of_le hle

namespace PairHyp

variable {d : SpFrame h} {χ : MulAut ↥T} (hp : PairHyp d χ)
include hp

theorem idx'_eq : (tImage χ (pCoreOf 2 M)).relIndex (Z0q M T) = 2 ^ d.k := by
  obtain ⟨v, hx⟩ := hp.exists_xData
  have hEM : tImage χ (Z0q M T) ≤ M := tImage_le_M h χ _
  have hE := hp.actsMat_E
  have hV4 := d.card_V4_eq hEM hE
  have h3 : Module.finrank d.F (perp (d.F ∙ v)) = 3 := by
    have := finrank_perp (d.F ∙ v)
    rw [finrank_span_singleton hx.ne] at this
    omega
  rw [hx.img_eq hEM hE, card_V4, d.card_F, card_fixSp, d.card_F,
    fixSp_xPoint (isPoint_span hx.ne), h3] at hV4
  have hpos : 0 < (2 ^ d.k) ^ 3 := by positivity
  have hrel :
      (Subgroup.centralizer (tImage χ (Z0q M T) : Set G)).relIndex (Uq M T L) = 2 ^ d.k := by
    have : (2 ^ d.k) ^ 3 * 2 ^ d.k = (2 ^ d.k) ^ 3 *
        (Subgroup.centralizer (tImage χ (Z0q M T) : Set G)).relIndex (Uq M T L) := by
      rw [← hV4]
      ring
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  refine le_antisymm hp.idx' ?_
  rw [← hrel]
  exact (Subgroup.relIndex_le_of_le_left (tImage_pCoreOf_le_centralizer h χ)
    Subgroup.index_ne_zero_of_finite).trans
    (Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) Subgroup.index_ne_zero_of_finite)

omit hp in
theorem relIndex_tImage_inv_eq (h : PUHyp M T L) {K : Subgroup G} (hKT : K ≤ T) :
    (tImage χ⁻¹ (pCoreOf 2 M)).relIndex K = (pCoreOf 2 M).relIndex (tImage χ K) := by
  rw [← relIndex_tImage χ hKT, tImage_tImage_inv χ h.pCore_le]

theorem endSide (hp' : PairHyp d χ⁻¹) : ∃ Y : Subgroup G, EndSide M T L d.k χ⁻¹ Y := by
  obtain ⟨v, hx⟩ := hp.exists_xData
  obtain ⟨v', hx'⟩ := hp'.exists_xData
  have hE := hp.actsMat_E
  have hYcT : Yc d χ v ≤ T := Yc_le.trans (inf_le_right.trans (tImage_le _ _))
  set Y := tImage χ⁻¹ (Yc d χ v) with hYdef
  have hYT : Y ≤ T := tImage_le _ _
  have hYQT : ⁅Y, pCoreOf 2 M⁆ ≤ T := commutator_le_of_le hYT h.pCore_le
  have hcommY : tImage χ ⁅Y, pCoreOf 2 M⁆ = ⁅Yc d χ v, tImage χ (pCoreOf 2 M)⁆ := by
    rw [tImage_commutator χ hYT h.pCore_le, hYdef, tImage_tImage_inv χ hYcT]
  have hCT : Uq M T L ⊓ Zq M L ≤ T :=
    inf_le_left.trans ((Uq_le_Z0q h.L_le).trans (Z0q_le_T h))
  have hKcT : Kc d χ v ≤ T := Kc_le_Uq.trans ((Uq_le_Z0q h.L_le).trans (Z0q_le_T h))
  refine ⟨Y, hp'.crit', hp'.crit, hp'.idx'_eq, fun hk => (hp'.Kc_eq hk hx').2.2.2,
    fun hk => (hp'.Kc_eq hk hx').2.2.1, ?_, ?_, fun hk => ?_, hp.not_le_normalClosure hx,
    fun K hKT hK => ?_, fun K hKT _ hK hidx => ?_, fun hk t ht => ?_, fun hk => ?_⟩
  · rw [← tImage_omegaOneCenterOf χ⁻¹]
    exact S36SP.tImage_mono χ⁻¹ omegaOneCenterOf_le_Yc
  · have := S36SP.tImage_mono χ⁻¹ (Yc_le (d := d) (χ := χ) (v := v))
    rwa [tImage_inf, tImage_inv_tImage χ h.pCore_le] at this
  · refine (tImage_le_tImage_iff χ hYQT).1 ?_
    rw [hcommY, ← (hp.Kc_eq hk hx).1]
    exact commutator_Yc_le
  · have h1 : ⁅tImage χ (pCoreOf 2 M), tImage χ K⁆ ≤ tImage χ (Z0q M T) := by
      rw [← tImage_commutator χ h.pCore_le hKT]
      exact S36SP.tImage_mono χ hK
    rw [relIndex_tImage_inv_eq h hKT]
    exact hp.relIndex_le hx (tImage_le χ K) h1
  · have h1 : ⁅tImage χ (pCoreOf 2 M), tImage χ K⁆ ≤ tImage χ (Z0q M T) := by
      rw [← tImage_commutator χ h.pCore_le hKT]
      exact S36SP.tImage_mono χ hK
    rw [relIndex_tImage_inv_eq h hKT] at hidx
    have h2 := S36SP.tImage_mono χ⁻¹ (hp.commutator_le_of_relIndex hx (tImage_le χ K) h1 hidx)
    rwa [tImage_commutator χ⁻¹ (tImage_le _ _) (Z0q_le_T h), tImage_inv_tImage χ h.pCore_le,
      tImage_commutator χ⁻¹ (tImage_le _ _) (Z0q_le_T h), tImage_inv_tImage χ hKT] at h2
  · obtain ⟨g, hg⟩ := actsMat_P hx' t ht
    exact d.key hk t (tImage_le_M h χ⁻¹ _ ht) (pow_eq_one_of_mem_T h (tImage_le _ _ ht)) g hg
  · obtain ⟨hKcen, hKC, -⟩ := hp.Kc_two hk hx
    refine ⟨tImage χ⁻¹ (Kc d χ v), ?_, S36SP.tImage_mono χ⁻¹ Kc_le_Uq, ?_, ?_⟩
    · refine (tImage_le_iff χ hYQT hKcT).1 ?_
      rw [hcommY]
      exact commutator_Yc_le
    ·
      have hDT : Dq M L ≤ T := inf_le_left.trans h.pCore_le
      have hL : tImage χ⁻¹ (Kc d χ v) ≤ Subgroup.centralizer (L : Set G) := by
        have := S36SP.tImage_mono χ⁻¹ (Kc_le_tImage_Dq (d := d) (χ := χ) (v := v))
        rw [tImage_inv_tImage χ hDT] at this
        exact this.trans inf_le_right
      have hT : tImage χ⁻¹ (Kc d χ v) ≤ Subgroup.centralizer (T : Set G) := by
        have h1 : Kc d χ v ≤ T ⊓ Subgroup.centralizer (T : Set G) := le_inf hKcT hKcen
        have h2 := S36SP.tImage_mono χ⁻¹ h1
        rw [← tImage_centralizer χ⁻¹ le_rfl, tImage_self] at h2
        exact h2.trans inf_le_right
      intro x hx₁
      rw [Subgroup.mem_centralizer_iff]
      have hcent : M ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [h.eq_sup]
        refine sup_le (fun l hl => ?_) (fun t ht => ?_) <;>
          rw [Subgroup.mem_centralizer_singleton_iff]
        · exact (Subgroup.mem_centralizer_iff.1 (hL hx₁) l hl)
        · exact (Subgroup.mem_centralizer_iff.1 (hT hx₁) t ht)
      exact fun m hm => Subgroup.mem_centralizer_singleton_iff.1 (hcent hm)
    · rw [← tImage_inf, inf_comm, hKC]
      exact (tImage_eq_bot_iff χ⁻¹ bot_le).2 rfl

theorem endCommon (hsp4 : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) d.k) :
    EndCommon M T L d.k := by
  obtain ⟨v, hx⟩ := hp.exists_xData
  refine ⟨hsp4, ?_, hp.hXL⟩
  rcases (show d.k = 1 ∨ 2 ≤ d.k by have := d.one_le; omega) with hk | hk
  · rw [(hp.Kc_two hk hx).2.2, hk, pow_one]
  · exact (hp.Kc_eq hk hx).2.1

end PairHyp

end CFSG.Quasithin.MS93.S36SP
