module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5TwSurvivor
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RC0
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Act
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5L2Rank
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Centre
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5InnerL
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5InnerO
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Order

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.StandardType CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem rstarTwE6
    (hR : LangFamilyCompFieldSL) (hL : LangFamilyCompLabel)
    (hG : GGTCInputG6InnerDiagLangTw) (hRC0 : LangNontoralCompField)
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .twistedE6 f) (hp : p = 3) :
    f = 1 ∧ LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 3 ∧ Nat.card B ≤ 3 ^ 4 := by
  classical
  have hf : 1 ≤ f := h.adm.2.1
  obtain ⟨act⟩ := h.exists_act_twE6 hf
  by_cases htor : ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ d : ↥D, g⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam ⟨d, h.d_le d.2⟩ : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f)))
  · obtain ⟨hf1, hmodJ, -⟩ := GGTCHyp.survivor_twE6 hR hL hG h hF hp hf act htor
    have hJperf : Group.IsPerfect ↥J :=
      Group.isPerfect_def.mpr (Assembly.isComponentOf_iff_open.1 h.j_comp).2.2.1
    have hB3 : IsElemAbelian 3 B := hp ▸ h.b_elem
    have hD9 : Nat.card D = 3 ^ 2 := hp ▸ h.d_card
    exact ⟨hf1, hmodJ, tcCard_le_of_L2 (by norm_num) hJperf hB3 h.j_norm h.j_cent hD9 hmodJ⟩
  · exact (GGTCHyp.false_of_nontoral_twE6 hRC0 h hF hf hp act htor).elim

theorem rstarTwE6_L
    (hR : LangFamilyCompFieldSL) (hL : LangFamilyCompLabel)
    (hG : GGTCInputG6InnerDiagLangTw) (hRC0 : LangNontoralCompField)
    (hA : TwE6q2OrderThreeCentralizers)
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .twistedE6 f) (hp : p = 3) (hf : f = 1)
    (hB : Nat.card B = 3 ^ 4) (hJ : LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 3) :
    LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 := by
  classical
  have _hJ := hJ
  have hf1 : 1 ≤ f := h.adm.2.1
  obtain ⟨act⟩ := h.exists_act_twE6 hf1
  by_cases htor : ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ d : ↥D, g⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam ⟨d, h.d_le d.2⟩ : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf1))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f)))
  · obtain ⟨-, -, hlab⟩ := GGTCHyp.survivor_twE6 hR hL hG h hF hp hf1 act htor
    have hZ : Subgroup.center ↥G₀ = ⊥ := h.center_eq_bot_twE6 hp
    have hin := h.lam_mem_inner_twE6 hp hf1 hf hB.le hZ act
    obtain ⟨g, hg, hg3, -, hLg⟩ := h.exists_inner_order_three_twE6 hp hf1 hZ act hin
    exact h.psu_six_of_order_three_twE6 hA hf hZ hg hg3 hLg hlab
  · exact (GGTCHyp.false_of_nontoral_twE6 hRC0 h hF hf1 hp act htor).elim

end CFSG.StandardType.TableCRes

end
