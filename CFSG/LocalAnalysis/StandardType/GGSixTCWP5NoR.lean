module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Act
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Toral
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5FrameO
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Rank

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)

section NoR

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem rstarTwE6_noR
    (hR : LangFamilyCompFieldSL) (hL : LangFamilyCompLabel)
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (_hF : GGSixLSevenFieldExtCase J .twistedE6 f) (hp : p = 3) (hf : f = 1)
    (hB : Nat.card B = 3 ^ 4) (hJ : LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 3) :
    ∀ R : Subgroup X, IsPGroup 2 R → R ≤ G₀ → B ≤ Subgroup.normalizer (R : Set X) → R = ⊥ := by
  intro R hR2 hRG hBR
  by_contra hR1
  have hf1 : 1 ≤ f := h.adm.2.1
  obtain ⟨act⟩ := h.exists_act_twE6 hf1
  obtain ⟨g, hg, hgT⟩ :=
    h.toral_twE6 hf1 hp (by rw [hf]; norm_num) hB.ge act hR1 hR2 hRG hBR
  obtain ⟨S, -, fr, hΘ, hBT⟩ := h.exists_frameO_twE6 hf1 hp act ⟨g, hg, hgT⟩
  have hbound := uframeO_conclude_psl28 (uFieldInput_of_SL hR (Or.inl rfl)) hL
    h.prime h.ne_two (K := GaloisField 2 (2 * f)) S fr hΘ hBT h.b_norm h.b_elem h.d_le
    h.d_card (h.j_comp.1.trans inf_le_left)
    (CFSG.Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent hJ
  rw [hB, hp] at hbound
  norm_num at hbound

end NoR

end CFSG.StandardType.TableCRes

end
