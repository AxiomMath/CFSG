module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Act
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5LangFrame

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)

section FrameO

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.exists_frameO_twE6
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hf : 1 ≤ f) (hp : p = 3) (act : TwE6Act G₀ B hf)
    (htor : ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ b : ↥B, g⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam b : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f)))) :
    ∃ S : LangSetup Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f))) 5, S.D.q = 2 ^ f ∧
      ∃ fr : GGTCUFrameO G₀ B (ModGL Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f)))),
        fr.Θ.range = S.Γ ∧ fr.BimgO ≤ S.D.torus := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : GaloisField 2 (2 * f), frobQEquiv hf c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  have : Nontrivial ↥B := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc (1 : ℕ) < 3 ^ 4 := by norm_num
      _ ≤ Nat.card B := by simpa [hp] using h.b_card
  obtain ⟨S, ι, ν, hq, hιinj, hιrange, hνinj, hνT, hlaw⟩ :=
    exists_langFrame_twE6 hf hK (frobQEquiv hf) hσ (N := ↥B) act.lam act.lam_inj htor
  refine ⟨S, hq, ?_, ?_, ?_⟩
  · exact ⟨ι.comp act.θ.toMonoidHom, hιinj.comp act.θ.injective, ν, hνinj,
      fun b y y' hy' =>
        hlaw b (act.θ (QuotientGroup.mk y)) (act.θ (QuotientGroup.mk y'))
          (act.act b y y' hy')⟩
  · change (ι.comp act.θ.toMonoidHom).range = S.Γ
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 act.θ.surjective, Subgroup.map_top,
      hιrange]
  · rintro _ ⟨b, rfl⟩
    exact hνT b

end FrameO

end CFSG.StandardType.TableCRes

end
