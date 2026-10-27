module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RC0Input
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5FrameD
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynOrders
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5FrameO

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.Open CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup IsRoot permLattice)

section RC0

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.false_of_nontoral_twE6
    (hRC0 : LangNontoralCompField)
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .twistedE6 f) (hf : 1 ≤ f) (hp : p = 3)
    (act : TwE6Act G₀ B hf)
    (hnt : ¬ ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ d : ↥D, g⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam ⟨d, h.d_le d.2⟩ : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f)))) : False := by
  classical
  have htor : ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ d : ↥(⊥ : Subgroup X), g⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam ⟨d, (bot_le : (⊥ : Subgroup X) ≤ B) d.2⟩ :
            ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))) := by
    refine ⟨1, Subgroup.one_mem _, fun d => ?_⟩
    have hd : (⟨d, (bot_le : (⊥ : Subgroup X) ≤ B) d.2⟩ : ↥B) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp d.2)
    simp [hd]
  obtain ⟨S, hSq, -, fr, hΘ, hBimg, -, g₀, hg₀, hν⟩ :=
    exists_frameO_twE6_sub hf act (D := ⊥) bot_le htor
  let D' : Subgroup (ModGL Tag.E6 (AlgebraicClosure (GaloisField 2 (2 * f)))) :=
    fr.DimgO D
  let Dtw : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f)))) := D'
  have hD'model : fr.DimgO D ≤ S.D.model := fr.DimgO_le_BimgO.trans hBimg
  have hD'abel : IsElemAbelian 3 D' := by
    have hB3 : IsElemAbelian 3 B := by rw [← hp]; exact h.b_elem
    have hsub : IsElemAbelian 3 (D.subgroupOf B) :=
      (hB3.subgroupOf B).mono (Subgroup.subgroupOf_mono B h.d_le)
    exact hsub.map fr.ν
  have hD'card : Nat.card D' = 3 ^ 2 := by
    change Nat.card (fr.DimgO D) = 3 ^ 2
    rw [fr.card_DimgO h.d_le, h.d_card, hp]
  have hD'nt : ¬ ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ x ∈ Dtw, g⁻¹ * x * g ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))) := by
    rintro ⟨g, hg, hgD'⟩
    apply hnt
    refine ⟨g₀ * g, Subgroup.mul_mem _ hg₀ hg, fun d => ?_⟩
    have hmem : fr.ν ⟨d, h.d_le d.2⟩ ∈ Dtw :=
      Subgroup.mem_map.mpr ⟨⟨d, h.d_le d.2⟩, Subgroup.mem_subgroupOf.mpr d.2, rfl⟩
    have hconj := hgD' _ hmem
    rw [hν ⟨d, h.d_le d.2⟩] at hconj
    have hgoal : (g₀ * g)⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam ⟨d, h.d_le d.2⟩ : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * (g₀ * g) =
        g⁻¹ * (g₀⁻¹ * baseChangeGL
          (algebraMap (GaloisField 2 (2 * f)) (AlgebraicClosure (GaloisField 2 (2 * f))))
          ((act.lam ⟨d, h.d_le d.2⟩ : ↥(RecipeExcLang.twInndiagGroup (GaloisField 2 (2 * f))
            (frobQEquiv hf))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * g₀) * g := by
      group
    rw [hgoal]
    exact hconj
  have hJG : J ≤ G₀ := h.j_comp.1.trans inf_le_left
  have hcomp : CFSG.Open.IsComponentOf (fr.JimgO J)
      (S.Γ ⊓ Subgroup.centralizer (D' : Set (ModGL Tag.E6
        (AlgebraicClosure (GaloisField 2 (2 * f)))))) := by
    rw [← hΘ]
    exact fr.isComponentOf_JimgO h.b_norm h.d_le hJG
      (CFSG.Assembly.isComponentOf_iff_open.1 h.j_comp)
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic (GaloisField 2 (2 * f)) 2 (by
    rw [hSq, GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm])
  have hdisj := hRC0 (AlgebraicClosure (GaloisField 2 (2 * f))) 5 S hAlg D' hD'model hD'abel
    hD'card hD'nt (fr.JimgO J) hcomp
  rw [hSq] at hdisj
  obtain ⟨e⟩ := fr.nonempty_equiv_JimgO hJG h.j_comp.2.2
  obtain ⟨t', m, f', hlt, hmod, -⟩ := hF
  rcases hdisj with hfield | ⟨-, -, -, h6048⟩
  · have h2 := two_le_of_fieldExt (k := 1) h.j_comp.2.2 e (by rwa [mul_one])
      ⟨t', m, f', hlt, hmod⟩
    omega
  · exact (CFSG.LocalAnalysis.GLTheoremA.I141F.Ord.card_ne_6048_of_lieModel hmod)
      ((Nat.card_congr e.toEquiv).trans h6048)

end RC0

end CFSG.StandardType.TableCRes

end
