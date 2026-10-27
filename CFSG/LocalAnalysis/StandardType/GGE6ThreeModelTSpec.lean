module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

@[expose] def IsLang (g : ModGL Tag.E6 Ω) : Prop :=
  g ∈ adjointGroup Tag.E6 Ω ∧ g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω

structure TSpec (g : ModGL Tag.E6 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : Prop where
  H_eq : D.H = (RecipeExcLang.twConj K σ).range
  diag_eq : ∀ x : Fin Tag.E6.rank → ZMod 3,
    ∃ hx : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr,
      D.ad x = rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hx⟩
  tor_eq : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom), c ∈ D.Tor ↔
    baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) ∈
      (torusGroup Tag.E6 Ω).map (MulAut.conj g).toMonoidHom
  nb_eq : ∀ i, baseChangeGL (algebraMap K Ω) ((D.nb i : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
    g * weylElt Tag.E6 Ω i 1 * g⁻¹

theorem rgrpConjAut_baseChangeGL (x : ↥(TwistedDiag.Rgrp Ω Fr))
    (c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        (rgrpConjAut hn hK σ hσ Fr hFr x c).1 =
      x.1 * baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 * x.1⁻¹ := by
  have key : ∀ a b : ModGL TwistTag.E6.tag K,
      baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) (a * b * a⁻¹) =
        baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) a *
          baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) b *
            (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) a)⁻¹ := by
    intro a b
    rw [map_mul, map_mul, map_inv]
  obtain ⟨w, rfl⟩ := (twInndiagEquivRgrp hn hK σ hσ Fr hFr).surjective x
  rw [rgrpConjAut_apply_baseChange, RecipeExcLang.coe_twConj]
  exact key w.1 c.1

end CFSG.StandardType.E6ThreeModel
