module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTSpec
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeFrame

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.E6ThreeModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem kgTw_conj_of_tspec {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {g₀ : ModGL Tag.E6 Ω} (hL : IsLang Fr g₀) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g₀ hζ D)
    {γ : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hγ : γ ∈ D.H) :
    ∃ (g : ModGL Tag.E6 Ω) (t : (Fin Tag.E6.rank → ZMod 3) → ModGL TwistTag.E6.tag K),
      IsLang Fr g ∧
      (∀ x, t x ∈ twistedE6InndiagGL K σ ∧
        baseChangeGL (algebraMap K Ω) (t x) = g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) ∧
      ∀ (x : Fin Tag.E6.rank → ZMod 3)
        (c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
        (((γ⁻¹ * D.ad x * γ) c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
          ModGL TwistTag.E6.tag K) = t x * (c : ModGL TwistTag.E6.tag K) * (t x)⁻¹ := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : RecipeExcLang.twInndiagGroup K σ,
      RecipeExcLang.twConj K σ w = γ := by
    have h : γ ∈ (RecipeExcLang.twConj K σ).range := by
      rw [← hD.H_eq]
      exact hγ
    exact MonoidHom.mem_range.mp h
  choose hx hDx using hD.diag_eq
  let e := twInndiagEquivRgrp hn hK σ hσ Fr hFr
  let y : (Fin Tag.E6.rank → ZMod 3) → ↥(TwistedDiag.Rgrp Ω Fr) :=
    fun x => ⟨g₀ * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g₀⁻¹, hx x⟩
  let wx : (Fin Tag.E6.rank → ZMod 3) → RecipeExcLang.twInndiagGroup K σ :=
    fun x => e.symm (y x)
  let t : (Fin Tag.E6.rank → ZMod 3) → ModGL TwistTag.E6.tag K :=
    fun x => ((w⁻¹ * wx x * w : RecipeExcLang.twInndiagGroup K σ) : ModGL TwistTag.E6.tag K)
  let W : ModGL Tag.E6 K := (w : ModGL TwistTag.E6.tag K)
  let B : (Fin Tag.E6.rank → ZMod 3) → ModGL Tag.E6 K :=
    fun x => (wx x : ModGL TwistTag.E6.tag K)
  let A : ModGL Tag.E6 Ω := baseChangeGL (τ := Tag.E6) (algebraMap K Ω) W
  let g : ModGL Tag.E6 Ω := A⁻¹ * g₀
  have hA_mem : A ∈ adjointGroup Tag.E6 Ω := by
    have h := ((TwistedDiag.mem_Rgrp Fr).1 (e w).2).1
    dsimp only [e, A] at h
    rw [twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr w] at h
    exact h
  have hA_fix : twistE6 Ω Fr A = A := by
    have h := ((TwistedDiag.mem_Rgrp Fr).1 (e w).2).2
    dsimp only [e, A] at h
    rw [twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr w] at h
    exact h
  have hwx : ∀ x, baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (B x) =
      g₀ * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g₀⁻¹ := by
    intro x
    have h2 : (↑(e (wx x)) : ModGL Tag.E6 Ω) =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (B x) :=
      twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr (wx x)
    have h3 : e (wx x) = y x := MulEquiv.apply_symm_apply e (y x)
    rw [← h2, h3]
  refine ⟨g, t, ?_, ?_, ?_⟩
  ·
    refine ⟨?_, ?_⟩
    · dsimp only [g]
      exact mul_mem (inv_mem hA_mem) hL.1
    · dsimp only [g]
      calc (A⁻¹ * g₀)⁻¹ * twistE6 Ω Fr (A⁻¹ * g₀)
          = g₀⁻¹ * twistE6 Ω Fr g₀ := by
            rw [map_mul, map_inv, hA_fix]
            group
        _ = TwistedDiag.n0 Ω := hL.2
  ·
    intro x
    refine ⟨?_, ?_⟩
    · exact twInndiagGroup_le_twistedE6InndiagGL σ (w⁻¹ * wx x * w).2
    · have h1 : baseChangeGL (algebraMap K Ω) (t x) =
          A⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (B x) * A := by
        change baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (W⁻¹ * B x * W) = _
        rw [map_mul, map_mul, map_inv]
      rw [h1, hwx x]
      dsimp only [g]
      rfl
  ·
    intro x c
    have hDad : D.ad x = RecipeExcLang.twConj K σ (wx x) := by
      rw [hDx x]
      change rgrpConjAut hn hK σ hσ Fr hFr (y x) = RecipeExcLang.twConj K σ (wx x)
      rw [← MulEquiv.apply_symm_apply e (y x)]
      exact rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr (wx x)
    have hmap : RecipeExcLang.twConj K σ (w⁻¹ * wx x * w) =
        (RecipeExcLang.twConj K σ w)⁻¹ * RecipeExcLang.twConj K σ (wx x) *
          RecipeExcLang.twConj K σ w := by
      rw [map_mul, map_mul, map_inv]
    have hconj : γ⁻¹ * D.ad x * γ = RecipeExcLang.twConj K σ (w⁻¹ * wx x * w) := by
      rw [← hw, hDad, hmap]
    rw [hconj]
    exact RecipeExcLang.coe_twConj σ (w⁻¹ * wx x * w) c

end CFSG.StandardType.KGL

end
