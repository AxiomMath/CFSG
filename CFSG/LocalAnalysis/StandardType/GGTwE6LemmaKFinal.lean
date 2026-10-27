module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKBook
public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKAsm
public import CFSG.LocalAnalysis.StandardType.GGTwE6SigmaTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRetype

public noncomputable section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.E6Descent CFSG.Open CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.StandardType.NoOffTwE6Three (GGTwE6ThreeToralTypeMinusOneInput)
open CFSG.StandardType.TableBExc.E6Three (zetaVec)

section Final


theorem exists_lang_typeMinusOne_of_toral {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) (Ω : Type)
    [Field Ω] [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {X : Subgroup (ModGL Tag.E6 Ω)} (hXR : X ≤ TwistedDiag.Rgrp Ω Fr) (hX3 : IsElemAbelian 3 X)
    (hcard : 3 ^ 4 ≤ Nat.card X) (hXt : NoOffTwE6Three.IsToralE6 Ω X) :
    ∃ g ∈ adjointGroup Tag.E6 Ω, g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω ∧
      ∀ x ∈ X, ∃ v, x = g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (GaloisField 2 (2 * f))
  have : CharP Ω 2 := charP_of_injective_algebraMap
    (algebraMap (GaloisField 2 (2 * f)) Ω).injective 2
  obtain ⟨v₀, g₀, hg₀, hg₀F, hA⟩ :=
    TwE6SigmaTorus.exists_sigmaTorus_of_toral hf Ω Fr hFr hXR hXt
  obtain ⟨a, ha, haζ, hw⟩ :=
    exists_family_of_toral_data lemmaKCheck h3 Fr hFr hζ hζo hX3 hcard hA
  have hFr' : Fr = iterateFrobenius Ω 2 f := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def]
  subst hFr'
  obtain ⟨z, hz, hzF⟩ : ∃ z ∈ familyGroup (K := Ω) a,
      (g₀ * z)⁻¹ * twistE6 Ω (iterateFrobenius Ω 2 f) (g₀ * z) = TwistedDiag.n0 Ω :=
    LangRetype.exists_lang_retype_twisted (L := Ω) 2 TwistTag.E6 f hf a
      (g₀ := g₀) (v := v₀) (w := twE6W0) (inv_mul_eq_iff_eq_mul.1 hg₀F)
      (fun s => by
        have h1 := (hA (s : ModGL Tag.E6 Ω) s.2).2
        rw [← ha s] at h1
        exact h1) hw
  have hzc := mem_familyCentralizer.1 (familyGroup_le_familyCentralizer a hz)
  refine ⟨g₀ * z, mul_mem hg₀ hzc.1, hzF, fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := haζ ⟨x, hx⟩
  refine ⟨v, ?_⟩
  have hd : rootDiagUnit Tag.E6 (zetaVec ζ hζ v) = g₀⁻¹ * x * g₀ := by
    rw [← hv]
    exact ha ⟨x, hx⟩
  have hc := hzc.2 ⟨x, hx⟩
  rw [hv] at hc
  have hzd : z * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * z := by
    calc z * rootDiagUnit Tag.E6 (zetaVec ζ hζ v)
        = (rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * z * (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹) *
            rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by rw [hc]
      _ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * z := by group
  calc x = g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ := by group
    _ = g₀ * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g₀⁻¹ := by rw [← hd]
    _ = g₀ * z * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * (g₀ * z)⁻¹ := by
        have e : g₀ * z * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * (g₀ * z)⁻¹ =
            g₀ * (z * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * z⁻¹) * g₀⁻¹ := by group
        rw [e, hzd]
        group

theorem ggTwE6ThreeToralTypeMinusOneInput : GGTwE6ThreeToralTypeMinusOneInput := by
  intro f hf h3 Ω _ _ _ Fr hFr ζ hζ hζo X hXR hX3 hcard hXt
  exact exists_lang_typeMinusOne_of_toral hf h3 Ω Fr hFr hζ hζo hXR hX3 hcard.ge hXt

end Final

end CFSG.StandardType.TwE6LemmaK
