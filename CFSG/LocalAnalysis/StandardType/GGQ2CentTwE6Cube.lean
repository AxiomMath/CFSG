module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelCentE
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwoCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri

public section

namespace CFSG.StandardType.GGQ2CentPort.Q2TwE6

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.E6ThreeModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open

theorem cube_eq_one_of_commute_hypE6
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2) {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hgF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ v, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t v) =
      g * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ v) * g⁻¹)
    {r : ModGL TwistTag.E6.tag K} (hr : r ∈ twistedE6RootGroup K σ)
    (hc : ∀ v ∈ NoOffRest.hypE6, t v * r = r * t v) : r ^ 3 = 1 := by
  classical
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let r' : ModGL TwistTag.E6.tag (AlgebraicClosure K) := baseChangeGL f r
  let n0 : ModGL TwistTag.E6.tag (AlgebraicClosure K) := TwistedDiag.n0 (AlgebraicClosure K)
  let u : ModGL TwistTag.E6.tag (AlgebraicClosure K) := g⁻¹ * r' * g
  have hrGF : r ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    simpa [twistedE6RootGroup] using hr
  have hrTF : r ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hrGF
  have hrAdj : r ∈ adjointGroup TwistTag.E6.tag K :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom hrTF
  have hfσ : ∀ c : K, f (σ c) = Fr (f c) := by
    intro c
    rw [hσ c, map_pow, hFr]
  have hr'TF : r' ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    CFSG.StandardType.TableBExcSmallRanks.baseChangeGL_mem_twistedFixedGroup
      TwistTag.E6 f σ.toRingHom Fr hfσ hrTF
  have hr'Adj : r' ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).mp hr'TF).1
  have hr'fix : twistHom TwistTag.E6 (AlgebraicClosure K) Fr r' = r' :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).mp hr'TF).2
  have huAdj : u ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mul_mem (mul_mem (inv_mem hg) hr'Adj) hg
  have hcomm : ∀ v ∈ NoOffRest.hypE6,
      rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ v) * u *
          (rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ v))⁻¹ = u := by
    intro v hv
    let d : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
      rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ v)
    have htv : baseChangeGL f (t v) = g * d * g⁻¹ := by
      simpa [f, d] using ht v
    have hbc : (g * d * g⁻¹) * r' = r' * (g * d * g⁻¹) := by
      have h := congrArg (baseChangeGL f) (hc v hv)
      rw [map_mul, map_mul, htv] at h
      simpa [r'] using h
    have hdu : d * u = u * d := by
      calc d * u = g⁻¹ * ((g * d * g⁻¹) * r') * g := by
            change d * (g⁻¹ * r' * g) = g⁻¹ * ((g * d * g⁻¹) * r') * g
            group
        _ = g⁻¹ * (r' * (g * d * g⁻¹)) * g := by rw [hbc]
        _ = u * d := by
            change g⁻¹ * (r' * (g * d * g⁻¹)) * g = (g⁻¹ * r' * g) * d
            group
    calc d * u * d⁻¹ = (u * d) * d⁻¹ := by rw [hdu]
      _ = u := by group
  have huT : u ∈ torusGroup Tag.E6 (AlgebraicClosure K) :=
    mem_torusGroup_of_commute_zetaVec (k := AlgebraicClosure K) hζo hζ huAdj hcomm
  have htheta : TwistedDiag.theta Fr u = u := by
    have hmap : twistHom TwistTag.E6 (AlgebraicClosure K) Fr u = n0⁻¹ * u * n0 := by
      calc twistHom TwistTag.E6 (AlgebraicClosure K) Fr u
          = (g * n0)⁻¹ * r' * (g * n0) := by
            change twistHom TwistTag.E6 (AlgebraicClosure K) Fr (g⁻¹ * r' * g) = _
            rw [map_mul, map_mul, map_inv, hr'fix, hgF]
            rfl
        _ = n0⁻¹ * u * n0 := by
            change (g * n0)⁻¹ * r' * (g * n0) = n0⁻¹ * (g⁻¹ * r' * g) * n0
            group
    change n0 * twistHom TwistTag.E6 (AlgebraicClosure K) Fr u * n0⁻¹ = u
    rw [hmap]
    group
  have hu3 : u ^ 3 = 1 := by
    obtain ⟨b, hb_eq⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup huT
    rw [hb_eq] at htheta ⊢
    have hb : b ^ 3 = 1 := by
      funext i
      have h :=
        (TwistedDiag.theta_rootDiagUnit_eq_iff (Ω := AlgebraicClosure K) Fr hFr b).mp
          htheta i
      simpa using h
    calc rootDiagUnit Tag.E6 b ^ 3 = rootDiagUnit Tag.E6 (b ^ 3) :=
          rootDiagUnit_pow (τ := Tag.E6) b 3
      _ = rootDiagUnit Tag.E6 1 := by rw [hb]
      _ = 1 := rootDiagUnit_one (τ := Tag.E6)
  have hr'3 : r' ^ 3 = 1 := by
    have h : g⁻¹ * r' ^ 3 * g = 1 := by
      have hu3' : (g⁻¹ * r' * g) ^ 3 = 1 := by
        change u ^ 3 = 1
        exact hu3
      calc g⁻¹ * r' ^ 3 * g = (g⁻¹ * r' * g) ^ 3 := by
            simpa using (conj_pow (a := g⁻¹) (b := r') (i := 3)).symm
        _ = 1 := hu3'
    calc r' ^ 3 = g * (g⁻¹ * r' ^ 3 * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h]
      _ = 1 := by group
  apply baseChangeGL_injective (τ := TwistTag.E6.tag) f
  rw [map_pow, map_one]
  simpa [r'] using hr'3

end CFSG.StandardType.GGQ2CentPort.Q2TwE6

end
