module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootJ
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenDefs
public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6
public import CFSG.LieType.Chevalley.E6EvenRootTorus
public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest

public section

namespace CFSG.StandardType.TwE6ThreeRootGen

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three

private noncomputable def twE6Three_Y
    {K : Type} [Field K] {σ : K ≃+* K}
    (g₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
    twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
  (MulAut.conj g₀⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (twistedE6RootGroup K σ).subtype)

private theorem twE6Three_Y_apply
    {K : Type} [Field K] {σ : K ≃+* K}
    (g₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (x : twistedE6RootGroup K σ) :
    twE6Three_Y g₀ x = g₀⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g₀ := rfl

private theorem twE6Three_Y_injective
    {K : Type} [Field K] {σ : K ≃+* K}
    (g₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
    Function.Injective (twE6Three_Y (σ := σ) g₀) := by
  intro x y hxy
  have h : baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (y : ModGL TwistTag.E6.tag K) := by
    have h' := hxy
    rw [twE6Three_Y_apply, twE6Three_Y_apply] at h'
    exact mul_left_cancel (mul_right_cancel h')
  exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h)

private noncomputable def twE6Three_E
    {K : Type} [Field K] {σ : K ≃+* K} (p : ℕ)
    (g₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (T : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)))
    (hTcomm : IsMulCommutative T) :
    Subgroup (twistedE6RootGroup K σ) :=
  (CFSG.LieType.SeitzGeneration.torsionSubgroup T hTcomm p).comap (twE6Three_Y g₀)

private theorem twE6Three_mem_E
    {K : Type} [Field K] {σ : K ≃+* K} (p : ℕ)
    (g₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (T : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)))
    (hTcomm : IsMulCommutative T) (x : twistedE6RootGroup K σ) :
    x ∈ twE6Three_E p g₀ T hTcomm ↔ x ^ p = 1 ∧ twE6Three_Y g₀ x ∈ T := by
  rw [twE6Three_E, Subgroup.mem_comap,
    CFSG.LieType.SeitzGeneration.mem_torsionSubgroup]
  constructor
  · rintro ⟨hxT, hxpY⟩
    refine ⟨?_, hxT⟩
    refine twE6Three_Y_injective g₀ ?_
    rw [map_pow, hxpY, map_one]
  · rintro ⟨hxp, hxT⟩
    refine ⟨hxT, ?_⟩
    rw [← map_pow, hxp, map_one]

theorem exists_twE6Frame
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} (p : ℕ)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {v : WeylGroup TwistTag.E6.tag} {g₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg₀ : g₀ ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g₀ =
      g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) :
    ∃ (E : Subgroup (twistedE6RootGroup K σ)) (F : TwE6Frame K σ n p E),
      F.Fr = Fr ∧ F.v = v ∧ F.g0 = g₀ := by
  let T : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) :=
    twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
      (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
  have hT : T ≤ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := inf_le_left
  have hTcomm : IsMulCommutative T :=
    ⟨⟨fun x y => Subtype.ext
      (CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm (hT x.2) (hT y.2))⟩⟩
  let E : Subgroup (twistedE6RootGroup K σ) := twE6Three_E p g₀ T hTcomm
  have hmem : ∀ x : twistedE6RootGroup K σ, x ∈ E ↔ x ^ p = 1 ∧
      g₀⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g₀ ∈ T := by
    intro x
    rw [twE6Three_mem_E, twE6Three_Y_apply]
  let F : TwE6Frame K σ n p E :=
    { Fr := Fr, v := v, g0 := g₀, fr_eq := hFr, g0_mem := hg₀, lang := hlang, mem_iff := hmem }
  exact ⟨E, F, rfl, rfl, rfl⟩

theorem excIsLongest_twE6W0 :
    ExcIsLongest TwistTag.E6.tag CFSG.HardMathSupport.Lang.E6Descent.twE6W0 := by
  intro α hα hpos i
  have h := congrFun (CFSG.HardMathSupport.Lang.E6Descent.twE6W0_smul α) i
  have h2 : (-(permLattice CFSG.RankThree.E6.e6Rho α)) i ≤ 0 := by
    simp only [Pi.neg_apply, permLattice, Function.comp_apply]
    exact neg_nonpos.mpr (hpos _)
  exact h.le.trans h2

theorem exists_mem_ggKGTwJ_conj
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * F.g0⁻¹)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ r ∈ ggKGTwJ F γ, ∀ x,
      ((r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * t x *
          ((r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K)⁻¹ =
        t (ExcSplitRootGen.excRefl (p := 3) γ x) := by
  let γT : Fin TwistTag.E6.tag.rank → ℤ := γ
  have hγT : IsRoot TwistTag.E6.tag γT := hγ
  change ∃ r ∈ ggKGTwJ F γT, ∀ x,
    ((r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * t x *
        ((r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K)⁻¹ =
      t (ExcSplitRootGen.excRefl (p := 3) γT x)
  obtain ⟨r, hrJ, hrY⟩ := ggKGTwJ_weyl hK hσ F hv hγT
  refine ⟨r, hrJ, fun x => ?_⟩
  let xT : Fin TwistTag.E6.tag.rank → ZMod 3 := x
  have hinj : Function.Injective (baseChangeGL (τ := TwistTag.E6.tag)
      (f := algebraMap K (AlgebraicClosure K))) :=
    baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  apply hinj
  let n : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γT)
  have hbr : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      F.g0 * n * F.g0⁻¹ := by
    have hprod : F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * F.g0 =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
          (rootReflection γT) := by
      simpa only [ggKGTwY_apply] using hrY
    calc
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
          F.g0 * (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((r : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) * F.g0) *
            F.g0⁻¹ := by group
      _ = F.g0 * n * F.g0⁻¹ := by rw [hprod]
  have htz : zetaVec (τ := Tag.E6) ζ hζ x =
      zetaVec (τ := TwistTag.E6.tag) ζ hζ xT := rfl
  rw [map_mul, map_mul, map_inv, hbr, ht x, htz]
  rw [show F.g0 * n * F.g0⁻¹ *
        (F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := TwistTag.E6.tag) ζ hζ xT) *
          F.g0⁻¹) * (F.g0 * n * F.g0⁻¹)⁻¹ =
      F.g0 * (n * rootDiagUnit TwistTag.E6.tag
        (zetaVec (τ := TwistTag.E6.tag) ζ hζ xT) * n⁻¹) * F.g0⁻¹ from by group]
  rw [show n = canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
    (rootReflection γT) from rfl]
  have hconj := CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit
    (τ := TwistTag.E6.tag) (K := AlgebraicClosure K)
    (w := rootReflection γT) (b := zetaVec (τ := TwistTag.E6.tag) ζ hζ xT)
  rw [hconj]
  rw [weylTuple_zetaVec]
  rw [ht (ExcSplitRootGen.excRefl (p := 3) γT xT)]
  rfl

end CFSG.StandardType.TwE6ThreeRootGen

end
