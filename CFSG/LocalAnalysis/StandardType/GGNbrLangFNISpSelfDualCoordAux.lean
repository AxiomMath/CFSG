module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpPrimary

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks

open Polynomial Module Matrix
open CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix

theorem kgfniSpSD_blockRestrict_square {K V : Type} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    {x : LinearMap.GeneralLinearGroup K V} (H : AltPrimaryData B x) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) [Fact (Irreducible a)] {S : V ≃+ V}
    (T : primaryComponent (x : Module.End K V) a ≃+ primaryComponent (x : Module.End K V) a)
    (hT : ∀ w, (T w : V) = S w) (hT' : ∀ w, (T.symm w : V) = S.symm w)
    {g g' : supportedUnitary B x {a}}
    (hgg' : ∀ v, ((g' : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      S (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) (S.symm v)))
    (w : primaryComponent (x : Module.End K V) a) :
    ((CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩ g' :
        Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) w : V) =
      (T ((CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩ g :
          Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) (T.symm w)) :
        V) := by
  classical
  have hleft : ((CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩ g' :
      Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) w : V) =
      ((g' : LinearMap.GeneralLinearGroup K V) : Module.End K V) (w : V) :=
    CFSG.RankThree.Classical.blockApply_blockRestrict H.squarefree {a} ⟨a, ha⟩ g' (w : V) w.2
  have hright : ((CFSG.RankThree.Classical.blockRestrict H.squarefree {a} ⟨a, ha⟩ g :
      Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) (T.symm w) : V) =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ((T.symm w : V)) :=
    CFSG.RankThree.Classical.blockApply_blockRestrict H.squarefree {a} ⟨a, ha⟩ g
      ((T.symm w : V)) (T.symm w).2
  rw [hT, hleft, hright, hT']
  exact hgg' (w : V)

theorem kgfniSpSD_extAut_pow_apply {K : Type} [Field K] {a : K[X]} {σ : K ≃+* K}
    (haσ : a.map (σ : K →+* K) = a) (k : ℕ) (q : K[X]) :
    (extAut a σ haσ ^ k) (AdjoinRoot.mk a q) =
      AdjoinRoot.mk a (q.map (((σ ^ k : K ≃+* K) : K →+* K))) := by
  induction k generalizing q with
  | zero =>
    rw [pow_zero]
    change AdjoinRoot.mk a q = AdjoinRoot.mk a
      (Polynomial.map ((1 : K ≃+* K) : K →+* K) q)
    have h : Polynomial.map ((1 : K ≃+* K) : K →+* K) q = q := Polynomial.map_id
    rw [h]
  | succ k ih =>
    rw [pow_succ]
    change (extAut a σ haσ ^ k) (extAut a σ haσ (AdjoinRoot.mk a q)) =
      AdjoinRoot.mk a (q.map (((σ ^ (k + 1) : K ≃+* K) : K →+* K)))
    rw [extAut_mk, ih (q.map (σ : K →+* K)), Polynomial.map_map]
    congr 1

theorem kgfniSpSD_altHermForm_semilin {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    {x : LinearMap.GeneralLinearGroup K V} (H : AltPrimaryData B x) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hself : reciprocalPolynomial a = a)
    [Fact (Irreducible a)]
    {θ : AdjoinRoot a →+* AdjoinRoot a}
    (hθ : ∀ z, θ z = rootInv (H.coeff_zero_ne ha) hself z)
    {σ : K ≃+* K} {τ : AdjoinRoot a ≃+* AdjoinRoot a}
    (hτ : ∀ c, τ (algebraMap K (AdjoinRoot a) c) = algebraMap K (AdjoinRoot a) (σ c))
    {T : primaryComponent (x : Module.End K V) a ≃+
      primaryComponent (x : Module.End K V) a}
    (hT : ∀ (c : AdjoinRoot a) (v : primaryComponent (x : Module.End K V) a),
      T (c • v) = τ c • T v)
    (hBT : ∀ u w : primaryComponent (x : Module.End K V) a,
      B ((T u : primaryComponent (x : Module.End K V) a) : V)
        ((T w : primaryComponent (x : Module.End K V) a) : V) = σ (B (u : V) (w : V)))
    (u w : primaryComponent (x : Module.End K V) a) :
    H.altHermForm ha hself θ hθ (1 : AdjoinRoot a) (T u) (T w) =
      τ (H.altHermForm ha hself θ hθ (1 : AdjoinRoot a) u w) := by
  classical
  let Hf : primaryComponent (x : Module.End K V) a →
      primaryComponent (x : Module.End K V) a → AdjoinRoot a :=
    fun u w => H.altHermForm ha hself θ hθ 1 u w
  have htr : ∀ (u w : primaryComponent (x : Module.End K V) a) (c : AdjoinRoot a),
      Algebra.trace K (AdjoinRoot a) (Hf u w * c) =
        B (u : V) ((c • w : primaryComponent (x : Module.End K V) a) : V) := by
    intro u w c
    rw [show Hf u w * c = c * Hf u w by ring,
      H.trace_altHermForm ha hself θ hθ (1 : AdjoinRoot a) u w c, mul_one]
  have h := traceTransfer_semilin K (AdjoinRoot a) (σ := σ) (τ := τ) hτ T hT
    (fun u w => B (u : V) (w : V)) hBT Hf htr u w
  simpa only [Hf] using h



end CFSG.StandardType

end
