module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaE
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaSDesc
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139HHerm
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139HNorm
import all CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.GroupTheory.CosetActionPerm
public import CFSG.GroupTheory.FixVConj
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13Stmts4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoLem
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E12Map
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E13Eq
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.GroupTheory.GL52 (F4poly)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

@[expose] def w1369_mulAutOfAddEquiv (e : Additive W ≃+ Additive W) : MulAut W where
  toFun w := Additive.toMul (e (Additive.ofMul w))
  invFun w := Additive.toMul (e.symm (Additive.ofMul w))
  left_inv w := by simp
  right_inv w := by simp
  map_mul' a b := by
    show Additive.toMul (e (Additive.ofMul (a * b))) =
      Additive.toMul (e (Additive.ofMul a)) * Additive.toMul (e (Additive.ofMul b))
    rw [ofMul_mul, map_add, toMul_add]

@[simp]
theorem w1369_mulAutOfAddEquiv_apply (e : Additive W ≃+ Additive W) (w : W) :
    w1369_mulAutOfAddEquiv e w = Additive.toMul (e (Additive.ofMul w)) := rfl

@[expose] def w1369_addEquivOfMulAut (s : MulAut W) : Additive W ≃+ Additive W where
  toFun := autAddHom s
  invFun := autAddHom s⁻¹
  left_inv v := by
    let w : W := Additive.toMul v
    have hv : Additive.ofMul w = v := rfl
    rw [← hv]
    simp [autAddHom]
  right_inv v := by
    let w : W := Additive.toMul v
    have hv : Additive.ofMul w = v := rfl
    rw [← hv]
    simp [autAddHom]
  map_add' := map_add (autAddHom s)

@[simp]
theorem w1369_addEquivOfMulAut_apply (s : MulAut W) (v : Additive W) :
    w1369_addEquivOfMulAut s v = autAddHom s v := rfl

theorem w1369_commute_mulAutOfAddEquiv_iff (e : Additive W ≃+ Additive W) (k : MulAut W) :
    (∀ v : Additive W, e (autAddHom k v) = autAddHom k (e v)) ↔
      w1369_mulAutOfAddEquiv e * k = k * w1369_mulAutOfAddEquiv e := by
  constructor
  · intro h
    ext w
    have hv := congrArg Additive.toMul (h (Additive.ofMul w))
    simpa [w1369_mulAutOfAddEquiv, autAddHom, MulAut.mul_apply] using hv
  · intro h v
    have hv := congrArg (fun f : MulAut W => Additive.ofMul (f (Additive.toMul v))) h
    simpa [w1369_mulAutOfAddEquiv, autAddHom, MulAut.mul_apply] using hv

section Scalar

variable (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
  (hfix : fixV (Subgroup.zpowers x) = ⊥)

@[expose] noncomputable def w1369_root : GaloisField 2 2 :=
  f4AlgEquivGalois (AdjoinRoot.root F4poly)

theorem w1369_root_smul (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    w1369_root • v = autAddHom x v := by
  letI := galoisModule hw2 x hx3 hfix
  change (f4RingHom hw2 x hx3 hfix (f4AlgEquivGalois.symm w1369_root)) v = autAddHom x v
  have hsymm : f4AlgEquivGalois.symm w1369_root = AdjoinRoot.root F4poly := by
    simp [w1369_root]
  rw [hsymm]
  change (f4AlgHom hw2 x hx3 hfix (AdjoinRoot.root F4poly)) v = autAddHom x v
  rw [f4AlgHom_root]
  rfl

theorem w1369_autAddHom_mul_apply (a b : MulAut W) (v : Additive W) :
    autAddHom (a * b) v = autAddHom a (autAddHom b v) := by
  simp [autAddHom, MulAut.mul_apply]

theorem w1369_pow_root_smul (n : ℕ) (v : Additive W) :
    letI := galoisModule hw2 x hx3 hfix
    (w1369_root ^ n) • v = autAddHom (x ^ n) v := by
  letI := galoisModule hw2 x hx3 hfix
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ', w1369_autAddHom_mul_apply]
      rw [mul_smul, ih, w1369_root_smul hw2 x hx3 hfix]

theorem w1369_scalar_of_mem_zpowers (hx_ord3 : orderOf x = 3) {a : MulAut W}
    (ha : a ∈ Subgroup.zpowers x) :
    letI := galoisModule hw2 x hx3 hfix
    ∃ c : GaloisField 2 2, ∀ v : Additive W, autAddHom a v = c • v := by
  letI := galoisModule hw2 x hx3 hfix
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [zpow_eq_zpow_emod' (x := x) i hx3]
  have hcases : i % (↑(3 : ℕ) : ℤ) = 0 ∨ i % (↑(3 : ℕ) : ℤ) = 1 ∨
      i % (↑(3 : ℕ) : ℤ) = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero]
    exact ⟨1, fun v => by simp⟩
  · rw [h, zpow_one]
    exact ⟨w1369_root, fun v => (w1369_root_smul hw2 x hx3 hfix v).symm⟩
  · rw [h]
    refine ⟨w1369_root ^ 2, fun v => ?_⟩
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact (w1369_pow_root_smul hw2 x hx3 hfix 2 v).symm

end Scalar

section Form

@[expose] def w1369_addFormInner (B : W →* W →* Multiplicative (ZMod 2)) (u : Additive W) :
    Additive W →+ ZMod 2 where
  toFun v := Multiplicative.toAdd (B (Additive.toMul u) (Additive.toMul v))
  map_zero' := by
    show Multiplicative.toAdd ((B (Additive.toMul u)) 1) = 0
    rw [map_one]
    rfl
  map_add' := fun a b => by
    show Multiplicative.toAdd
        ((B (Additive.toMul u)) (Additive.toMul (a + b))) =
      Multiplicative.toAdd ((B (Additive.toMul u)) (Additive.toMul a)) +
        Multiplicative.toAdd ((B (Additive.toMul u)) (Additive.toMul b))
    rw [toMul_add, map_mul, toAdd_mul]

@[simp]
theorem w1369_addFormInner_apply (B : W →* W →* Multiplicative (ZMod 2))
    (u v : Additive W) :
    w1369_addFormInner B u v =
      Multiplicative.toAdd (B (Additive.toMul u) (Additive.toMul v)) := rfl

@[expose] def w1369_addForm (B : W →* W →* Multiplicative (ZMod 2)) :
    Additive W →+ Additive W →+ ZMod 2 where
  toFun := w1369_addFormInner B
  map_zero' := by
    refine AddMonoidHom.ext fun v => ?_
    show w1369_addFormInner B 0 v = 0
    rw [w1369_addFormInner_apply]
    show Multiplicative.toAdd ((B 1) (Additive.toMul v)) = 0
    rw [map_one]
    rfl
  map_add' := fun a b => by
    refine AddMonoidHom.ext fun v => ?_
    show w1369_addFormInner B (a + b) v =
      (w1369_addFormInner B a + w1369_addFormInner B b) v
    rw [w1369_addFormInner_apply, AddMonoidHom.add_apply, w1369_addFormInner_apply,
      w1369_addFormInner_apply]
    show Multiplicative.toAdd ((B (Additive.toMul (a + b))) (Additive.toMul v)) =
      Multiplicative.toAdd ((B (Additive.toMul a)) (Additive.toMul v)) +
        Multiplicative.toAdd ((B (Additive.toMul b)) (Additive.toMul v))
    rw [toMul_add, map_mul, MonoidHom.mul_apply, toAdd_mul]

@[simp]
theorem w1369_addForm_apply (B : W →* W →* Multiplicative (ZMod 2)) (u v : Additive W) :
    w1369_addForm B u v =
      Multiplicative.toAdd (B (Additive.toMul u) (Additive.toMul v)) := by
  show w1369_addFormInner B u v = Multiplicative.toAdd (B (Additive.toMul u) (Additive.toMul v))
  rw [w1369_addFormInner_apply]

theorem w1369_addForm_alt (B : W →* W →* Multiplicative (ZMod 2))
    (halt : ∀ x : W, B x x = 1) (u : Additive W) :
    w1369_addForm B u u = 0 := by
  rw [w1369_addForm_apply]
  show Multiplicative.toAdd ((B (Additive.toMul u)) (Additive.toMul u)) = 0
  rw [halt]
  rfl

theorem w1369_addForm_left_nondegenerate (B : W →* W →* Multiplicative (ZMod 2))
    (hnd : ∀ x : W, (∀ y : W, B x y = 1) → x = 1) :
    ∀ u : Additive W, (∀ v, w1369_addForm B u v = 0) → u = 0 := by
  intro u hu
  have h : ∀ y : W, B (Additive.toMul u) y = 1 := by
    intro y
    have := hu (Additive.ofMul y)
    simpa [w1369_addForm_apply] using this
  have h1 : Additive.toMul u = 1 := hnd _ h
  simpa using congrArg Additive.ofMul h1

theorem w1369_addForm_symm (B : W →* W →* Multiplicative (ZMod 2))
    (halt : ∀ x : W, B x x = 1) (u v : Additive W) :
    w1369_addForm B u v = w1369_addForm B v u := by
  have h := halt (Additive.toMul u * Additive.toMul v)
  rw [map_mul B (Additive.toMul u) (Additive.toMul v)] at h
  change (B (Additive.toMul u)) (Additive.toMul u * Additive.toMul v) *
      (B (Additive.toMul v)) (Additive.toMul u * Additive.toMul v) = 1 at h
  rw [map_mul (B (Additive.toMul u)) (Additive.toMul u) (Additive.toMul v),
    map_mul (B (Additive.toMul v)) (Additive.toMul u) (Additive.toMul v)] at h
  rw [halt (Additive.toMul u), halt (Additive.toMul v)] at h
  simp only [one_mul, mul_one] at h
  have h2 : Multiplicative.toAdd (B (Additive.toMul u) (Additive.toMul v)) +
      Multiplicative.toAdd (B (Additive.toMul v) (Additive.toMul u)) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa [toAdd_mul] using this
  simpa [w1369_addForm_apply] using (CharTwo.add_eq_zero.mp h2)

@[expose] noncomputable def w1369_bilinForm (hw2 : ∀ w : W, w ^ 2 = 1)
    (B : W →* W →* Multiplicative (ZMod 2)) :
    letI := addModTwo hw2
    LinearMap.BilinForm (ZMod 2) (Additive W) := by
  letI := addModTwo hw2
  exact LinearMap.mk₂ (ZMod 2) (fun u v => w1369_addForm B u v)
    (fun u₁ u₂ v => by
      have h := map_add (w1369_addForm B) u₁ u₂
      simpa using congrArg (fun f : Additive W →+ ZMod 2 => f v) h)
    (fun c u v => by
      have h := ZMod.map_smul (n := 2) (w1369_addForm B) c u
      simpa using congrArg (fun f : Additive W →+ ZMod 2 => f v) h)
    (fun u v₁ v₂ => by
      have h := map_add (w1369_addForm B u) v₁ v₂
      simpa using h)
    (fun c u v => by
      have h := ZMod.map_smul (n := 2) (w1369_addForm B u) c v
      simpa using h)

theorem w1369_bilinForm_apply (hw2 : ∀ w : W, w ^ 2 = 1)
    (B : W →* W →* Multiplicative (ZMod 2)) (u v : Additive W) :
    letI := addModTwo hw2
    w1369_bilinForm hw2 B u v = w1369_addForm B u v := by
  letI := addModTwo hw2
  rfl

theorem w1369_bilinForm_nondegenerate (hw2 : ∀ w : W, w ^ 2 = 1)
    (B : W →* W →* Multiplicative (ZMod 2))
    (hnd : ∀ x : W, (∀ y : W, B x y = 1) → x = 1) (halt : ∀ x : W, B x x = 1) :
    letI := addModTwo hw2
    (w1369_bilinForm hw2 B).Nondegenerate := by
  letI := addModTwo hw2
  refine ⟨?_, ?_⟩
  · intro u hu
    exact w1369_addForm_left_nondegenerate B hnd u fun v => by
      rw [← w1369_bilinForm_apply]; exact hu v
  · intro v hv
    refine w1369_addForm_left_nondegenerate B hnd v fun u => ?_
    have h := hv u
    rw [w1369_bilinForm_apply] at h
    rwa [w1369_addForm_symm B halt v u]

theorem w1369_bilinForm_symm (hw2 : ∀ w : W, w ^ 2 = 1)
    (B : W →* W →* Multiplicative (ZMod 2)) (halt : ∀ x : W, B x x = 1)
    (u v : Additive W) :
    letI := addModTwo hw2
    w1369_bilinForm hw2 B u v = w1369_bilinForm hw2 B v u := by
  letI := addModTwo hw2
  rw [w1369_bilinForm_apply, w1369_bilinForm_apply, w1369_addForm_symm B halt]

end Form

section Adjoint

theorem w1369_smul_adjoint (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hx_ord3 : orderOf x = 3)
    (B : W →* W →* Multiplicative (ZMod 2))
    (hnd : ∀ y : W, (∀ z : W, B y z = 1) → y = 1) (halt : ∀ y : W, B y y = 1)
    (K : Subgroup (MulAut W))
    (hinvK : ∀ k ∈ K, ∀ u v : W, B (k u) (k v) = B u v)
    (hcommK : ∀ k ∈ K, k * x = x * k)
    (hcent : Subgroup.centralizer (K : Set (MulAut W)) = Subgroup.zpowers x)
    (μ : GaloisField 2 2) :
    letI := galoisModule hw2 x hx3 hfix
    ∃ μ' : GaloisField 2 2, ∀ u v : Additive W,
      w1369_addForm B (μ • u) v = w1369_addForm B u (μ' • v) := by
  letI := galoisModule hw2 x hx3 hfix
  by_cases hμ : μ = 0
  · refine ⟨0, fun u v => ?_⟩
    rw [hμ, zero_smul, zero_smul]
    simp
  · have hμ' : μ ≠ 0 := hμ
    letI := addModTwo hw2
    let Blin := w1369_bilinForm hw2 B
    have hBlin : Blin.Nondegenerate := w1369_bilinForm_nondegenerate hw2 B hnd halt
    have hBsymm : ∀ a b : Additive W, Blin a b = Blin b a :=
      fun a b => w1369_bilinForm_symm hw2 B halt a b
    let σ : Additive W →ₗ[ZMod 2] Additive W :=
      (LinearMap.lsmul (GaloisField 2 2) (Additive W) μ).toAddMonoidHom.toZModLinearMap 2
    have hσ : ∀ u : Additive W, σ u = μ • u := fun u => rfl
    let T : Additive W →ₗ[ZMod 2] Additive W := Blin.leftAdjointOfNondegenerate hBlin σ
    have hTadj : ∀ a b : Additive W, Blin (σ a) b = Blin a (T b) := by
      intro a b
      have hadj := Blin.isAdjointPairLeftAdjointOfNondegenerate hBlin σ b a
      rw [hBsymm (T b) a] at hadj
      rw [hBsymm b (σ a)] at hadj
      exact hadj.symm
    have hσsurj : Function.Surjective σ := by
      intro w
      refine ⟨(μ⁻¹) • w, ?_⟩
      show σ ((μ⁻¹) • w) = w
      rw [hσ, smul_smul, mul_inv_cancel₀ hμ', one_smul]
    have hTinj : Function.Injective T := by
      intro p q hpq
      have h0 : T (p - q) = 0 := by rw [map_sub, hpq, sub_self]
      have hz : p - q = 0 := by
        apply hBlin.2
        intro w
        obtain ⟨w', rfl⟩ := hσsurj w
        rw [hTadj w' (p - q), h0, map_zero]
      exact sub_eq_zero.mp hz
    have hTsurj : Function.Surjective T := Finite.surjective_of_injective hTinj
    have hinvAdd : ∀ k ∈ K, ∀ u v : Additive W,
        Blin (autAddHom k u) (autAddHom k v) = Blin u v := by
      intro k hk u v
      rw [w1369_bilinForm_apply, w1369_bilinForm_apply, w1369_addForm_apply,
        w1369_addForm_apply]
      change Multiplicative.toAdd (B (k (Additive.toMul u)) (k (Additive.toMul v))) =
        Multiplicative.toAdd (B (Additive.toMul u) (Additive.toMul v))
      rw [hinvK k hk]
    have hklin : ∀ k ∈ K, ∀ c : GaloisField 2 2, ∀ w : Additive W,
        autAddHom k (c • w) = c • autAddHom k w := by
      intro k hk c w
      have h := (hGaloisLinearEquiv hw2 x hx3 hfix k (hcommK k hk)).map_smul c w
      rwa [hGaloisLinearEquiv_apply, hGaloisLinearEquiv_apply] at h
    have hk1 : ∀ k ∈ K, ∀ u : Additive W, autAddHom k (autAddHom k⁻¹ u) = u := by
      intro k hk u
      rw [← w1369_autAddHom_mul_apply]
      simp [autAddHom]
    have hσlin : ∀ (k : MulAut W) (hk : k ∈ K) (a : Additive W),
        σ a = autAddHom k (σ (autAddHom k⁻¹ a)) := by
      intro k hk a
      rw [hσ, hσ, hklin k hk, hk1 k hk]
    have hTcomm : ∀ k ∈ K, ∀ v : Additive W, T (autAddHom k v) = autAddHom k (T v) := by
      intro k hk v
      have hkey : ∀ u : Additive W,
          Blin u (T (autAddHom k v)) = Blin u (autAddHom k (T v)) := by
        intro u
        calc Blin u (T (autAddHom k v))
            = Blin (σ u) (autAddHom k v) := (hTadj u (autAddHom k v)).symm
          _ = Blin (autAddHom k (σ (autAddHom k⁻¹ u))) (autAddHom k v) := by
                rw [hσlin k hk u]
          _ = Blin (σ (autAddHom k⁻¹ u)) v := hinvAdd k hk _ v
          _ = Blin (autAddHom k⁻¹ u) (T v) := hTadj _ _
          _ = Blin (autAddHom k (autAddHom k⁻¹ u)) (autAddHom k (T v)) :=
                (hinvAdd k hk _ _).symm
          _ = Blin u (autAddHom k (T v)) := by rw [hk1 k hk u]
      have hz : T (autAddHom k v) - autAddHom k (T v) = 0 := by
        apply hBlin.2
        intro u
        rw [map_sub]
        exact sub_eq_zero.mpr (hkey u)
      exact sub_eq_zero.mp hz
    let e : Additive W ≃+ Additive W :=
      AddEquiv.ofBijective T.toAddMonoidHom ⟨hTinj, hTsurj⟩
    have he : ∀ v : Additive W, e v = T v := fun v => rfl
    have hmem : w1369_mulAutOfAddEquiv e ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [eq_comm, ← w1369_commute_mulAutOfAddEquiv_iff e k]
      intro v
      rw [he, he]
      exact hTcomm k hk v
    have hgX : w1369_mulAutOfAddEquiv e ∈ Subgroup.zpowers x := by
      rw [← hcent]
      exact hmem
    obtain ⟨μ'', hμ''⟩ := w1369_scalar_of_mem_zpowers hw2 x hx3 hfix hx_ord3 hgX
    have hTμ : ∀ v : Additive W, T v = μ'' • v := by
      intro v
      have h := hμ'' v
      rwa [show autAddHom (w1369_mulAutOfAddEquiv e) v = T v from by
        rw [autAddHom_apply, w1369_mulAutOfAddEquiv_apply]; rfl] at h
    refine ⟨μ'', fun u v => ?_⟩
    rw [← w1369_bilinForm_apply hw2 B (μ • u) v, ← hσ u, hTadj u v,
      w1369_bilinForm_apply hw2 B u (T v), hTμ v]

end Adjoint

theorem w1369_trace_eq_zero (δ : GaloisField 2 2)
    (h : ∀ a : GaloisField 2 2,
      Algebra.trace (ZMod 2) (GaloisField 2 2) (a * δ) = 0) : δ = 0 := by
  have hnd := traceForm_nondegenerate (ZMod 2) (GaloisField 2 2)
  refine hnd.2 δ fun a => ?_
  rw [Algebra.traceForm_apply]
  exact h a

section Invariance

theorem w1369_b_invariant (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (B : W →* W →* Multiplicative (ZMod 2))
    (K : Subgroup (MulAut W))
    (hinvK : ∀ k ∈ K, ∀ u v : W, B (k u) (k v) = B u v)
    (hcommK : ∀ k ∈ K, k * x = x * k)
    (θ : GaloisField 2 2 →+* GaloisField 2 2) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (b : Additive W →ₗ[GaloisField 2 2] Additive W →ₛₗ[θ] GaloisField 2 2),
      (∀ u v : Additive W, w1369_addForm B u v =
        Algebra.trace (ZMod 2) (GaloisField 2 2) (b u v)) →
      ∀ k ∈ K, ∀ u v : Additive W, b (autAddHom k u) (autAddHom k v) = b u v := by
  letI := galoisModule hw2 x hx3 hfix
  intro b hbtr k hk u v
  have hb_smul : ∀ (a : GaloisField 2 2) (p c : Additive W),
      b (a • p) c = a * b p c := by
    intro a p c
    have h := congrArg (fun f : Additive W →ₛₗ[θ] GaloisField 2 2 => f c) (map_smul b a p)
    simpa [LinearMap.smul_apply, smul_eq_mul] using h
  have hkl : ∀ (a : GaloisField 2 2) (w : Additive W),
      a • autAddHom k w = autAddHom k (a • w) := by
    intro a w
    have h := (hGaloisLinearEquiv hw2 x hx3 hfix k (hcommK k hk)).map_smul a w
    rw [hGaloisLinearEquiv_apply (h := k) hw2 x hx3 hfix (hcommK k hk) (a • w),
        hGaloisLinearEquiv_apply (h := k) hw2 x hx3 hfix (hcommK k hk) w] at h
    exact h.symm
  have hδ : ∀ a : GaloisField 2 2,
      Algebra.trace (ZMod 2) (GaloisField 2 2)
        (a * (b (autAddHom k u) (autAddHom k v) - b u v)) = 0 := by
    intro a
    have h1 : Algebra.trace (ZMod 2) (GaloisField 2 2)
        (a * b (autAddHom k u) (autAddHom k v)) =
        w1369_addForm B (a • autAddHom k u) (autAddHom k v) := by
      rw [hbtr]
      exact congrArg (Algebra.trace (ZMod 2) (GaloisField 2 2))
        (hb_smul a (autAddHom k u) (autAddHom k v)).symm
    have h2 : w1369_addForm B (a • autAddHom k u) (autAddHom k v) =
        w1369_addForm B (a • u) v := by
      rw [hkl a u]
      exact hinvK k hk (a • u) v
    have h3 : Algebra.trace (ZMod 2) (GaloisField 2 2) (a * b u v) =
        w1369_addForm B (a • u) v := by
      rw [hbtr]
      exact congrArg (Algebra.trace (ZMod 2) (GaloisField 2 2))
        (hb_smul a u v).symm
    rw [mul_sub, map_sub, h1, h2, h3, sub_self]
  have hzero := w1369_trace_eq_zero (b (autAddHom k u) (autAddHom k v) - b u v) hδ
  exact sub_eq_zero.mp hzero

end Invariance

section FixedField

def w1369_fixedSubfield (θ : GaloisField 2 2 →+* GaloisField 2 2) :
    Subfield (GaloisField 2 2) where
  carrier := {c | θ c = c}
  zero_mem' := map_zero θ
  one_mem' := map_one θ
  add_mem' := by intro a b ha hb; change θ (a + b) = a + b; rw [map_add, ha, hb]
  mul_mem' := by intro a b ha hb; change θ (a * b) = a * b; rw [map_mul, ha, hb]
  neg_mem' := by intro a ha; change θ (-a) = -a; rw [map_neg, ha]
  inv_mem' := by intro a ha; change θ a⁻¹ = a⁻¹; rw [map_inv₀, ha]

theorem w1369_fixed_card (θ : GaloisField 2 2 →+* GaloisField 2 2)
    (hθ2 : ∀ c : GaloisField 2 2, θ (θ c) = c)
    (hθ1 : θ ≠ RingHom.id (GaloisField 2 2)) :
    Nat.card {c : GaloisField 2 2 // θ c = c} = 2 := by
  let F : Subfield (GaloisField 2 2) := w1369_fixedSubfield θ
  have hcongr : Nat.card {c : GaloisField 2 2 // θ c = c} = Nat.card F :=
    Nat.card_congr (Equiv.refl _)
  rw [hcongr]
  have hcardE : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hpow : Nat.card F ^ Module.finrank F (GaloisField 2 2) = 4 := by
    rw [← Module.natCard_eq_pow_finrank (K := F) (V := GaloisField 2 2), hcardE]
  have hge : 2 ≤ Nat.card F := by
    haveI : Nontrivial F :=
      ⟨⟨⟨0, F.zero_mem⟩, ⟨1, F.one_mem⟩,
        fun h => zero_ne_one (Subtype.ext_iff.mp h)⟩⟩
    have := Finite.one_lt_card (α := F)
    omega
  have hlt : Nat.card F < 4 := by
    obtain ⟨b, hb⟩ : ∃ b : GaloisField 2 2, θ b ≠ b := by
      by_contra h
      apply hθ1
      ext c
      by_contra hc
      exact h ⟨c, hc⟩
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    have h := Fintype.card_lt_of_injective_of_notMem (Subfield.subtype F)
      (Subfield.subtype_injective F) (b := b) (by
        rintro ⟨x, rfl⟩
        exact hb x.2)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardE] at h
    exact h
  have hle : Nat.card F ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ Nat.card F := by omega
    have hF3 : Nat.card F = 3 := by omega
    have hd1 : Module.finrank F (GaloisField 2 2) = 1 := by
      by_contra hd
      have hfin1 : 1 ≤ Module.finrank F (GaloisField 2 2) := by
        by_contra h0
        have h0' : Module.finrank F (GaloisField 2 2) = 0 := by omega
        rw [h0', pow_zero] at hpow
        norm_num at hpow
      have hd2 : 2 ≤ Module.finrank F (GaloisField 2 2) := by omega
      have h1 : 3 ^ 2 ≤ 3 ^ Module.finrank F (GaloisField 2 2) :=
        Nat.pow_le_pow_right (by norm_num) hd2
      have h2 : 3 ^ Module.finrank F (GaloisField 2 2) ≤
          Nat.card F ^ Module.finrank F (GaloisField 2 2) := Nat.pow_le_pow_left h3 _
      have h4 : 3 ^ 2 ≤ 4 := h1.trans (h2.trans (le_of_eq hpow))
      norm_num at h4
    rw [hF3, hd1, pow_one] at hpow
    norm_num at hpow
  omega

end FixedField

theorem w1369_hermitian_case (hw2 : ∀ w : W, w ^ 2 = 1)
    (S : Std139 G X D s Y n) (hn : n = 3) {K : Subgroup (MulAut W)}
    (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥)
    {x : MulAut W} (hxgen : X = Subgroup.zpowers x) (hx3 : x ^ 3 = 1) (hxne : x ≠ 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hx_ord3 : orderOf x = 3)
    (hcommK : ∀ k ∈ K, k * x = x * k)
    (hcent : Subgroup.centralizer (K : Set (MulAut W)) = Subgroup.zpowers x)
    {B : W →* W →* Multiplicative (ZMod 2)}
    (hnd : ∀ y : W, (∀ z : W, B y z = 1) → y = 1) (halt : ∀ y : W, B y y = 1)
    (hinv : ∀ k ∈ K, ∀ u v : W, B (k u) (k v) = B u v)
    {θ : GaloisField 2 2 →+* GaloisField 2 2}
    (hθ2 : ∀ c : GaloisField 2 2, θ (θ c) = c)
    (hθid : θ ≠ RingHom.id (GaloisField 2 2)) :
    letI := galoisModule hw2 x hx3 hfix
    ∀ (b : Additive W →ₗ[GaloisField 2 2] Additive W →ₛₗ[θ] GaloisField 2 2),
      (∀ u v : Additive W, w1369_addForm B u v =
        Algebra.trace (ZMod 2) (GaloisField 2 2) (b u v)) →
      (∀ u : Additive W, (∀ v : Additive W, b u v = 0) → u = 0) →
      (∀ u v : Additive W, b v u = θ (b u v)) →
      (∀ k ∈ K, ∀ u v : Additive W, b (autAddHom k u) (autAddHom k v) = b u v) →
      False := by
  letI := galoisModule hw2 x hx3 hfix
  intro b hbtr hbnd hbsymm hbinv
  have hxX : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
  have hcardY : Nat.card Y = 16 := by
    have hYidx : Y.index = 4 := by
      have h := S.Yrk
      change padicValNat 2 Y.index = 2 at h
      have hdvd : Y.index ∣ 2 ^ 6 := by
        have hW : Nat.card W = 2 ^ 6 := by rw [S.card, hn]; norm_num
        rw [← hW]
        exact ⟨Nat.card Y, by rw [mul_comm]; exact (Y.card_mul_index).symm⟩
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rw [hk, padicValNat.pow, padicValNat_self] at h
      norm_num at h
      rw [hk, h]; norm_num
    have hcard := Y.card_mul_index
    rw [S.card, hn, hYidx] at hcard
    omega
  let A : Submodule (GaloisField 2 2) (Additive W) :=
    YSubmodule hw2 x hx3 hfix hxX S.Yinv
  have hcardA : Nat.card A = 16 := by
    rw [← Nat.card_congr (YSubmoduleEquiv hw2 x hx3 hfix hxX S.Yinv), hcardY]
  have hKcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have hfrA : Module.finrank (GaloisField 2 2) A = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := A)
    rw [hcardA, hKcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h).symm
  have hfrV : Module.finrank (GaloisField 2 2) (Additive W) = 3 := by
    have hcardW : Nat.card (Additive W) = 4 ^ 3 := by
      change Nat.card W = 4 ^ 3
      rw [S.card, hn]
    have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 2) (V := Additive W)
    rw [hcardW, hKcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h).symm
  have hA : Module.finrank (GaloisField 2 2) A + 1 =
      Module.finrank (GaloisField 2 2) (Additive W) := by rw [hfrA, hfrV]
  have hcommd : ∀ d : ↥D, (d : MulAut W) * x = x * (d : MulAut W) :=
    fun d => S.DX d d.2 x hxX
  let C : Subgroup (MulAut W) := Subgroup.centralizer (X : Set (MulAut W))
  have hcommC : ∀ h ∈ C, h * x = x * h := by
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp hh x hxX).symm
  have hKleC : K ≤ C := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (S.component_commutes_X hK.comp k hk y hy).symm
  have hDleC : D ≤ C := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (S.DX d hd y hy).symm
  let φ : ↥C →* (Additive W ≃ₗ[GaloisField 2 2] Additive W) :=
    HLinHom hw2 x hx3 hfix C hcommC
  have hφd : ∀ d : ↥D,
      hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d) =
        φ ⟨(d : MulAut W), hDleC d.2⟩ := by
    intro d
    exact (congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) hc)
      (Subsingleton.elim (hcommd d)
        (hcommC (⟨(d : MulAut W), hDleC d.2⟩ : ↥C) (hDleC d.2)))).trans
      (HLinHom_apply hw2 x hx3 hfix C hcommC (⟨(d : MulAut W), hDleC d.2⟩ : ↥C)).symm
  let Kb : Subgroup (Additive W ≃ₗ[GaloisField 2 2] Additive W) :=
    HLin hw2 x hx3 hfix K hcommK
  have hirrK : ∀ Z : Subgroup W, StableUnder K Z → Z = ⊥ ∨ Z = ⊤ :=
    fun Z hZ => hirr.2.2.2 Z hZ bot_le le_top
  have hirrKb : ∀ M : Submodule (GaloisField 2 2) (Additive W),
      (∀ k ∈ Kb, ∀ x ∈ M, k x ∈ M) → M = ⊥ ∨ M = ⊤ := by
    intro M hM
    apply hirr_submodule_of_hirr_subgroup (G := K) hirrK
    intro k hk z hz
    have hmem : hGaloisLinearEquiv hw2 x hx3 hfix k (hcommK k hk) ∈ Kb := by
      change hGaloisLinearEquiv hw2 x hx3 hfix k (hcommK k hk) ∈
        HLin hw2 x hx3 hfix K hcommK
      rw [mem_HLin hw2 x hx3 hfix K hcommK]
      exact ⟨k, hk, rfl⟩
    exact hM _ hmem z hz
  have habs : ∀ f : Additive W →ₗ[GaloisField 2 2] Additive W,
      (∀ k ∈ Kb, ∀ x, f (k x) = k (f x)) →
        ∃ c : GaloisField 2 2, ∀ x, f x = c • x := by
    intro f hf
    by_cases hf0 : f = 0
    · exact ⟨0, fun x => by rw [hf0]; simp⟩
    · have hker : LinearMap.ker f = ⊥ :=
        (hirrKb (LinearMap.ker f) (by
          rintro k hk x hx
          rw [LinearMap.mem_ker] at hx ⊢
          rw [hf k hk x, hx, map_zero])).resolve_right (by
            intro h
            exact hf0 (by
              ext x
              have : x ∈ LinearMap.ker f := by rw [h]; exact Submodule.mem_top
              simpa [LinearMap.mem_ker] using this))
      have hrange : LinearMap.range f = ⊤ :=
        (hirrKb (LinearMap.range f) (by
          rintro k hk y hy
          obtain ⟨z, rfl⟩ := hy
          exact ⟨k z, hf k hk z⟩)).resolve_left (by
            intro h
            exact hf0 (by
              ext x
              have : f x ∈ LinearMap.range f := ⟨x, rfl⟩
              rw [h] at this
              simpa using this))
      have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hker
      have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
      let e : Additive W ≃ₗ[GaloisField 2 2] Additive W :=
        LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
      have hmem : w1369_mulAutOfAddEquiv e.toAddEquiv ∈
          Subgroup.centralizer (K : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        rw [eq_comm, ← w1369_commute_mulAutOfAddEquiv_iff e.toAddEquiv k]
        intro v
        have hmemKb : hGaloisLinearEquiv hw2 x hx3 hfix k (hcommK k hk) ∈ Kb := by
          change hGaloisLinearEquiv hw2 x hx3 hfix k (hcommK k hk) ∈
            HLin hw2 x hx3 hfix K hcommK
          rw [mem_HLin hw2 x hx3 hfix K hcommK]
          exact ⟨k, hk, rfl⟩
        have h := hf _ hmemKb v
        rw [hGaloisLinearEquiv_apply (h := k) hw2 x hx3 hfix (hcommK k hk) v,
            hGaloisLinearEquiv_apply (h := k) hw2 x hx3 hfix (hcommK k hk) (f v)] at h
        change f (autAddHom k v) = autAddHom k (f v)
        exact h
      have hgX : w1369_mulAutOfAddEquiv e.toAddEquiv ∈ Subgroup.zpowers x := by
        rw [← hcent]; exact hmem
      obtain ⟨c, hc⟩ := w1369_scalar_of_mem_zpowers hw2 x hx3 hfix hx_ord3 hgX
      refine ⟨c, fun v => ?_⟩
      have h := hc v
      rwa [show autAddHom (w1369_mulAutOfAddEquiv e.toAddEquiv) v = f v from by
        rw [autAddHom_apply, w1369_mulAutOfAddEquiv_apply]; rfl] at h
  have hbinvKb : ∀ k ∈ Kb, ∀ u v : Additive W, b (k u) (k v) = b u v := by
    intro k hk u v
    change k ∈ HLin hw2 x hx3 hfix K hcommK at hk
    obtain ⟨k', hk', rfl⟩ := (mem_HLin hw2 x hx3 hfix K hcommK k).mp hk
    rw [hGaloisLinearEquiv_apply (h := k') hw2 x hx3 hfix (hcommK k' hk') u,
        hGaloisLinearEquiv_apply (h := k') hw2 x hx3 hfix (hcommK k' hk') v]
    exact hbinv k' hk' u v
  have hnorm : ∀ (d : ↥D) (k : Additive W ≃ₗ[GaloisField 2 2] Additive W), k ∈ Kb →
      hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d) * k *
        (hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d))⁻¹ ∈ Kb := by
    intro d k hk
    change k ∈ HLin hw2 x hx3 hfix K hcommK at hk
    obtain ⟨k', hk', rfl⟩ := (mem_HLin hw2 x hx3 hfix K hcommK k).mp hk
    have hdK : (d : MulAut W) * k' * (d : MulAut W)⁻¹ ∈ K := by
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj (d : MulAut W)).toMonoidHom hk'
      rw [hK.normal (d : MulAut W) (S.DG d.2)] at hmem
      simpa [MulAut.conj_apply] using hmem
    refine ⟨(d : MulAut W) * k' * (d : MulAut W)⁻¹, hdK, ?_⟩
    have hφk : hGaloisLinearEquiv hw2 x hx3 hfix k' (hcommK k' hk') =
        φ ⟨k', hKleC hk'⟩ := by
      exact (congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix k' hc)
        (Subsingleton.elim (hcommK k' hk') (hcommC (⟨k', hKleC hk'⟩ : ↥C) (hKleC hk')))).trans
        (HLinHom_apply hw2 x hx3 hfix C hcommC (⟨k', hKleC hk'⟩ : ↥C)).symm
    have hφt : hGaloisLinearEquiv hw2 x hx3 hfix ((d : MulAut W) * k' * (d : MulAut W)⁻¹)
        (hcommK _ hdK) =
        φ ⟨(d : MulAut W) * k' * (d : MulAut W)⁻¹, hKleC hdK⟩ := by
      exact (congrArg (fun hc => hGaloisLinearEquiv hw2 x hx3 hfix _ hc)
        (Subsingleton.elim (hcommK _ hdK)
          (hcommC (⟨_, hKleC hdK⟩ : ↥C) (hKleC hdK)))).trans
        (HLinHom_apply hw2 x hx3 hfix C hcommC (⟨_, hKleC hdK⟩ : ↥C)).symm
    rw [hφd d, hφk, hφt, ← map_mul, ← map_inv, ← map_mul]
    exact congrArg φ (Subtype.ext rfl)
  have hmem : ∀ d : ↥D, hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d) ∈
      {g : Additive W ≃ₗ[GaloisField 2 2] Additive W |
        (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
        ∃ l : GaloisField 2 2, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y} := by
    intro d
    refine ⟨?_, ?_, ?_⟩
    · intro v
      by_cases hd1 : (d : MulAut W) = 1
      · have hd1' : d = 1 := Subtype.ext hd1
        subst hd1'
        simp only [Subgroup.coe_one]
        rw [hGaloisLinearEquiv_one]
        simp
      · have hmemY := (Std139.commSub_axis hw2 S d.2 hd1).2.1
        have hval : Additive.toMul
            (hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d) v - v) ∈ Y := by
          apply hmemY
          rw [commSub]
          refine Subgroup.subset_closure ⟨(d : MulAut W), Subgroup.mem_zpowers (d : MulAut W),
            Additive.toMul v, Subgroup.mem_top _, ?_⟩
          have h1 : Additive.toMul
              (hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d) v - v) =
              (d : MulAut W) (Additive.toMul v) * (Additive.toMul v)⁻¹ := by
            rw [hGaloisLinearEquiv_apply, autAddHom_apply, sub_eq_add_neg, toMul_add, toMul_neg]
            rfl
          exact h1.symm
        exact hval
    · intro a ha
      have haY : Additive.toMul a ∈ Y := ha
      have hfixa : (d : MulAut W) (Additive.toMul a) = Additive.toMul a :=
        mem_fixV.mp (S.YD haY) d d.2
      rw [hGaloisLinearEquiv_apply]
      change Additive.ofMul ((d : MulAut W) (Additive.toMul a)) = a
      rw [hfixa]
      rfl
    · exact normalizer_preserves_herm θ Kb hirrKb habs b hbnd hbsymm hbinvKb
        (hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d)) (hnorm d)
  have hinj : Function.Injective (fun d : ↥D =>
      (⟨hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d), hmem d⟩ :
        {g : Additive W ≃ₗ[GaloisField 2 2] Additive W |
          (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
          ∃ l : GaloisField 2 2, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y})) := by
    intro d d' h
    have h1 : hGaloisLinearEquiv hw2 x hx3 hfix (d : MulAut W) (hcommd d) =
        hGaloisLinearEquiv hw2 x hx3 hfix (d' : MulAut W) (hcommd d') :=
      congrArg Subtype.val h
    apply Subtype.ext
    ext w
    have hv := congrArg (fun g : Additive W ≃ₗ[GaloisField 2 2] Additive W =>
      Additive.toMul (g (Additive.ofMul w))) h1
    simpa [hGaloisLinearEquiv_apply, autAddHom_apply] using hv
  haveI : Finite (Additive W ≃ₗ[GaloisField 2 2] Additive W) :=
    Finite.of_injective (fun g : Additive W ≃ₗ[GaloisField 2 2] Additive W =>
      (g : Additive W → Additive W)) (fun g h hgh => by ext x; exact congrFun hgh x)
  have hcard_le : Nat.card ↥D ≤ Nat.card
      {g : Additive W ≃ₗ[GaloisField 2 2] Additive W |
        (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
        ∃ l : GaloisField 2 2, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y} :=
    Nat.card_le_card_of_injective _ hinj
  have hDcard : Nat.card D = 4 := by rw [S.Dcard, hn]; norm_num
  have hle := lemmaH_herm θ hθ2 hθid (by rw [hfrV]) A hA b hbnd hbsymm
  rw [w1369_fixed_card θ hθ2 hθid] at hle
  have h4le : 4 ≤ Nat.card
      {g : Additive W ≃ₗ[GaloisField 2 2] Additive W |
        (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
        ∃ l : GaloisField 2 2, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y} := by
    rw [← hDcard]; exact hcard_le
  exact absurd (h4le.trans hle) (by norm_num)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
