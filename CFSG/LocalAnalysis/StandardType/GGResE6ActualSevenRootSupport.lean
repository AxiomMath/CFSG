module

public import CFSG.LocalAnalysis.StandardType.GGResE6NormWordOrbits
public import CFSG.LocalAnalysis.StandardType.GGResE7LiteralModel
public import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
public import CFSG.LocalAnalysis.StandardType.GGE6DepKNoTv
public import CFSG.LocalAnalysis.StandardType.GGKOnlyE6Normalization
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGResE6Coordinates
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small
public import CFSG.Quasithin.Background.SmithB45HatA6Out
public import CFSG.Sporadic.Co2Smith.Transport
public import CFSG.Blueprint.Chevalley
public import CFSG.Assembly.E6FourCentMask
public import CFSG.Mathlib.Decide.Bounded
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.Tactic
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13604
public import Certificates.Certificate13657
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate830101
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Background.SmithB42Alt7Ctx
public import CFSG.Quasithin.Background.SmithB42Alt7Model
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11


public section
namespace CFSG.StandardType

open CFSG.StandardType.E6NormWordOrbit

variable {G : Type} [Group G] [Finite G] {Bs : Subgroup G}

@[expose] def e6dot (u v : Fin 6 → ZMod 3) : ZMod 3 := ∑ i, u i * v i

@[expose] def e6dotLin (u : Fin 6 → ZMod 3) : Module.Dual (ZMod 3) (Fin 6 → ZMod 3) where
  toFun v := e6dot u v
  map_add' v w := by
    simp only [e6dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [e6dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[expose] noncomputable def e6WordAut {ι : Type} (φ : ι → MulAut ↥Bs) : List ι → MulAut ↥Bs
  | [] => 1
  | i :: is => e6WordAut φ is * φ i

@[expose] noncomputable def e6RootRefl (φL : Fin 6 → MulAut ↥Bs) (i0 : Fin 6)
    (w : List (Fin 6)) : MulAut ↥Bs :=
  e6WordAut φL w * φL i0 * (e6WordAut φL w)⁻¹

end CFSG.StandardType

end

public section

public section

namespace CFSG.StandardType

open Module LinearMap

namespace E6Seven

variable {K : Type*} [Field K]

@[expose] noncomputable def gram7Block (C : Matrix (Fin 6) (Fin 6) K) (c : Fin 6 → K) (d : K) :
    Matrix (Fin 6 ⊕ Fin 1) (Fin 6 ⊕ Fin 1) K :=
  Matrix.fromBlocks C
    (Matrix.of fun i _ => c i)
    (Matrix.of fun _ j => c j)
    (Matrix.of fun _ _ => d)

@[expose] noncomputable def gram7 (C : Matrix (Fin 6) (Fin 6) K) (c : Fin 6 → K) (d : K) :
    Matrix (Fin 7) (Fin 7) K :=
  (gram7Block C c d).submatrix (fun i => finSumFinEquiv.symm i) (fun i => finSumFinEquiv.symm i)

theorem gram7Block_symm (C : Matrix (Fin 6) (Fin 6) K) (c : Fin 6 → K) (d : K)
    (hC : C.IsSymm) : (gram7Block C c d).IsSymm := by
  apply Matrix.IsSymm.fromBlocks hC _ (by ext i j; rfl)
  ext i j
  rfl

theorem gram7_symm (C : Matrix (Fin 6) (Fin 6) K) (c : Fin 6 → K) (d : K)
    (hC : C.IsSymm) : (gram7 C c d).IsSymm := by
  have h := (gram7Block_symm C c d hC).submatrix (fun i => finSumFinEquiv.symm i)
  simpa [gram7] using h

@[expose] noncomputable def B7 (C : Matrix (Fin 6) (Fin 6) K) (c : Fin 6 → K) (d : K) :
    LinearMap.BilinForm K (Fin 7 → K) :=
  Matrix.toBilin' (gram7 C c d)

theorem B7_isSymm (C : Matrix (Fin 6) (Fin 6) K) (c : Fin 6 → K) (d : K)
    (hC : C.IsSymm) : (B7 C c d).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp only [B7, Matrix.toBilin'_apply']
  have hM : (gram7 C c d).IsSymm := gram7_symm C c d hC
  have h := Matrix.dotProduct_transpose_mulVec (A := gram7 C c d) (x := y) (y := x)
  rw [hM.eq] at h
  exact h.symm

@[simp]
theorem B7_toMatrix (C : Matrix (Fin 6) (Fin 6) K) (c : Fin 6 → K) (d : K) :
    BilinForm.toMatrix' (B7 C c d) = gram7 C c d := by
  simp [B7]

@[simp]
theorem B7_single_single (C : Matrix (Fin 6) (Fin 6) K) (c : Fin 6 → K) (d : K)
    (i j : Fin 7) :
    B7 C c d (Pi.single i 1) (Pi.single j 1) = gram7 C c d i j := by
  simp [B7]

end E6Seven

end CFSG.StandardType

namespace E6Seven

open CFSG.StandardType.E6QTwo

variable {K : Type*} [Field K]

@[expose] def emb6 (v : Fin 6 → K) : Fin 7 → K :=
  fun i => Fin.lastCases (0 : K) (fun j => v j) i

@[expose] noncomputable def reflection7 (M : Matrix (Fin 7) (Fin 7) K) (i : Fin 6) :
    (Fin 7 → K) →ₗ[K] (Fin 7 → K) :=
  Matrix.toLin' (1 - Matrix.of fun r c =>
    if r = Fin.castSucc i then M (Fin.castSucc i) c else 0)

theorem reflection7_apply (M : Matrix (Fin 7) (Fin 7) K) (i : Fin 6) (x : Fin 7 → K) :
    reflection7 M i x = x - (Matrix.mulVec M x) (Fin.castSucc i) • Pi.single (Fin.castSucc i) 1 := by
  ext r
  simp only [reflection7, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.mulVec, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, dotProduct]
  simp only [Matrix.sub_apply, Matrix.one_apply]
  by_cases h : r = Fin.castSucc i
  · simp only [h]
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single (Fin.castSucc i)]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h
        simp at h
    · simp [Matrix.of_apply]
  · simp [h]

theorem B7_reflection (M : Matrix (Fin 7) (Fin 7) K) (hM : M.IsSymm)
    (hii : ∀ i : Fin 6, M (Fin.castSucc i) (Fin.castSucc i) = 2)
    (i : Fin 6) (u v : Fin 7 → K) :
    (Matrix.toBilin' M) (reflection7 M i u) (reflection7 M i v) = (Matrix.toBilin' M) u v := by
  rw [reflection7_apply, reflection7_apply]
  set a := Matrix.mulVec M u (Fin.castSucc i)
  set b := Matrix.mulVec M v (Fin.castSucc i)
  have hBu : (Matrix.toBilin' M) u (Pi.single (Fin.castSucc i) 1) = a := by
    rw [Matrix.toBilin'_apply', Matrix.mulVec_single_one]
    simp only [a, Matrix.col, Matrix.mulVec, dotProduct]
    rw [hM.eq]
    rw [Finset.sum_congr rfl (fun j _ => mul_comm (u j) (M (Fin.castSucc i) j))]
  have hBv : (Matrix.toBilin' M) (Pi.single (Fin.castSucc i) 1) v = b := by
    rw [Matrix.toBilin'_apply']
    simp [b, single_dotProduct]
  have hBii : (Matrix.toBilin' M) (Pi.single (Fin.castSucc i) 1) (Pi.single (Fin.castSucc i) 1) = 2 := by
    rw [Matrix.toBilin'_apply', Matrix.mulVec_single_one]
    rw [single_dotProduct, one_mul]
    simp [Matrix.col, hii i]
  rw [map_sub, map_smul]
  have hB : (Matrix.toBilin' M) (u - a • Pi.single (Fin.castSucc i) 1) =
      (Matrix.toBilin' M) u - a • (Matrix.toBilin' M) (Pi.single (Fin.castSucc i) 1) := by
    simp [map_sub, map_smul]
  rw [hB]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [hBu, hBv, hBii]
  ring

end E6Seven
end

public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.StandardType.E6QTwo
open scoped Matrix

theorem gram7_castSucc_castSucc (c : Fin 6 → ZMod 3) (b : ZMod 3) (i j : Fin 6) :
    gram7 cartanE6ModThree c b i.castSucc j.castSucc = cartanE6ModThree i j := by
  simp only [gram7, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm i.castSucc = Sum.inl i from by decide +kernel +revert]
  rw [show finSumFinEquiv.symm j.castSucc = Sum.inl j from by decide +kernel +revert]
  change gram7Block cartanE6ModThree c b (Sum.inl i) (Sum.inl j) = cartanE6ModThree i j
  simp [gram7Block, Matrix.fromBlocks_apply₁₁]

theorem gram7_castSucc_last (c : Fin 6 → ZMod 3) (b : ZMod 3) (i : Fin 6) :
    gram7 cartanE6ModThree c b i.castSucc (Fin.last 6) = c i := by
  simp only [gram7, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm i.castSucc = Sum.inl i from by decide +kernel +revert]
  rw [show finSumFinEquiv.symm (Fin.last 6) = Sum.inr (0 : Fin 1) from by
    decide +kernel +revert]
  change gram7Block cartanE6ModThree c b (Sum.inl i) (Sum.inr (0 : Fin 1)) = c i
  simp [gram7Block, Matrix.fromBlocks_apply₁₂]

theorem gram7_last_last (c : Fin 6 → ZMod 3) (b : ZMod 3) :
    gram7 cartanE6ModThree c b (Fin.last 6) (Fin.last 6) = b := by
  simp only [gram7, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.last 6) = Sum.inr (0 : Fin 1) from by
    decide +kernel +revert]
  change gram7Block cartanE6ModThree c b (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)) = b
  simp [gram7Block, Matrix.fromBlocks_apply₂₂]

end E6Seven
end StandardType
end CFSG
end

namespace CFSG.StandardType
open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open CFSG.StandardType.E6Seven
open scoped Matrix

theorem e6_Bform_H_H_eq_e6dot
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    {Bform : LinearMap.BilinForm (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, Bform (h i) = α i)
    (u s : Fin 6 → ZMod 3) :
    Bform (Fintype.linearCombination (ZMod 3) h u)
      (Fintype.linearCombination (ZMod 3) h s) = e6dot (Cmul s) u := by
  have hC : C = cartanE6ModThree := by
    ext i j
    rw [C_eq_mathlib]
    simp [cartanE6ModThree]
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, hB,
    LinearMap.sum_apply, LinearMap.smul_apply,
    apply_linearCombination_eq_cartanE6ModThree hpair, hpair,
    cartanE6ModThree_symm, e6dot, Cmul,
    Finset.mul_sum, Finset.sum_mul, smul_eq_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [cartanE6ModThree_symm, hC]
  ring

end CFSG.StandardType

public section

namespace CFSG.StandardType

open CFSG.Assembly Module
open CFSG.StandardType.E6QTwo
open scoped Matrix
open _root_.E6Seven

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

namespace E6Seven

noncomputable def B7Block (C : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (c : Fin 6 → ZMod 3) (d : ZMod 3) :
    LinearMap.BilinForm (ZMod 3) (Fin 6 ⊕ Fin 1 → ZMod 3) :=
  Matrix.toBilin' (gram7Block C c d)

theorem B7_eq_B7Block (c : Fin 6 → ZMod 3) (d : ZMod 3)
    (x y : Fin 7 → ZMod 3) :
    B7 cartanE6ModThree c d x y =
      B7Block cartanE6ModThree c d
        (fun i => x (finSumFinEquiv i)) (fun i => y (finSumFinEquiv i)) := by
  simp only [B7, B7Block, gram7, Matrix.toBilin'_apply']
  rw [Matrix.submatrix_mulVec_equiv]
  rw [dotProduct_comp_equiv_symm]
  rfl

theorem exists_seven_chart_form
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hLI : LinearIndependent (ZMod 3) h)
    (hdim : Module.finrank (ZMod 3) V = 7)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (b : ZMod 3) :
    ∃ (z : V) (c : Fin 6 → ZMod 3) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
      (Bform : LinearMap.BilinForm (ZMod 3) V),
      (∀ i, chart (h i) = Pi.single i.castSucc 1) ∧
      chart z = Pi.single (Fin.last 6) 1 ∧
      (∀ i, Bform (h i) = α i) ∧
      (∀ i j, Bform (h i) (h j) = cartanE6ModThree i j) ∧
      (∀ i, Bform (h i) z = α i z) ∧
      Bform z z = b ∧
      Bform = (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap := by
  obtain ⟨z, hzLI⟩ := exists_linearIndependent_snoc_of_lt_finrank (R := ZMod 3) (v := h) hLI
    (by rw [hdim]; norm_num)
  let v : Fin 7 → V := @Fin.snoc 6 (fun _ => V) h z
  let bB : Basis (Fin 7) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank (b := v) hzLI (by simp [hdim])
  have hb : ⇑bB = v := coe_basisOfLinearIndependentOfCardEqFinrank (b := v) hzLI _
  let chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3) := bB.equivFun
  let c : Fin 6 → ZMod 3 := fun i => α i z
  let Bform : LinearMap.BilinForm (ZMod 3) V :=
    (B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap
  have hb_z : bB (Fin.last 6) = z := by
    rw [show bB (Fin.last 6) = v (Fin.last 6) from congr_fun hb (Fin.last 6)]
    change @Fin.snoc 6 (fun _ => V) h z (Fin.last 6) = z
    rw [Fin.snoc_last]
  have hchart_h : ∀ i, chart (h i) = Pi.single i.castSucc 1 := by
    intro i
    have hb_i : bB i.castSucc = h i := by
      rw [show bB i.castSucc = v i.castSucc from congr_fun hb i.castSucc]
      simp [v, Fin.snoc_castSucc]
    rw [← hb_i]
    ext j
    rw [Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  have hchart_z : chart z = Pi.single (Fin.last 6) 1 := by
    rw [← hb_z]
    ext j
    rw [Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  have hform_h : ∀ i, Bform (h i) = α i := by
    intro i
    apply Basis.ext bB
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · have hb_k : bB k.castSucc = h k := by
        rw [show bB k.castSucc = v k.castSucc from congr_fun hb k.castSucc]
        simp [v, Fin.snoc_castSucc]
      rw [hb_k]
      change B7 cartanE6ModThree c b (chart (h i)) (chart (h k)) = α i (h k)
      rw [hchart_h i, hchart_h k, B7_single_single]
      rw [gram7_castSucc_castSucc]
      exact (hpair i k).symm
    · rw [hb_z]
      change B7 cartanE6ModThree c b (chart (h i)) (chart z) = α i z
      rw [hchart_h i, hchart_z, B7_single_single]
      rw [gram7_castSucc_last]
  refine ⟨z, c, chart, Bform, hchart_h, hchart_z, hform_h, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hform_h i]
    exact hpair i j
  · intro i
    change Bform (h i) z = α i z
    rw [hform_h i]
  · change B7 cartanE6ModThree c b (chart z) (chart z) = b
    rw [hchart_z, B7_single_single]
    exact gram7_last_last c b
  · rfl

theorem chart_generator_invariant
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Bs : Subgroup G}
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (φ : Fin 6 → MulAut ↥Bs) (ι : Additive ↥Bs ≃+ V)
    (hlin : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (c : Fin 6 → ZMod 3) (b : ZMod 3)
    (hchart_h : ∀ i, chart (h i) = Pi.single i.castSucc 1)
    (hform_h : ∀ i, ((B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap)
      (h i) = α i)
    (hsymm : (gram7 cartanE6ModThree c b).IsSymm)
    (hdiag : ∀ i : Fin 6, gram7 cartanE6ModThree c b i.castSucc i.castSucc = 2)
    (i : Fin 6) :
    ∀ u v, ((B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap)
      (ggLin (p := 3) ι (φ i) u) (ggLin (p := 3) ι (φ i) v) =
      ((B7 cartanE6ModThree c b).comp chart.toLinearMap chart.toLinearMap) u v := by
  intro u v
  have hchart_action : ∀ w, chart (ggLin (p := 3) ι (φ i) w) =
      reflection7 (gram7 cartanE6ModThree c b) i (chart w) := by
    intro w
    rw [hlin i w]
    rw [map_sub, map_smul, hchart_h i]
    rw [reflection7_apply]
    congr 1
    have hB : (B7 cartanE6ModThree c b) (Pi.single i.castSucc 1) (chart w) =
        (Matrix.mulVec (gram7 cartanE6ModThree c b) (chart w)) i.castSucc := by
      simp [B7, Matrix.toBilin'_apply', single_one_dotProduct]
    rw [← hB]
    have := congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f w) (hform_h i)
    simpa [LinearMap.BilinForm.comp_apply, hchart_h i] using this.symm
  change (B7 cartanE6ModThree c b) (chart (ggLin (p := 3) ι (φ i) u))
      (chart (ggLin (p := 3) ι (φ i) v)) =
    (B7 cartanE6ModThree c b) (chart u) (chart v)
  rw [hchart_action u, hchart_action v]
  exact B7_reflection (gram7 cartanE6ModThree c b) hsymm hdiag i (chart u) (chart v)

end E6Seven

end CFSG.StandardType
end

namespace CFSG.StandardType

section KOnlyCountPrior

open CFSG.Assembly Module
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {B Bs L D J K : Subgroup G} {x y : G}

theorem ggIsTransvection_mul_of_same_functional
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} {yV zV : V} {f : Module.Dual (ZMod p) V}
    (hφ : ∀ v, ggLin (p := p) ι φ v = v - f v • yV)
    (hψ : ∀ v, ggLin (p := p) ι ψ v = v - f v • zV)
    (hp2 : p ≠ 2) (hfy : f yV = 2) (hfz : f zV = 2) (hyz : yV ≠ zV) :
    GGIsTransvection p (φ * ψ) := by
  obtain ⟨-, hf⟩ := ne_zero_of_apply_eq_two (p := p) hp2 hfy
  have hw : yV - zV ≠ 0 := sub_ne_zero.mpr hyz
  have hfw : f (yV - zV) = 0 := by rw [map_sub, hfy, hfz, sub_self]
  refine ggIsTransvection_of_apply ι hw hf hfw ?_
  intro v
  rw [map_mul, LinearEquiv.mul_apply, hψ, hφ]
  simp only [map_sub, map_smul, smul_eq_mul, hfz]
  module

theorem kOnlyE6_no_same_functional_mul
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} {yV zV : V} {f : Module.Dual (ZMod p) V}
    (hH : GGResHyp p B Bs x L D J y K)
    (hφ : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hψ : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hφlin : ∀ v, ggLin (p := p) ι φ v = v - f v • yV)
    (hψlin : ∀ v, ggLin (p := p) ι ψ v = v - f v • zV)
    (hfy : f yV = 2) (hfz : f zV = 2) (hyz : yV ≠ zV) :
    False := by
  have hmem : φ * ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := mul_mem hφ hψ
  have hmem' : φ * ψ ∈ ggAutomizerJoin L Bs {K} := by
    simpa [ggAutomizerJoin_singleton] using hmem
  have hind : φ * ψ ∈ ggInduced ⊤ Bs :=
    ggAutomizerJoin_le_ggInduced_top L {K} hmem'
  exact hH.2.2.2.1 (φ * ψ) hind
    (ggIsTransvection_mul_of_same_functional ι hφlin hψlin
      hH.1.1.2.2.2.2.2.1.2.1 hfy hfz hyz)

end KOnlyCountPrior

end CFSG.StandardType

public section

namespace CFSG.StandardType

open CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem reflection_mul_reflection_same_coroot {f f' : Module.Dual K V} {y : V}
    (hfy : f y = 2) (hfy' : f' y = 2) (v : V) :
    (reflection hfy * reflection hfy') v = v + ((f' - f) v) • y := by
  simp only [LinearEquiv.mul_apply, reflection_apply, LinearMap.sub_apply, smul_eq_mul,
    map_sub, map_smul, hfy, hfy', mul_zero, sub_zero, zero_smul]
  module

theorem reflection_conj_eq {f g : Module.Dual K V} {y z : V}
    (hfy : f y = 2) (hgz : g z = 2) (hfz : f z = 0) (v : V) :
    (reflection hfy * reflection hgz * (reflection hfy)⁻¹) v =
      v - ((g - (g y) • f) v) • z := by
  rw [reflection_inv]
  simp only [LinearEquiv.mul_apply, reflection_apply, smul_eq_mul, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, hfy, hgz, hfz, mul_zero, sub_zero, zero_smul]
  module

theorem reflection_commutator_apply {f g : Module.Dual K V} {y z : V}
    (h2 : (2 : K) ≠ 0) (hfy : f y = 2) (hgz : g z = 2) (hfz : f z = 0)
    (hgy : g y ≠ 0) (v : V) :
    (reflection hfy * reflection hgz * (reflection hfy)⁻¹ * (reflection hgz)⁻¹) v =
      v + (g y * f v) • z := by
  rw [reflection_inv hgz]
  have hconj : (reflection hfy * reflection hgz * (reflection hfy)⁻¹) =
      reflection (f := g - (g y) • f) (x := z) (by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hgz, hfz,
          mul_zero, sub_zero]) := by
    ext w
    rw [reflection_conj_eq hfy hgz hfz w, reflection_apply]
  rw [hconj]
  rw [reflection_mul_reflection_same_coroot (f := g - (g y) • f) (f' := g)
    (y := z) (by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hgz, hfz,
        mul_zero, sub_zero]) hgz]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  module

theorem ggIsTransvection_commutator_of_reflections
    {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} {y z : V} {f g : Module.Dual (ZMod p) V}
    (hφ : ∀ v, ggLin (p := p) ι φ v = v - f v • y)
    (hψ : ∀ v, ggLin (p := p) ι ψ v = v - g v • z)
    (hp2 : p ≠ 2)
    (hfy : f y = 2) (hgz : g z = 2) (hfz : f z = 0) (hgy : g y ≠ 0) :
    GGIsTransvection p (φ * ψ * φ⁻¹ * ψ⁻¹) := by
  obtain ⟨-, hf⟩ := ne_zero_of_apply_eq_two (p := p) hp2 hfy
  obtain ⟨hz, -⟩ := ne_zero_of_apply_eq_two (p := p) hp2 hgz
  have hf' : ((g y) • f : Module.Dual (ZMod p) V) ≠ 0 := smul_ne_zero hgy hf
  refine ggIsTransvection_of_apply ι (w := z) hz hf' ?_ ?_
  · simp only [LinearMap.smul_apply, smul_eq_mul, hfz, mul_zero]
  · have hφr : ggLin (p := p) ι φ = reflection hfy := LinearEquiv.ext fun v => by
      rw [hφ, reflection_apply]
    have hψr : ggLin (p := p) ι ψ = reflection hgz := LinearEquiv.ext fun v => by
      rw [hψ, reflection_apply]
    have hmap : (ggLin (p := p) ι) (φ * ψ * φ⁻¹ * ψ⁻¹) =
        (ggLin (p := p) ι φ) * (ggLin (p := p) ι ψ) *
          (ggLin (p := p) ι φ)⁻¹ * (ggLin (p := p) ι ψ)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    intro v
    rw [hmap, hφr, hψr,
      reflection_commutator_apply (K := ZMod p) (zmod_two_ne_zero hp2) hfy hgz hfz hgy v]
    simp only [LinearMap.smul_apply, smul_eq_mul, mul_comm]

theorem kOnlyE6_no_mixed_cross
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} {yV zV : V} {f g : Module.Dual (ZMod p) V}
    (hφ : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hψ : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hφlin : ∀ v, ggLin (p := p) ι φ v = v - f v • yV)
    (hψlin : ∀ v, ggLin (p := p) ι ψ v = v - g v • zV)
    (hfy : f yV = 2) (hgz : g zV = 2) (hfz : f zV = 0) (hgy : g yV ≠ 0) :
    False := by
  have hmem : φ * ψ * φ⁻¹ * ψ⁻¹ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    exact mul_mem (mul_mem (mul_mem hφ hψ) (inv_mem hφ)) (inv_mem hψ)
  have hmem' : φ * ψ * φ⁻¹ * ψ⁻¹ ∈ ggAutomizerJoin L Bs {K} := by
    simpa [ggAutomizerJoin_singleton] using hmem
  have hind : φ * ψ * φ⁻¹ * ψ⁻¹ ∈ ggInduced ⊤ Bs :=
    ggAutomizerJoin_le_ggInduced_top L {K} hmem'
  exact hH.2.2.2.1 (φ * ψ * φ⁻¹ * ψ⁻¹) hind
    (ggIsTransvection_commutator_of_reflections ι hφlin hψlin
      hH.1.1.2.2.2.2.2.1.2.1 hfy hgz hfz hgy)

theorem ggReflection_cross_zero_iff_of_resHyp
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} {yV zV : V} {f g : Module.Dual (ZMod p) V}
    (hφ : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hψ : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hφlin : ∀ v, ggLin (p := p) ι φ v = v - f v • yV)
    (hψlin : ∀ v, ggLin (p := p) ι ψ v = v - g v • zV)
    (hfy : f yV = 2) (hgz : g zV = 2) :
    f zV = 0 ↔ g yV = 0 := by
  constructor
  · intro hfz
    by_contra hgy
    exact kOnlyE6_no_mixed_cross hH ι hφ hψ hφlin hψlin hfy hgz hfz hgy
  · intro hgy
    by_contra hfz
    exact kOnlyE6_no_mixed_cross hH ι hψ hφ hψlin hφlin hgz hfy hgy hfz

end CFSG.StandardType

end
public section

namespace CFSG.StandardType

open CFSG.Assembly Module CFSG.StandardType.E6QTwo
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]
  {B Bs L D J K : Subgroup G} {x y : G}

theorem e6_actual_cross_zero_iff
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} {ha hr : V} {aa ar : Module.Dual (ZMod 3) V}
    (hφ : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hψ : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hφlin : ∀ v, ggLin (p := 3) ι φ v = v - aa v • ha)
    (hψlin : ∀ v, ggLin (p := 3) ι ψ v = v - ar v • hr)
    (hselfa : aa ha = 2) (hselfr : ar hr = 2) :
    aa hr = 0 ↔ ar ha = 0 :=
  ggReflection_cross_zero_iff_of_resHyp hH ι hφ hψ hφlin hψlin hselfa hselfr

theorem e6_actual_no_same_coroot
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    {φ ψ : MulAut ↥Bs} {f g : Module.Dual (ZMod 3) V} {z : V}
    (hφ : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hψ : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hφlin : ∀ v, ggLin (p := 3) ι φ v = v - f v • z)
    (hψlin : ∀ v, ggLin (p := 3) ι ψ v = v - g v • z)
    (hfz : f z = 2) (hgz : g z = 2) (hfg : f ≠ g) :
    False := by
  have hmem : φ * ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := mul_mem hφ hψ
  have hmem' : φ * ψ ∈ ggAutomizerJoin L Bs {K} := by
    simpa [ggAutomizerJoin_singleton] using hmem
  have hind : φ * ψ ∈ ggInduced ⊤ Bs :=
    ggAutomizerJoin_le_ggInduced_top L {K} hmem'
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hfz
    exact (by decide : (2 : ZMod 3) ≠ 0) hfz.symm
  have hne : g - f ≠ 0 := sub_ne_zero.mpr (Ne.symm hfg)
  have hzero : (g - f) z = 0 := by
    simp only [LinearMap.sub_apply, hfz, hgz, sub_self]
  have hlin : ∀ v, ggLin (p := 3) ι (φ * ψ) v = v + (g - f) v • z := by
    intro v
    have hφr : ggLin (p := 3) ι φ = reflection hfz := LinearEquiv.ext hφlin
    have hψr : ggLin (p := 3) ι ψ = reflection hgz := LinearEquiv.ext hψlin
    rw [map_mul, hφr, hψr]
    exact reflection_mul_reflection_same_coroot hfz hgz v
  exact hH.2.2.2.1 (φ * ψ) hind
    (ggIsTransvection_of_apply (p := 3) ι hz hne hzero hlin)

theorem e6_actual_added_norm2_mem
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    {φa φu : MulAut ↥Bs} {ha hu : V} {aa au : Module.Dual (ZMod 3) V}
    (hφa : φa ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hφu : φu ∈ ggAutomizer L Bs)
    (hlinA : ∀ v, ggLin (p := 3) ι φa v = v - aa v • ha)
    (hlinU : ∀ v, ggLin (p := 3) ι φu v = v - au v • hu)
    (hselfa : aa ha = 2) (hselfu : au hu = 2)
    (haeq : aa = au)
    {t : ZMod 3} {r : V}
    (hdec : ha = hu + t • r) (hr : r ≠ 0)
    :
    t = 0 ∧ φa ∈ ggAutomizer L Bs := by
  have hφujoin : φu ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    Subgroup.mem_sup_left hφu
  by_cases ht : t = 0
  · refine ⟨ht, ?_⟩
    have hha : ha = hu := by
      rw [hdec, ht, zero_smul, add_zero]
    have hlinA' : ∀ v, ggLin (p := 3) ι φa v = v - au v • hu := by
      intro v
      rw [hlinA, hha, haeq]
    have hEqLin : ggLin (p := 3) ι φa = ggLin (p := 3) ι φu :=
      LinearEquiv.ext fun v => by rw [hlinA', hlinU]
    have hEq : φa = φu := ggLin_injective (p := 3) ι hEqLin
    simpa [hEq] using hφu
  · exfalso
    have hne : ha ≠ hu := by
      intro h
      have hzero : t • r = 0 := by
        have := congrArg (fun z => z - hu) hdec
        rw [h, add_sub_cancel_left] at this
        simpa using this.symm
      exact (smul_ne_zero ht hr) hzero
    have hlinU' : ∀ v, ggLin (p := 3) ι φu v = v - aa v • hu := by
      intro v
      rw [hlinU, haeq]
    have hselfu' : aa hu = 2 := by simpa [haeq] using hselfu
    exact kOnlyE6_no_same_functional_mul (p := 3) ι hH hφa hφujoin
      hlinA hlinU' hselfa hselfu' hne

theorem e6_actual_added_norm1_false
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    {φa φg : MulAut ↥Bs} {h : V} {a : Module.Dual (ZMod 3) V} {r : V}
    (hφa : φa ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hφg : φg ∈ ggAutomizer L Bs)
    (hlinA : ∀ v, ggLin (p := 3) ι φa v = v - a v • h)
    (hself : a h = 2)
    (hgh : ggLin (p := 3) ι φg h = h + r)
    (hdual : ∀ v, a (ggLin (p := 3) ι φg v) = a v)
    (hr : r ≠ 0) :
    False := by
  let φc : MulAut ↥Bs := φg * φa * φg⁻¹
  have hφc : φc ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    have hjoin : ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := le_sup_left
    exact mul_mem (mul_mem (hjoin hφg) hφa) (inv_mem (hjoin hφg))
  have hlinC : ∀ v, ggLin (p := 3) ι φc v = v - a v • (h + r) := by
    intro v
    have hglin : ggLin (p := 3) ι φg⁻¹ v =
        (ggLin (p := 3) ι φg).symm v := by
      have hmap : ggLin (p := 3) ι φg⁻¹ = (ggLin (p := 3) ι φg)⁻¹ :=
        map_inv (ggLin (p := 3) ι) φg
      rw [hmap]
      rfl
    have hdual' : a ((ggLin (p := 3) ι φg).symm v) = a v := by
      have h := hdual ((ggLin (p := 3) ι φg).symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
    calc
      ggLin (p := 3) ι φc v
          = ggLin (p := 3) ι φg (ggLin (p := 3) ι φa
              (ggLin (p := 3) ι φg⁻¹ v)) := by
              simp only [φc, map_mul, LinearEquiv.mul_apply]
      _ = ggLin (p := 3) ι φg (ggLin (p := 3) ι φg⁻¹ v - a v • h) := by
              rw [hlinA]
              congr 1
              rw [hglin, hdual']
      _ = v - a v • (h + r) := by
              have hg : ggLin (p := 3) ι φg (ggLin (p := 3) ι φg⁻¹ v) = v := by
                rw [hglin]
                exact LinearEquiv.apply_symm_apply _ _
              rw [map_sub, map_smul, hg, hgh]
  have hne : h ≠ h + r := by
    intro hh
    have : r = 0 := by
      have h' := congrArg (fun z => z - h) hh.symm
      simpa using h' 
    exact hr this
  have hselfC : a (h + r) = 2 := by
    rw [← hgh, hdual, hself]
  exact kOnlyE6_no_same_functional_mul (p := 3) ι hH hφa hφc hlinA hlinC
    hself hselfC hne

theorem e6_common_kernel_eq_span_of_independent
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {x : V}
    (hh : LinearIndependent (ZMod 3) h)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hx0 : x ≠ 0) (hx : ∀ i, α i x = 0) :
    ∀ v, (∀ i, α i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {x} := by
  classical
  let x0 : V := Fintype.linearCombination (ZMod 3) h cartanE6KernelVec
  have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hh, Fintype.card_fin, hdim]
  have hsurj : Function.Surjective (Fintype.linearCombination (ZMod 3) h) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  have hxrepr : ∃ cx : Fin 6 → ZMod 3,
      Fintype.linearCombination (ZMod 3) h cx = x := hsurj x
  obtain ⟨cx, hcx⟩ := hxrepr
  have hcxC : cartanE6ModThree *ᵥ cx = 0 := by
    ext i
    have h' := congrArg (fun v => α i v) hcx
    rw [hx i] at h'
    rwa [apply_linearCombination_eq_cartanE6ModThree hpair i cx] at h'
  have hcxn : cx = cx 0 • cartanE6KernelVec := eq_smul_cartanE6KernelVec cx hcxC
  have hcx0 : cx 0 ≠ 0 := by
    intro h0
    apply hx0
    rw [← hcx, hcxn, h0, zero_smul]
    simp
  have hx' : x = cx 0 • x0 := by
    calc
      x = Fintype.linearCombination (ZMod 3) h cx := hcx.symm
      _ = Fintype.linearCombination (ZMod 3) h (cx 0 • cartanE6KernelVec) :=
            congrArg (fun v => Fintype.linearCombination (ZMod 3) h v) hcxn
      _ = cx 0 • Fintype.linearCombination (ZMod 3) h cartanE6KernelVec :=
            map_smul (Fintype.linearCombination (ZMod 3) h) (cx 0) cartanE6KernelVec
      _ = cx 0 • x0 := rfl
  have hx0inv : x0 = (cx 0)⁻¹ • x := by
    calc
      x0 = (cx 0)⁻¹ • (cx 0 • x0) := by
            rw [smul_smul, inv_mul_cancel₀ hcx0, one_smul]
      _ = (cx 0)⁻¹ • x := by rw [← hx']
  intro v
  constructor
  · intro hv
    obtain ⟨c, hcv⟩ := hsurj v
    have hcC : cartanE6ModThree *ᵥ c = 0 := by
      ext i
      have h' := congrArg (fun v => α i v) hcv
      rw [hv i] at h'
      rwa [apply_linearCombination_eq_cartanE6ModThree hpair i c] at h'
    have hcn : c = c 0 • cartanE6KernelVec := eq_smul_cartanE6KernelVec c hcC
    have hv' : v = c 0 • x0 := by
      calc
        v = Fintype.linearCombination (ZMod 3) h c := hcv.symm
        _ = Fintype.linearCombination (ZMod 3) h (c 0 • cartanE6KernelVec) :=
              congrArg (fun v => Fintype.linearCombination (ZMod 3) h v) hcn
        _ = c 0 • Fintype.linearCombination (ZMod 3) h cartanE6KernelVec :=
              map_smul (Fintype.linearCombination (ZMod 3) h) (c 0) cartanE6KernelVec
        _ = c 0 • x0 := rfl
    rw [hv', hx0inv, smul_smul]
    exact Submodule.mem_span_singleton.mpr ⟨c 0 * (cx 0)⁻¹, rfl⟩
  · intro hv
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    intro i
    rw [map_smul, hx i, smul_zero]

theorem e6_actual_independent_six_chart
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ Λa : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs}
    {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod 3) V}
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hCL : GGIntCartan ML CL)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e)
    (hind : LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)))
    (hcard : Nat.card Bs = 3 ^ 6) :
    ∃ (s : ZMod 3) (ec : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)),
      s ≠ 0 ∧
      ec (ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs))) = cartanE6KernelVec ∧
      (∀ i : Fin 6, ec (h (Sum.inl (e i))) = s • Pi.single i 1) ∧
      ∀ i v, ec (ggLin (p := 3) ι (φ (Sum.inl (e i))) v) =
        ec v - (∑ j : Fin 6, ec v j * (CartanMatrix.E 6 i j : ZMod 3)) • Pi.single i 1 := by
  classical
  let h' : Fin 6 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let xV : V := ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs))
  have hpair' : ∀ i j : Fin 6, α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML]
  have hli' : LinearIndependent (ZMod 3) h' := by
    have hinj : Function.Injective (fun i : Fin 6 => Sum.inl (e i) : Fin 6 → Λ ⊕ Λa) := by
      intro i j hij
      exact e.injective (Sum.inl.inj hij)
    simpa [h', Function.comp_def] using hind.comp e e.injective
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hVcard : Nat.card V = 3 ^ 6 := by
    rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Additive.toMul, hcard]
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hVpow : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
      simpa using (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V))
    have hpow : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 6 := hVpow.symm.trans hVcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hxVne : xV ≠ 0 := by
    intro h0
    have h0' : ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs)) = 0 := by
      simpa [xV] using h0
    have h1 : (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) = 1 := by
      have h2 : Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) = 0 :=
        ι.injective (h0'.trans (map_zero ι).symm)
      simpa using (Additive.ofMul.injective h2)
    have hx1 : x ≠ 1 := by
      have hS : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
      exact hS.2.2.1
    exact hx1 (congrArg (fun z : ↥Bs => (z : G)) h1)
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) :=
    hH.1.tableB_facts.2.2.2.1
  have hxα : ∀ i : Fin 6, α' i xV = 0 := by
    intro i
    let φi : MulAut ↥Bs := φ (Sum.inl (e i))
    have hφi : φi ∈ ggAutomizer L Bs := by
      rw [hclosL]
      exact Subgroup.subset_closure ⟨e i, rfl⟩
    have hfixb : φi ⟨x, hH.1.tableB_facts.2.2.1⟩ =
        ⟨x, hH.1.tableB_facts.2.2.1⟩ :=
      CFSG.StandardType.E6Dep.ggAutomizer_fix_of_centralizes
        (Bs := Bs) (K := L) (y := x) hH.1.tableB_facts.2.2.1 hLx φi hφi
    have hfixV : ggLin (p := 3) ι φi xV = xV := by
      rw [show xV = ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs)) from rfl,
        ggLin_apply_ofMul, hfixb]
    have hlinx := hlin (Sum.inl (e i)) xV
    rw [hfixV] at hlinx
    have hzero : α' i xV • h' i = 0 := by
      have hlinx' : xV = xV - α' i xV • h' i := by
        simpa only [α', h'] using hlinx
      have hadd : xV + α' i xV • h' i = xV + 0 := by
        simpa only [add_zero] using (eq_sub_iff_add_eq.mp hlinx')
      exact add_left_cancel hadd
    have hi : h' i ≠ 0 := by
      intro h0
      have hsum : (∑ j : Fin 6, (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) j • h' j) = 0 := by
        simpa [h0] using congrArg (fun z => z) h0
      have hcoord := (Fintype.linearIndependent_iff.mp hli') (Pi.single i 1) hsum i
      simpa using hcoord
    exact (smul_eq_zero.mp hzero).resolve_right hi
  have hker : ∀ v : V, (∀ i : Fin 6, α' i v = 0) ↔
      v ∈ Submodule.span (ZMod 3) {xV} :=
    e6_common_kernel_eq_span_of_independent hli' hdim hpair' hxVne hxα
  obtain ⟨s, ec, hs, hex, heh, heact⟩ :=
    exists_e6_independent_six_coordinates h' α' xV hli' hdim hker hpair'
  refine ⟨s, ec, hs, hex, heh, ?_⟩
  intro i v
  rw [hlin (Sum.inl (e i)) v]
  exact heact i v

end CFSG.StandardType

end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]
  {B Bs L D J K : Subgroup G} {x y : G}

theorem e6_actual_insideU_eq_of_same_coroot
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    {F R : MulAut ↥Bs} {ha : V}
    {aa ar : Module.Dual (ZMod 3) V}
    (hFjoin : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hRjoin : R ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • ha)
    (hRlin : ∀ v, ggLin (p := 3) ι R v = v - ar v • ha)
    (hselfF : aa ha = 2) (hselfR : ar ha = 2) :
    F = R := by
  by_contra hne
  have hne' : aa ≠ ar := by
    intro h
    apply hne
    apply ggLin_injective (p := 3) ι
    ext v
    rw [hFlin v, hRlin v, h]
  exact e6_actual_no_same_coroot hH ι hFjoin hRjoin hFlin hRlin hselfF hselfR hne'

theorem e6_actual_insideU_membership_of_same_coroot
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    {F R : MulAut ↥Bs} {ha : V}
    {aa ar : Module.Dual (ZMod 3) V}
    (hFjoin : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hRmem : R ∈ ggAutomizer L Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • ha)
    (hRlin : ∀ v, ggLin (p := 3) ι R v = v - ar v • ha)
    (hselfF : aa ha = 2) (hselfR : ar ha = 2) :
    F ∈ ggAutomizer L Bs := by
  have hRjoin : R ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    Subgroup.mem_sup_left hRmem
  rw [e6_actual_insideU_eq_of_same_coroot hH ι hFjoin hRjoin hFlin hRlin hselfF hselfR]
  exact hRmem

end CFSG.StandardType

end

end

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Blueprint.Chevalley

@[expose] def e6C : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, -1, 0, 0, 0;
     0, 2, 0, -1, 0, 0;
     -1, 0, 2, -1, 0, 0;
     0, -1, -1, 2, -1, 0;
     0, 0, 0, -1, 2, -1;
     0, 0, 0, 0, -1, 2]

@[expose] def e6SelIdx : Fin 16 → Fin 72 :=
  ![5, 4, 3, 2, 1, 0, 49, 58, 55, 68, 9, 35, 7, 25, 52, 39]

@[expose] def e6SelList : List (Fin 6 → ZMod 3) :=
  [![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0],
   ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
   ![1, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 0],
   ![1, 1, 2, 0, 2, 1], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 1],
   ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1], ![0, 1, 1, 2, 1, 1],
   ![1, 1, 1, 1, 1, 0]]

@[expose] def e6SelVec (k : Fin 16) : Fin 6 → ZMod 3 :=
  e6SelList.getD k.val (fun _ => 0)

theorem e6SelVec_eq_root (k : Fin 16) :
    e6SelVec k = fun i => ((e6RootVec (e6SelIdx k).val i : ℤ) : ZMod 3) := by
  fin_cases k <;> funext i <;> fin_cases i <;> decide +kernel

@[expose] def e6CH (h : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  fun i => ∑ j, ((e6C i j : ℤ) : ZMod 3) * h j

@[expose] def e6Eval (v root : Fin 6 → ZMod 3) : ZMod 3 :=
  ∑ i, v i * root i

@[expose] def e6RootPair (root h : Fin 6 → ZMod 3) : ZMod 3 :=
  e6Eval (e6CH h) root

private def e6Norm (v : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  if h0 : v 0 ≠ 0 then (v 0)⁻¹ • v
  else if h1 : v 1 ≠ 0 then (v 1)⁻¹ • v
  else if h2 : v 2 ≠ 0 then (v 2)⁻¹ • v
  else if h3 : v 3 ≠ 0 then (v 3)⁻¹ • v
  else if h4 : v 4 ≠ 0 then (v 4)⁻¹ • v
  else if h5 : v 5 ≠ 0 then (v 5)⁻¹ • v
  else 0

private theorem e6Norm_scale :
    ∀ v : Fin 6 → ZMod 3, v ≠ 0 →
      ∃ c : ZMod 3, c ≠ 0 ∧ v = c • e6Norm v := by
  decide +kernel

private theorem e6Norm_idem :
    ∀ v : Fin 6 → ZMod 3, e6Norm (e6Norm v) = e6Norm v := by
  decide +kernel

private def e6Reps : Finset (Fin 6 → ZMod 3) :=
  Finset.univ.filter fun v => e6Norm v = v

private theorem e6Norm_mem_reps (v : Fin 6 → ZMod 3) : e6Norm v ∈ e6Reps := by
  rw [e6Reps, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, e6Norm_idem v⟩

private def e6Key (v : Fin 6 → ZMod 3) : ℕ :=
  ∑ k : Fin 16, if e6Eval v (e6SelVec k) = 0 then 2 ^ (k : ℕ) else 0

private theorem e6Key_eq_of_pattern {u v : Fin 6 → ZMod 3}
    (h : ∀ k : Fin 16, e6Eval u (e6SelVec k) = 0 ↔ e6Eval v (e6SelVec k) = 0) :
    e6Key u = e6Key v := by
  unfold e6Key
  apply Finset.sum_congr rfl
  intro k _
  by_cases hu : e6Eval u (e6SelVec k) = 0
  · have hv : e6Eval v (e6SelVec k) = 0 := (h k).mp hu
    simp [hu, hv]
  · have hv : e6Eval v (e6SelVec k) ≠ 0 := fun hv => hu ((h k).mpr hv)
    simp [hu, hv]

private theorem e6SelVec_spanning :
    ∀ v : Fin 6 → ZMod 3, (∀ k : Fin 16, e6Eval v (e6SelVec k) = 0) → v = 0 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6Reps_key_inj :
    ∀ u : Fin 6 → ZMod 3, u ∈ e6Reps →
      ∀ v : Fin 6 → ZMod 3, v ∈ e6Reps →
        e6Key u = e6Key v → u = v := by
  decide +kernel

private theorem e6Eval_smul_zero_iff (c : ZMod 3) (hc : c ≠ 0)
    (v r : Fin 6 → ZMod 3) :
    e6Eval (c • v) r = 0 ↔ e6Eval v r = 0 := by
  unfold e6Eval
  rw [show (∑ i, (c • v) i * r i) = c * ∑ i, v i * r i by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring]
  rw [mul_eq_zero]
  simp [hc]

theorem e6SelVec_separates :
    ∀ u v : Fin 6 → ZMod 3,
      (∀ k : Fin 16, e6Eval u (e6SelVec k) = 0 ↔
        e6Eval v (e6SelVec k) = 0) →
      ∃ mu : ZMod 3, u = mu • v := by
  intro u v hpat
  by_cases hv0 : v = 0
  · have hu0 : u = 0 := by
      apply e6SelVec_spanning u
      intro k
      have hvk : e6Eval v (e6SelVec k) = 0 := by simp [hv0, e6Eval]
      exact (hpat k).mpr hvk
    exact ⟨0, by simp [hu0, hv0]⟩
  · have hu0 : u ≠ 0 := by
      intro hu
      apply hv0
      apply e6SelVec_spanning v
      intro k
      have huk : e6Eval u (e6SelVec k) = 0 := by simp [hu, e6Eval]
      exact (hpat k).mp huk
    obtain ⟨cu, hcu, huc⟩ := e6Norm_scale u hu0
    obtain ⟨cv, hcv, hvc⟩ := e6Norm_scale v hv0
    have hpatN : ∀ k : Fin 16,
        e6Eval (e6Norm u) (e6SelVec k) = 0 ↔
          e6Eval (e6Norm v) (e6SelVec k) = 0 := by
      intro k
      rw [← e6Eval_smul_zero_iff cu hcu (e6Norm u) (e6SelVec k),
        ← e6Eval_smul_zero_iff cv hcv (e6Norm v) (e6SelVec k)]
      rw [← huc, ← hvc]
      exact hpat k
    have hkey : e6Key (e6Norm u) = e6Key (e6Norm v) :=
      e6Key_eq_of_pattern hpatN
    have hnorm : e6Norm u = e6Norm v :=
      e6Reps_key_inj (e6Norm u) (e6Norm_mem_reps u)
        (e6Norm v) (e6Norm_mem_reps v) hkey
    have hvc' : e6Norm v = cv⁻¹ • v := by
      calc
        e6Norm v = cv⁻¹ • (cv • e6Norm v) := by
          rw [smul_smul, inv_mul_cancel₀ hcv, one_smul]
        _ = cv⁻¹ • v := by rw [← hvc]
    refine ⟨cu * cv⁻¹, ?_⟩
    calc
      u = cu • e6Norm u := huc
      _ = cu • e6Norm v := by rw [hnorm]
      _ = cu • (cv⁻¹ • v) := by rw [hvc']
      _ = (cu * cv⁻¹) • v := by rw [smul_smul]

theorem e6_zero_pattern_proportional
    (h a : Fin 6 → ZMod 3)
    (hpat : ∀ m : Fin 72,
      (∑ i, a i * ((e6RootVec m i : ℤ) : ZMod 3) = 0) ↔
      e6RootPair (fun i => ((e6RootVec m i : ℤ) : ZMod 3)) h = 0) :
    ∃ mu : ZMod 3, a = mu • e6CH h := by
  apply e6SelVec_separates a (e6CH h)
  intro k
  rw [e6SelVec_eq_root k]
  simpa [e6Eval, e6RootPair] using hpat (e6SelIdx k)

end CFSG.StandardType

end

public section

namespace CFSG.StandardType.E6InsideSpanNormalizer

open CFSG.StandardType.E6NormWordOrbit
open scoped Matrix

@[expose] def refl (w v : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  v - (((2 : ZMod 3) * (norm w)⁻¹) * (∑ i, Cmul w i * v i)) • w

theorem refl_apply (w v : Fin 6 → ZMod 3) :
    refl w v = v - (((2 : ZMod 3) * (norm w)⁻¹) *
      (∑ i, Cmul w i * v i)) • w := rfl

@[expose] def rootSet : Nat :=
  rootList.foldl
    (fun acc l => acc ||| 1 <<< vecKey (fun i => l.getD i.val 0)) 0

@[expose] def isRoot (v : Fin 6 → ZMod 3) : Bool :=
  rootSet.testBit (vecKey v)

theorem isRoot_iff_rootVec :
    ∀ v : Fin 6 → ZMod 3, isRoot v = true ↔ ∃ m : Fin 72, rootVec m = v := by
  decide +kernel

theorem refl_test_iff_bits :
    ∀ w : Fin 6 → ZMod 3, norm w ≠ 0 →
      ((∀ i j : Fin 6,
          isRoot (refl w (s i (refl w (unitRoot j)))) = true) ↔
        isRoot w = true) := by
  decide +kernel

theorem refl_test_iff (w : Fin 6 → ZMod 3) (hn : norm w ≠ 0) :
    ((∀ i j : Fin 6,
        ∃ m : Fin 72, rootVec m = refl w (s i (refl w (unitRoot j)))) ↔
      ∃ m : Fin 72, rootVec m = w) := by
  simp only [← isRoot_iff_rootVec]
  exact refl_test_iff_bits w hn

end CFSG.StandardType.E6InsideSpanNormalizer

end

public section

namespace CFSG.StandardType

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e6SixCanonical_Cmul_eq_e6CH (v : Fin 6 → ZMod 3) :
    Cmul v = e6CH v := rfl

variable {G : Type} [Group G] [Finite G] {Bs : Subgroup G}

@[simp] theorem applyWord_nil (v : Fin 6 → ZMod 3) : applyWord ([] : List (Fin 6)) v = v := rfl

@[simp] theorem applyWord_cons (i : Fin 6) (is : List (Fin 6)) (v : Fin 6 → ZMod 3) :
    applyWord (i :: is) v = applyWord is (s i v) := rfl

theorem C_symm : ∀ i j : Fin 6, C i j = C j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem e6dot_Cmul_s (i : Fin 6) (u v : Fin 6 → ZMod 3) :
    e6dot (Cmul u) (s i v) = e6dot (Cmul (s i u)) v := by
  fin_cases i <;>
    simp [e6dot, Cmul, s, sDual, C, Cℤ, unitRoot, Pi.single_apply, Fin.sum_univ_six] <;>
    ring

theorem e6dot_Cmul_foldl : ∀ (w : List (Fin 6)) (u v : Fin 6 → ZMod 3),
    e6dot (Cmul u) (w.foldl (fun v i => s i v) v) =
    e6dot (Cmul (w.reverse.foldl (fun u i => s i u) u)) v
  | [], u, v => rfl
  | i :: is, u, v => by
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [e6dot_Cmul_foldl is u (s i v)]
      rw [e6dot_Cmul_s i (is.reverse.foldl (fun u i => s i u) u) v]

theorem e6dot_Cmul_applyWord (w : List (Fin 6)) (u v : Fin 6 → ZMod 3) :
    e6dot (Cmul u) (applyWord w v) = e6dot (Cmul (applyWord w.reverse u)) v :=
  e6dot_Cmul_foldl w u v

theorem C_diag (i : Fin 6) : C i i = 2 := by
  fin_cases i <;> rfl

theorem Cmul_sub (u v : Fin 6 → ZMod 3) : Cmul (u - v) = Cmul u - Cmul v := by
  rw [Cmul_eq_mulVec, Cmul_eq_mulVec, Cmul_eq_mulVec, Matrix.mulVec_sub]

theorem Cmul_smul (c : ZMod 3) (v : Fin 6 → ZMod 3) : Cmul (c • v) = c • Cmul v := by
  rw [Cmul_eq_mulVec, Cmul_eq_mulVec, Matrix.mulVec_smul]

theorem s_sub (i : Fin 6) (u v : Fin 6 → ZMod 3) : s i (u - v) = s i u - s i v := by
  simp only [s, Cmul_sub, Pi.sub_apply, sub_smul]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply]
  ring

theorem s_smul (i : Fin 6) (c : ZMod 3) (v : Fin 6 → ZMod 3) :
    s i (c • v) = c • s i v := by
  simp only [s, Cmul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem applyWord_sub : ∀ (w : List (Fin 6)) (u v : Fin 6 → ZMod 3),
    applyWord w (u - v) = applyWord w u - applyWord w v
  | [], u, v => rfl
  | i :: is, u, v => by
      rw [applyWord_cons, applyWord_cons, applyWord_cons, s_sub]
      exact applyWord_sub is (s i u) (s i v)

theorem applyWord_smul : ∀ (w : List (Fin 6)) (c : ZMod 3) (v : Fin 6 → ZMod 3),
    applyWord w (c • v) = c • applyWord w v
  | [], c, v => rfl
  | i :: is, c, v => by
      rw [applyWord_cons, applyWord_cons, s_smul]
      exact applyWord_smul is c (s i v)

theorem applyWord_append (w₁ w₂ : List (Fin 6)) (v : Fin 6 → ZMod 3) :
    applyWord (w₁ ++ w₂) v = applyWord w₂ (applyWord w₁ v) := by
  simp only [applyWord, List.foldl_append]

theorem s_involutive (i : Fin 6) (v : Fin 6 → ZMod 3) : s i (s i v) = v := by
  have hC : Cmul (s i v) i = - Cmul v i := by
    rw [Cmul_s]
    simp only [sDual, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [C_diag]
    ring
  calc
    s i (s i v) = s i v - (Cmul (s i v) i) • unitRoot i := rfl
    _ = s i v - (- Cmul v i) • unitRoot i := by rw [hC]
    _ = (v - Cmul v i • unitRoot i) + Cmul v i • unitRoot i := by
          rw [s, neg_smul, sub_neg_eq_add]
    _ = v := by module

theorem applyWord_reverse_applyWord : ∀ (w : List (Fin 6)) (v : Fin 6 → ZMod 3),
    applyWord w.reverse (applyWord w v) = v
  | [], v => rfl
  | i :: is, v => by
      rw [List.reverse_cons, applyWord_append]
      change s i (applyWord is.reverse (applyWord is (s i v))) = v
      rw [applyWord_reverse_applyWord is (s i v), s_involutive]

theorem applyWord_applyWord_reverse (w : List (Fin 6)) (v : Fin 6 → ZMod 3) :
    applyWord w (applyWord w.reverse v) = v := by
  simpa using applyWord_reverse_applyWord w.reverse v

theorem e6dot_Cmul_unitRoot (i : Fin 6) (v : Fin 6 → ZMod 3) :
    e6dot (Cmul (unitRoot i)) v = Cmul v i := by
  fin_cases i <;>
    simp [e6dot, Cmul, unitRoot, Pi.single_apply, Fin.sum_univ_six, C, Cℤ] <;>
    ring

theorem applyWord_conj_s (w : List (Fin 6)) (i0 : Fin 6)
    (x beta : Fin 6 → ZMod 3)
    (hbeta : applyWord w (unitRoot i0) = beta)
    (hfun : ∀ y, e6dot (Cmul (unitRoot i0)) (applyWord w.reverse y) = e6dot (Cmul beta) y) :
    applyWord w (s i0 (applyWord w.reverse x)) =
      x - e6dot (Cmul beta) x • beta := by
  rw [s, applyWord_sub, applyWord_smul, applyWord_applyWord_reverse, hbeta]
  rw [show Cmul (applyWord w.reverse x) i0 =
      e6dot (Cmul (unitRoot i0)) (applyWord w.reverse x) from
    (e6dot_Cmul_unitRoot i0 (applyWord w.reverse x)).symm]
  rw [hfun x]

theorem s_add (i : Fin 6) (u v : Fin 6 → ZMod 3) : s i (u + v) = s i u + s i v := by
  simp only [s, Cmul_add, Pi.add_apply, add_mul, add_smul]
  module

theorem applyWord_add : ∀ (w : List (Fin 6)) (u v : Fin 6 → ZMod 3),
    applyWord w (u + v) = applyWord w u + applyWord w v
  | [], u, v => rfl
  | i :: is, u, v => by
      rw [applyWord_cons, applyWord_cons, applyWord_cons, s_add]
      exact applyWord_add is (s i u) (s i v)

theorem C_isSymm : C.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply]
  exact (C_symm i j).symm

theorem e6dot_comm (u v : Fin 6 → ZMod 3) : e6dot u v = e6dot v u := by
  simp [e6dot, mul_comm]

theorem e6dot_Cmul_swap (u v : Fin 6 → ZMod 3) :
    e6dot (Cmul u) v = e6dot (Cmul v) u := by
  rw [e6dot_comm (Cmul u) v, e6dot_comm (Cmul v) u]
  have h := C_isSymm.dotProduct_mulVec_comm (x := v) (y := u)
  simpa [e6dot, Cmul_eq_mulVec, dotProduct] using h

theorem e6dot_Cmul_self (u : Fin 6 → ZMod 3) : e6dot (Cmul u) u = norm u := by
  change (∑ i, Cmul u i * u i) = ∑ i, u i * Cmul u i
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem e6dotLin_apply (u v : Fin 6 → ZMod 3) : e6dotLin u v = e6dot u v := rfl

theorem r_ne_zero : r ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Fin 6 → ZMod 3 => v 0) h
  norm_num [r] at h0

theorem norm_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have h : ∀ y : ZMod 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  exact h x

@[simp] theorem e6WordAut_nil {ι : Type} (φ : ι → MulAut ↥Bs) :
    e6WordAut φ ([] : List ι) = 1 := rfl

@[simp] theorem e6WordAut_cons {ι : Type} (φ : ι → MulAut ↥Bs) (i : ι) (is : List ι) :
    e6WordAut φ (i :: is) = e6WordAut φ is * φ i := rfl

theorem e6WordAut_append {ι : Type} (φ : ι → MulAut ↥Bs) (w₁ w₂ : List ι) :
    e6WordAut φ (w₁ ++ w₂) = e6WordAut φ w₂ * e6WordAut φ w₁ := by
  induction w₁ with
  | nil => simp
  | cons i is ih =>
      rw [List.cons_append, e6WordAut_cons, e6WordAut_cons, ih, mul_assoc]

theorem e6WordAut_reverse {ι : Type} (φ : ι → MulAut ↥Bs)
    (hinv : ∀ i, φ i * φ i = 1) (w : List ι) :
    e6WordAut φ w.reverse = (e6WordAut φ w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons i is ih =>
      rw [List.reverse_cons, e6WordAut_append, ih]
      simp only [e6WordAut_cons, e6WordAut_nil, one_mul, mul_one]
      rw [mul_inv_rev]
      have hi : (φ i)⁻¹ = φ i := inv_eq_of_mul_eq_one_right (hinv i)
      rw [hi]

theorem e6WordAut_act {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    {ec : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)}
    (hact : ∀ i v, ec (ggLin (p := 3) ι (φL i) v) = s i (ec v))
    (w : List (Fin 6)) (v : V) :
    ec (ggLin (p := 3) ι (e6WordAut φL w) v) = applyWord w (ec v) := by
  induction w generalizing v with
  | nil => simp
  | cons i is ih =>
      rw [e6WordAut_cons, map_mul, LinearEquiv.mul_apply, ih, hact, applyWord_cons]

theorem e6WordAut_mem {A : Subgroup (MulAut ↥Bs)} {φL : Fin 6 → MulAut ↥Bs}
    (hgen : ∀ i, φL i ∈ A) (w : List (Fin 6)) : e6WordAut φL w ∈ A := by
  induction w with
  | nil => simp
  | cons i is ih =>
      rw [e6WordAut_cons]
      exact mul_mem ih (hgen i)

theorem e6RootRefl_mem {A : Subgroup (MulAut ↥Bs)} {φL : Fin 6 → MulAut ↥Bs}
    (hgen : ∀ i, φL i ∈ A) (i0 : Fin 6) (w : List (Fin 6)) :
    e6RootRefl φL i0 w ∈ A := by
  rw [e6RootRefl]
  exact mul_mem (mul_mem (e6WordAut_mem hgen w) (hgen i0))
    (inv_mem (e6WordAut_mem hgen w))

theorem e6RootRefl_act {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    {ec : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)}
    (hact : ∀ i v, ec (ggLin (p := 3) ι (φL i) v) = s i (ec v))
    (hinv : ∀ i, φL i * φL i = 1)
    (i0 : Fin 6) (w : List (Fin 6)) (beta : Fin 6 → ZMod 3)
    (hbeta : applyWord w (unitRoot i0) = beta) (v : V) :
    ec (ggLin (p := 3) ι (e6RootRefl φL i0 w) v) =
      ec v - e6dot (Cmul beta) (ec v) • beta := by
  have hfun : ∀ y : Fin 6 → ZMod 3,
      e6dot (Cmul (unitRoot i0)) (applyWord w.reverse y) = e6dot (Cmul beta) y := by
    intro y
    rw [e6dot_Cmul_applyWord w.reverse (unitRoot i0) y, List.reverse_reverse, hbeta]
  have hGinv_act : ∀ z : V,
      ec (ggLin (p := 3) ι (e6WordAut φL w)⁻¹ z) =
        applyWord w.reverse (ec z) := by
    intro z
    rw [map_inv]
    have h := e6WordAut_act (V := V) (ι := ι) (φL := φL) (ec := ec) hact w.reverse z
    rw [e6WordAut_reverse (φ := φL) hinv w] at h
    simpa only [map_inv] using h
  let X : V := ggLin (p := 3) ι (e6WordAut φL w)⁻¹ v
  have hX : ec X = applyWord w.reverse (ec v) := hGinv_act v
  have hR : ggLin (p := 3) ι (φL i0) X = ec.symm (s i0 (ec X)) := by
    apply ec.injective
    rw [LinearEquiv.apply_symm_apply, hact]
  calc
    ec (ggLin (p := 3) ι (e6RootRefl φL i0 w) v)
        = ec (ggLin (p := 3) ι (e6WordAut φL w)
            (ggLin (p := 3) ι (φL i0) X)) := by
            simp only [e6RootRefl, X, map_mul, map_mul, map_inv,
              LinearEquiv.mul_apply]
    _ = ec (ggLin (p := 3) ι (e6WordAut φL w)
            (ec.symm (s i0 (ec X)))) := by rw [hR]
    _ = applyWord w (ec (ec.symm (s i0 (ec X)))) :=
            e6WordAut_act (V := V) (ι := ι) (φL := φL) (ec := ec) hact w _
    _ = applyWord w (s i0 (ec X)) := by
            rw [LinearEquiv.apply_symm_apply]
    _ = applyWord w (s i0 (applyWord w.reverse (ec v))) := by
            rw [hX]
    _ = ec v - e6dot (Cmul beta) (ec v) • beta :=
            applyWord_conj_s w i0 (ec v) beta hbeta hfun

variable {B L D J K : Subgroup G} {x y : G}

theorem e6_added_mem_of_chart
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {φL : Fin 6 → MulAut ↥Bs}
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    (hinv : ∀ i, φL i * φL i = 1)
    (ec : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3))
    (hact : ∀ i v, ec (ggLin (p := 3) ι (φL i) v) = s i (ec v))
    {φa : MulAut ↥Bs} {ha : V} {aa : Module.Dual (ZMod 3) V}
    (hφa : φa ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hlinA : ∀ v, ggLin (p := 3) ι φa v = v - aa v • ha)
    (hselfa : aa ha = 2) :
    φa ∈ ggAutomizer L Bs := by
  classical
  let w : Fin 6 → ZMod 3 := ec ha
  let a' : Module.Dual (ZMod 3) (Fin 6 → ZMod 3) :=
    aa.comp (ec.symm : (Fin 6 → ZMod 3) →ₗ[ZMod 3] V)
  let aCoord : Fin 6 → ZMod 3 := fun i => a' (fun j => if i = j then 1 else 0)
  have ha'_apply : ∀ u : Fin 6 → ZMod 3, a' u = ∑ i, aCoord i * u i := by
    intro u
    rw [LinearMap.pi_apply_eq_sum_univ a' u]
    simp only [aCoord, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hself' : a' w = 2 := by
    simpa [a', w] using hselfa
  let ψ : Fin 72 → MulAut ↥Bs := fun m => e6RootRefl φL 0 (rootPath m)
  let ar : Fin 72 → Module.Dual (ZMod 3) V := fun m =>
    (e6dotLin (Cmul (rootVec m))).comp
      (ec : V →ₗ[ZMod 3] (Fin 6 → ZMod 3))
  have hψmem : ∀ m, ψ m ∈ ggAutomizer L Bs := by
    intro m
    exact e6RootRefl_mem hgenL 0 (rootPath m)
  have hψlin : ∀ m v, ggLin (p := 3) ι (ψ m) v =
      v - ar m v • ec.symm (rootVec m) := by
    intro m v
    apply ec.injective
    rw [map_sub, map_smul,
      e6RootRefl_act hact hinv 0 (rootPath m) (rootVec m) (rootVec_applyWord m) v]
    simp [ar, e6dotLin, ψ]
  have hselfu : ∀ m, ar m (ec.symm (rootVec m)) = 2 := by
    intro m
    simp [ar, e6dotLin, e6dot_Cmul_self, norm_rootVec m]
  have hpat : ∀ m, a' (rootVec m) = 0 ↔ e6RootPair (rootVec m) w = 0 := by
    intro m
    have hcross := e6_actual_cross_zero_iff hH ι hφa
      (Subgroup.mem_sup_left (hψmem m)) hlinA (hψlin m) hselfa (hselfu m)
    have haa : aa (ec.symm (rootVec m)) = a' (rootVec m) := rfl
    have har : ar m ha = e6RootPair (rootVec m) w := by
      change e6dot (Cmul (rootVec m)) (ec ha) = e6RootPair (rootVec m) (ec ha)
      rw [e6dot_Cmul_swap (rootVec m) (ec ha)]
      simp [e6RootPair, e6Eval, ← e6SixCanonical_Cmul_eq_e6CH, e6dot, mul_comm]
    rwa [haa, har] at hcross
  have hpatCoord : ∀ m,
      (∑ i, aCoord i * rootVec m i = 0) ↔ e6RootPair (rootVec m) w = 0 := by
    intro m
    rw [← ha'_apply (rootVec m)]
    exact hpat m
  have hpatSource : ∀ m : Fin 72,
      (∑ i, aCoord i * ((e6RootVec m i : ℤ) : ZMod 3) = 0) ↔
      e6RootPair (fun i => ((e6RootVec m i : ℤ) : ZMod 3)) w = 0 := by
    intro m
    have hroot : rootVec m = (fun i => ((e6RootVec m i : ℤ) : ZMod 3)) :=
      funext (rootVec_eq_source m)
    convert hpatCoord m using 1 <;> simp only [hroot, e6RootPair, e6Eval]
  obtain ⟨mu, hmu⟩ := e6_zero_pattern_proportional w aCoord hpatSource
  have hmu_apply : ∀ u, a' u = mu * e6dot (Cmul w) u := by
    intro u
    have hcoord : ∀ i, aCoord i = mu * Cmul w i := by
      intro i
      have h := congrArg (fun f : Fin 6 → ZMod 3 => f i) hmu
      simpa [Pi.smul_apply, smul_eq_mul, ← e6SixCanonical_Cmul_eq_e6CH] using h
    rw [ha'_apply u]
    calc
      ∑ i, aCoord i * u i = ∑ i, (mu * Cmul w i) * u i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoord i]
      _ = mu * ∑ i, Cmul w i * u i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = mu * e6dot (Cmul w) u := rfl
  have hself_mu : mu * norm w = 2 := by
    have h := hself'
    rw [hmu_apply w, e6dot_Cmul_self] at h
    exact h
  have hmu_ne : mu ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hself_mu
    exact (by decide : (2 : ZMod 3) ≠ 0) hself_mu.symm
  rcases norm_cases (norm w) with h0 | h1 | h2
  · exfalso
    rw [h0, mul_zero] at hself_mu
    exact (by decide : (0 : ZMod 3) ≠ 2) hself_mu
  · exfalso
    let G : MulAut ↥Bs := e6WordAut φL (translationWord w)
    have hGmem : G ∈ ggAutomizer L Bs := e6WordAut_mem hgenL _
    have hgh : ggLin (p := 3) ι G ha = ha + ec.symm r := by
      apply ec.injective
      calc
        ec (ggLin (p := 3) ι G ha)
            = applyWord (translationWord w) (ec ha) :=
                e6WordAut_act hact (translationWord w) ha
        _ = applyWord (translationWord w) w := by simp [w]
        _ = w + r := translationWord_spec w h1
        _ = ec ha + ec (ec.symm r) := by simp [w]
        _ = ec (ha + ec.symm r) := (map_add ec ha (ec.symm r)).symm
    have hCinv : Cmul (applyWord (translationWord w).reverse w) = Cmul w := by
      have h1' := applyWord_reverse_applyWord (translationWord w) w
      rw [translationWord_spec w h1] at h1'
      rw [applyWord_add, applyWord_fixes_r] at h1'
      have hinv : applyWord (translationWord w).reverse w = w - r :=
        eq_sub_of_add_eq h1'
      rw [hinv, Cmul_sub, Cmul_r, sub_zero]
    have hdual : ∀ v, aa (ggLin (p := 3) ι G v) = aa v := by
      intro v
      calc
        aa (ggLin (p := 3) ι G v) = a' (ec (ggLin (p := 3) ι G v)) := by simp [a']
        _ = a' (applyWord (translationWord w) (ec v)) := by
              rw [e6WordAut_act hact (translationWord w) v]
        _ = mu * e6dot (Cmul w) (applyWord (translationWord w) (ec v)) :=
              hmu_apply _
        _ = mu * e6dot (Cmul (applyWord (translationWord w).reverse w)) (ec v) := by
              rw [e6dot_Cmul_applyWord (translationWord w) w (ec v)]
        _ = mu * e6dot (Cmul w) (ec v) := by rw [hCinv]
        _ = a' (ec v) := (hmu_apply (ec v)).symm
        _ = aa v := by simp [a']
    exact e6_actual_added_norm1_false hH ι hφa hGmem hlinA hselfa hgh hdual
      (by
        intro hzero
        apply r_ne_zero
        have h := congrArg ec hzero
        simpa using h)
  · obtain ⟨m, t, hdecW⟩ := (norm_two_iff w).mp h2
    have hmu1 : mu = 1 := by
      rw [h2] at hself_mu
      rcases norm_cases mu with hm0 | hm1 | hm2
      · exfalso
        rw [hm0] at hself_mu
        exact (by decide : (0 : ZMod 3) * 2 ≠ 2) hself_mu
      · exact hm1
      · exfalso
        rw [hm2] at hself_mu
        exact (by decide : (2 : ZMod 3) * 2 ≠ 2) hself_mu
    have hCw : Cmul w = Cmul (rootVec m) := by
      rw [hdecW, Cmul_add, Cmul_smul, Cmul_r, smul_zero, add_zero]
    have haeq : aa = ar m := by
      apply LinearMap.ext
      intro v
      have h := hmu_apply (ec v)
      rw [hmu1] at h
      simpa [a', ar, e6dotLin, hCw] using h
    have hdec : ha = ec.symm (rootVec m) + t • ec.symm r := by
      calc
        ha = ec.symm (ec ha) := by rw [LinearEquiv.symm_apply_apply]
        _ = ec.symm w := rfl
        _ = ec.symm (rootVec m + t • r) := by rw [hdecW]
        _ = ec.symm (rootVec m) + t • ec.symm r := by rw [map_add, map_smul]
    have hrV : ec.symm r ≠ 0 := by
      intro hzero
      apply r_ne_zero
      have h := congrArg ec hzero
      simpa using h
    exact (e6_actual_added_norm2_mem hH ι hφa (hψmem m) hlinA (hψlin m)
      hselfa (hselfu m) haeq hdec hrV).2

theorem e6ChartSum (i : Fin 6) (v : Fin 6 → ZMod 3) :
    (∑ j, v j * (CartanMatrix.E 6 i j : ZMod 3)) = Cmul v i := by
  rw [show Cmul v i = ∑ j, (CartanMatrix.E 6 i j : ZMod 3) * v j by
    simp [Cmul, C, Cℤ_eq_mathlib]]
  apply Finset.sum_congr rfl
  intro j _
  ring

end CFSG.StandardType

end

public section

namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open scoped Matrix

theorem e6_radical_alignment_of_commonKernel_le_line
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (hLI : LinearIndependent (ZMod 3) h)
    (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (x : V) (hfix : ∀ w, (∀ i, α i w = 0) → ∃ lam : ZMod 3, w = lam • x) :
    ∃ lam : ZMod 3, x = lam • Fintype.linearCombination (ZMod 3) h r := by
  let wr := Fintype.linearCombination (ZMod 3) h cartanE6KernelVec
  have hkill : ∀ i, α i wr = 0 := by
    intro i
    change α i (Fintype.linearCombination (ZMod 3) h cartanE6KernelVec) = 0
    rw [apply_linearCombination_eq_cartanE6ModThree (h := h) (α := α) hpair]
    exact congr_fun cartanE6ModThree_mulVec_cartanE6KernelVec i
  have hwr : wr ≠ 0 := by
    intro hzero
    have hcoeff : cartanE6KernelVec = 0 :=
      hLI.fintypeLinearCombination_injective (by simpa [wr] using hzero)
    exact cartanE6KernelVec_ne_zero hcoeff
  obtain ⟨lam, hwrx⟩ := hfix wr hkill
  have hlam : lam ≠ 0 := by
    intro hzero
    exact hwr (by rw [hwrx, hzero, zero_smul])
  have hr : cartanE6KernelVec = r := by decide +kernel
  refine ⟨lam⁻¹, ?_⟩
  rw [← hr]
  change x = lam⁻¹ • wr
  rw [hwrx, smul_smul, inv_mul_cancel₀ hlam, one_smul]

end CFSG.StandardType.E6Seven

public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open scoped Matrix

theorem e6WordAut_act_linearCombination
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (w : List (Fin 6)) (u : Fin 6 → ZMod 3) :
    ggLin (p := 3) ι (e6WordAut φL w)
        (Fintype.linearCombination (ZMod 3) h u) =
      Fintype.linearCombination (ZMod 3) h (applyWord w u) := by
  let H : (Fin 6 → ZMod 3) → V := Fintype.linearCombination (ZMod 3) h
  have hC : C = cartanE6ModThree := by
    ext i j
    rw [C_eq_mathlib]
    simp [cartanE6ModThree]
  have hUnit : ∀ i : Fin 6, Fintype.linearCombination (ZMod 3) h (unitRoot i) = h i := by
    intro i
    rw [unitRoot, Fintype.linearCombination_apply_single, one_smul]
  have hH_s : ∀ i u, H (s i u) = H u - (cartanE6ModThree *ᵥ u) i • h i := by
    intro i u
    change Fintype.linearCombination (ZMod 3) h (s i u) =
      Fintype.linearCombination (ZMod 3) h u -
        (cartanE6ModThree *ᵥ u) i • h i
    rw [s, map_sub, map_smul, hUnit i, Cmul_eq_mulVec, hC]
  have hact : ∀ i u, ggLin (p := 3) ι (φL i) (H u) = H (s i u) := by
    intro i u
    rw [hlin i (H u), apply_linearCombination_eq_cartanE6ModThree (h := h) (α := α) hpair i u]
    rw [hH_s i u]
  have hmain : ∀ (w : List (Fin 6)) (u : Fin 6 → ZMod 3),
      ggLin (p := 3) ι (e6WordAut φL w) (H u) = H (applyWord w u) := by
    intro w
    induction w with
    | nil => intro u; simp
    | cons i is ih =>
        intro u
        rw [e6WordAut_cons, map_mul, LinearEquiv.mul_apply, hact i u, ih (s i u), applyWord_cons]
  exact hmain w u

theorem conjugate_reflection_apply
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V)
    (g : V ≃ₗ[ZMod 3] V) (hgB : ∀ u v, B (g u) (g v) = B u v)
    (h0 w : V) (hg0 : g h0 = w) (v : V) :
    g (g.symm v - B h0 (g.symm v) • h0) = v - B w v • w := by
  rw [map_sub, map_smul, hg0, LinearEquiv.apply_symm_apply]
  have h := hgB h0 (g.symm v)
  rw [hg0, LinearEquiv.apply_symm_apply] at h
  rw [h.symm]

theorem e6WordAut_isometry
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V)
    (φL : Fin 6 → MulAut ↥Bs) (ι : Additive ↥Bs ≃+ V)
    (hgenB : ∀ i, ∀ u v, B (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = B u v)
    (w : List (Fin 6)) (u v : V) :
    B (ggLin (p := 3) ι (e6WordAut φL w) u)
      (ggLin (p := 3) ι (e6WordAut φL w) v) = B u v := by
  induction w generalizing u v with
  | nil => simp
  | cons i is ih =>
      rw [e6WordAut_cons, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ih, hgenB i]

theorem e6RootRefl_apply_full
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φL : Fin 6 → MulAut ↥Bs}
    (B : LinearMap.BilinForm (ZMod 3) V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hB : ∀ i, B (h i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenB : ∀ i, ∀ u v, B (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = B u v)
    (hinv : ∀ i, φL i * φL i = 1)
    (i0 : Fin 6) (w : List (Fin 6)) (beta : Fin 6 → ZMod 3)
    (hbeta : applyWord w (unitRoot i0) = beta) (v : V) :
    ggLin (p := 3) ι (e6RootRefl φL i0 w) v =
      v - B (Fintype.linearCombination (ZMod 3) h beta) v •
        Fintype.linearCombination (ZMod 3) h beta := by
  let H : (Fin 6 → ZMod 3) → V := Fintype.linearCombination (ZMod 3) h
  let g : V ≃ₗ[ZMod 3] V := ggLin (p := 3) ι (e6WordAut φL w)
  have hgB : ∀ u v, B (g u) (g v) = B u v :=
    e6WordAut_isometry B φL ι hgenB w
  have hUnit : ∀ i : Fin 6, Fintype.linearCombination (ZMod 3) h (unitRoot i) = h i := by
    intro i
    rw [unitRoot, Fintype.linearCombination_apply_single, one_smul]
  have hg0 : g (h i0) = H beta := by
    change ggLin (p := 3) ι (e6WordAut φL w) (h i0) = H beta
    rw [← hUnit i0]
    rw [e6WordAut_act_linearCombination (h := h) (α := α)
      (hpair := hpair) (hlin := hlin) (φL := φL) (w := w) (u := unitRoot i0), hbeta]
  have hphi0 : ∀ v, ggLin (p := 3) ι (φL i0) v = v - B (h i0) v • h i0 := by
    intro v
    rw [hlin i0 v, hB i0]
  have hconj : ∀ v, ggLin (p := 3) ι (e6RootRefl φL i0 w) v =
      g (g.symm v - B (h i0) (g.symm v) • h i0) := by
    intro v
    rw [e6RootRefl]
    simp only [g, map_mul, map_inv, LinearEquiv.mul_apply]
    have harg : (ggLin (p := 3) ι (e6WordAut φL w))⁻¹ v =
        (ggLin (p := 3) ι (e6WordAut φL w)).symm v := rfl
    rw [harg]
    rw [hphi0]
  rw [hconj v]
  have hg0' : g (h i0) = Fintype.linearCombination (ZMod 3) h beta := by
    simpa [H] using hg0
  exact conjugate_reflection_apply B g hgB (h i0)
    (Fintype.linearCombination (ZMod 3) h beta) hg0' v

end E6Seven
end CFSG.StandardType

public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open scoped Matrix

theorem e6_fullRootAction_sameWitness
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (φL : Fin 6 → MulAut ↥Bs)
    (hpair : ∀ i j, α i (h j) = cartanE6ModThree i j)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h i)
    (hgenL : ∀ i, φL i ∈ ggAutomizer L Bs)
    (hinv : ∀ i, φL i * φL i = 1)
    (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (c : Fin 6 → ZMod 3)
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (hchart_h : ∀ i, chart (h i) = Pi.single i.castSucc 1)
    (hform_h : ∀ i, Bform (h i) = α i)
    (hBform : Bform = (B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap)
    (hsymm : (gram7 cartanE6ModThree c 0).IsSymm)
    (hdiag : ∀ i : Fin 6, gram7 cartanE6ModThree c 0 i.castSucc i.castSucc = 2) :
    (∀ m, e6RootRefl φL 0 (rootPath m) ∈ ggAutomizer L Bs) ∧
    (∀ m v, ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m)) v =
      v - Bform (Fintype.linearCombination (ZMod 3) h (rootVec m)) v •
        Fintype.linearCombination (ZMod 3) h (rootVec m)) ∧
    (∀ m, Bform (Fintype.linearCombination (ZMod 3) h (rootVec m))
      (Fintype.linearCombination (ZMod 3) h (rootVec m)) = 2) := by
  have hgenB : ∀ i, ∀ u v,
      Bform (ggLin (p := 3) ι (φL i) u) (ggLin (p := 3) ι (φL i) v) = Bform u v := by
    intro i u v
    rw [hBform]
    exact chart_generator_invariant h α φL ι hlin chart c 0 hchart_h
      (by intro j; rw [← hBform]; exact hform_h j) hsymm hdiag i u v
  let H : (Fin 6 → ZMod 3) → V := Fintype.linearCombination (ZMod 3) h
  have hRootAction : ∀ m v, ggLin (p := 3) ι (e6RootRefl φL 0 (rootPath m)) v =
      v - Bform (H (rootVec m)) v • H (rootVec m) := by
    intro m v
    exact e6RootRefl_apply_full Bform h α hpair hform_h hlin hgenB hinv 0
      (rootPath m) (rootVec m) (rootVec_applyWord m) v
  have hRootMem : ∀ m, e6RootRefl φL 0 (rootPath m) ∈ ggAutomizer L Bs := by
    intro m
    exact e6RootRefl_mem hgenL 0 (rootPath m)
  have hUnit : ∀ i : Fin 6, H (unitRoot i) = h i := by
    intro i
    change Fintype.linearCombination (ZMod 3) h (unitRoot i) = h i
    rw [unitRoot, Fintype.linearCombination_apply_single, one_smul]
  have hRootSelf : ∀ m, Bform (H (rootVec m)) (H (rootVec m)) = 2 := by
    intro m
    have hg0 : ggLin (p := 3) ι (e6WordAut φL (rootPath m)) (h 0) = H (rootVec m) := by
      change ggLin (p := 3) ι (e6WordAut φL (rootPath m)) (h 0) = H (rootVec m)
      rw [← hUnit 0]
      rw [e6WordAut_act_linearCombination (h := h) (α := α)
        (hpair := hpair) (hlin := hlin) (φL := φL) (w := rootPath m)
        (u := unitRoot 0), rootVec_applyWord m]
    rw [← hg0]
    rw [e6WordAut_isometry Bform φL ι hgenB]
    rw [hform_h 0, hpair 0 0]
    decide +kernel
  exact ⟨hRootMem, hRootAction, hRootSelf⟩

end E6Seven
end CFSG.StandardType

public section

namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_raw_chart_root_actions
    {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (hV : Λ ⊕ Λa → V)
    (αV : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - αV o w • hV o)
    (hsel : LinearIndependent (ZMod 3) (fun i : Λ => hV (Sum.inl i)))
    (hpair : ∀ i j : Λ,
      αV (Sum.inl i) (hV (Sum.inl j)) = (CL i j : ZMod 3))
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hclosL : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (e : Fin 6 ≃ Λ)
    (hML' : ML = CoxeterMatrix.E₆.reindex e)
    (hcard : Nat.card Bs = 3 ^ 7) :
    ∃ (z : V) (c : Fin 6 → ZMod 3) (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
      (Bform : LinearMap.BilinForm (ZMod 3) V),
      (∀ i : Fin 6, chart (hV (Sum.inl (e i))) = Pi.single i.castSucc 1) ∧
      chart z = Pi.single (Fin.last 6) 1 ∧
      (∀ i : Fin 6, Bform (hV (Sum.inl (e i))) = αV (Sum.inl (e i))) ∧
      (∀ i j : Fin 6,
        Bform (hV (Sum.inl (e i))) (hV (Sum.inl (e j))) = cartanE6ModThree i j) ∧
      (∀ i : Fin 6, Bform (hV (Sum.inl (e i))) z = αV (Sum.inl (e i)) z) ∧
      Bform z z = 0 ∧
      Bform = (B7 cartanE6ModThree c 0).comp chart.toLinearMap chart.toLinearMap ∧
      (∀ m, e6RootRefl (fun i : Fin 6 => φ (Sum.inl (e i))) 0 (rootPath m)
        ∈ ggAutomizer L Bs) ∧
      (∀ m v, ggLin (p := 3) ι
        (e6RootRefl (fun i : Fin 6 => φ (Sum.inl (e i))) 0 (rootPath m)) v =
        v - Bform (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) v •
          Fintype.linearCombination (ZMod 3)
            (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) ∧
      (∀ m, Bform (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m))
        (Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) (rootVec m)) = 2) := by
  classical
  let h' : Fin 6 → V := fun i => hV (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => αV (Sum.inl (e i))
  let φL : Fin 6 → MulAut ↥Bs := fun i => φ (Sum.inl (e i))
  have hLI : LinearIndependent (ZMod 3) h' := hsel.comp e e.injective
  have hpair' : ∀ i j, α' i (h' j) = cartanE6ModThree i j := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML']
    simp [cartanE6ModThree]
  have hVcard : Nat.card V = 3 ^ 7 := by
    rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Additive.toMul, hcard]
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hVpow : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V))
  have hdim : Module.finrank (ZMod 3) V = 7 := by
    have hpow : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 7 := hVpow.symm.trans hVcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  obtain ⟨z, c, chart, Bform, hchart_h, hchart_z, hform_h, hform_hh, hform_hz, hform_zz,
    hBform⟩ := exists_seven_chart_form h' α' hLI hdim hpair' 0
  have hsymm : (gram7 cartanE6ModThree c 0).IsSymm := by
    apply gram7_symm
    apply Matrix.IsSymm.ext
    intro i j
    exact (cartanE6ModThree_symm i j).symm
  have hdiag : ∀ i : Fin 6, gram7 cartanE6ModThree c 0 i.castSucc i.castSucc = 2 := by
    intro i
    rw [gram7_castSucc_castSucc]
    fin_cases i <;> rfl
  have hclosL' : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    rw [hclosL]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [φL]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
  have hgenL : ∀ i, φL i ∈ ggAutomizer L Bs := by
    intro i
    rw [hclosL']
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hinv : ∀ i, φL i * φL i = 1 := by
    intro i
    have := (hrefl (Sum.inl (e i))).1
    simpa [φL, pow_two] using this
  have hlinL : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α' i v • h' i := by
    intro i v
    exact hlin (Sum.inl (e i)) v
  exact ⟨z, c, chart, Bform, hchart_h, hchart_z, hform_h, hform_hh, hform_hz, hform_zz,
    hBform, e6_fullRootAction_sameWitness h' α' φL hpair' hlinL hgenL hinv chart c Bform
      hchart_h hform_h hBform hsymm hdiag⟩

end CFSG.StandardType.E6Seven

end

public section

namespace CFSG.StandardType.E6Seven

open CFSG.Assembly Module E6QTwo E6NormWordOrbit
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6_raw_radical_alignment
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hFix : GGTBFixInput)
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hcard : Nat.card Bs = 3 ^ 7)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (hV : Λ ⊕ Λa → V)
    (αV : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - αV o w • hV o)
    (hsel : LinearIndependent (ZMod 3) (fun i : Λ => hV (Sum.inl i)))
    (hpair : ∀ i j : Λ,
      αV (Sum.inl i) (hV (Sum.inl j)) = (CL i j : ZMod 3))
    (hclosL : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (e : Fin 6 ≃ Λ)
    (hML' : ML = CoxeterMatrix.E₆.reindex e)
    (hΛa1 : 1 ≤ Nat.card Λa) :
    ∃ lam : ZMod 3,
      ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) =
        lam • Fintype.linearCombination (ZMod 3)
          (fun i : Fin 6 => hV (Sum.inl (e i))) cartanE6KernelVec := by
  classical
  let h' : Fin 6 → V := fun i => hV (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => αV (Sum.inl (e i))
  have hLI : LinearIndependent (ZMod 3) h' := hsel.comp e e.injective
  have hpair' : ∀ i j, α' i (h' j) = cartanE6ModThree i j := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML']
    simp [cartanE6ModThree]
  have hpos : 0 < Fintype.card Λa := by
    rw [← Nat.card_eq_fintype_card]
    omega
  let a0 : Λa := Classical.choice (Fintype.card_pos_iff.mp hpos)
  let φO : Option Λ → MulAut ↥Bs := fun o => match o with
    | some i => φ (Sum.inl i)
    | none => φ (Sum.inr a0)
  let hO : Option Λ → V := fun o => match o with
    | some i => hV (Sum.inl i)
    | none => hV (Sum.inr a0)
  let αO : Option Λ → Module.Dual (ZMod 3) V := fun o => match o with
    | some i => αV (Sum.inl i)
    | none => αV (Sum.inr a0)
  have hlinO : ∀ o w, ggLin (p := 3) ι (φO o) w = w - αO o w • hO o := by
    rintro (_ | i) w
    · exact hlin (Sum.inr a0) w
    · exact hlin (Sum.inl i) w
  have hclosO : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun i : Λ => φO (some i)) := by
    simpa [φO] using hclosL
  have hfix : ∀ w : V, (∀ i : Fin 6, α' i w = 0) →
      ∃ lam : ZMod 3, w = lam • ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) := by
    intro w hw
    have hwO : ∀ i : Λ, αO (some i) w = 0 := by
      intro i
      have := hw (e.symm i)
      simpa [αO, α'] using this
    have hspan := ggResI_fixSpan (p := 3) (Λ := Λ) (V := V) (φ := φO) (h := hO)
      (α := αO) hFix hH hH.1.tableB_facts.2.2.1 ι hlinO hclosO w hwO
    rw [Submodule.mem_span_singleton] at hspan
    obtain ⟨lam, hlam⟩ := hspan
    exact ⟨lam, hlam.symm⟩
  exact e6_radical_alignment_of_commonKernel_le_line h' hLI α' hpair'
    (ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩)) hfix

end CFSG.StandardType.E6Seven

end

public section
public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E6NormWordOrbit
open CFSG.StandardType.E6QTwo
open scoped Matrix

theorem e6_restriction_proportional_sameWitness
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (rootRefl : Fin 72 → MulAut ↥Bs)
    (hRootMem : ∀ m, rootRefl m ∈ ggAutomizer L Bs)
    (hRootAction : ∀ m v, ggLin (p := 3) ι (rootRefl m) v =
      v - Bform (Fintype.linearCombination (ZMod 3) h (rootVec m)) v •
        Fintype.linearCombination (ZMod 3) h (rootVec m))
    (hRootSelf : ∀ m, Bform (Fintype.linearCombination (ZMod 3) h (rootVec m))
      (Fintype.linearCombination (ZMod 3) h (rootVec m)) = 2)
    (F : MulAut ↥Bs) (w : V) (aa : Module.Dual (ZMod 3) V)
    (hF : F ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (hFlin : ∀ v, ggLin (p := 3) ι F v = v - aa v • w)
    (hself : aa w = 2) :
    ∃ μ : ZMod 3, ∀ u : Fin 6 → ZMod 3,
      aa (Fintype.linearCombination (ZMod 3) h u) =
        μ * Bform (Fintype.linearCombination (ZMod 3) h u) w := by
  let H : (Fin 6 → ZMod 3) → V := Fintype.linearCombination (ZMod 3) h
  let aCoord : Fin 6 → ZMod 3 := fun i => aa (h i)
  let beta : Fin 6 → ZMod 3 := fun i => Bform (h i) w
  have hHlin : ∀ u : Fin 6 → ZMod 3, aa (H u) = e6Eval aCoord u := by
    intro u
    change aa (Fintype.linearCombination (ZMod 3) h u) = e6Eval aCoord u
    rw [Fintype.linearCombination_apply, map_sum, e6Eval]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul]
    exact mul_comm _ _
  have hBlin : ∀ u : Fin 6 → ZMod 3, Bform (H u) w = e6Eval beta u := by
    intro u
    change Bform (Fintype.linearCombination (ZMod 3) h u) w = e6Eval beta u
    rw [Fintype.linearCombination_apply, map_sum, e6Eval]
    rw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  have hcross : ∀ m : Fin 72, aa (H (rootVec m)) = 0 ↔ Bform (H (rootVec m)) w = 0 := by
    intro m
    exact e6_actual_cross_zero_iff hH ι hF
      ((show ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs from le_sup_left) (hRootMem m))
      hFlin (hRootAction m) hself (hRootSelf m)
  have hpat : ∀ m : Fin 72,
      e6Eval aCoord (rootVec m) = 0 ↔ e6Eval beta (rootVec m) = 0 := by
    intro m
    rw [← hHlin (rootVec m), ← hBlin (rootVec m)]
    exact hcross m
  have hsel : ∀ k : Fin 16, e6SelVec k = rootVec (e6SelIdx k) := by
    intro k
    funext i
    rw [e6SelVec_eq_root]
    exact (rootVec_eq_source (e6SelIdx k) i).symm
  have hpat16 : ∀ k : Fin 16,
      e6Eval aCoord (e6SelVec k) = 0 ↔ e6Eval beta (e6SelVec k) = 0 := by
    intro k
    rw [hsel k]
    exact hpat (e6SelIdx k)
  obtain ⟨μ, hμ⟩ := e6SelVec_separates aCoord beta hpat16
  refine ⟨μ, fun u => ?_⟩
  rw [hHlin u, hμ, hBlin u]
  rw [e6Eval, e6Eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end E6Seven
end CFSG.StandardType

public section

namespace CFSG.StandardType.E6Seven

open CFSG.StandardType.E6QTwo
open CFSG.StandardType.E7F3
open _root_.E6Seven
open scoped Matrix
open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def canonicalCoupling : Fin 6 → ZMod 3 := ![2, 0, 0, 0, 0, 0]

theorem canonicalCoupling_dot_kernelVec :
    canonicalCoupling ⬝ᵥ cartanE6KernelVec = 2 := by
  decide +kernel

theorem gram7_canonical_eq_C7 :
    gram7 cartanE6ModThree canonicalCoupling 2 = C7 := by
  decide +kernel

theorem emb6_cartanE6KernelVec : emb6 cartanE6KernelVec = rvec := by
  decide +kernel

theorem pair_eq_B7 (u v : Fin 7 → ZMod 3) :
    pair u v = B7 cartanE6ModThree canonicalCoupling 2 u v := by
  rw [B7, Matrix.toBilin'_apply', gram7_canonical_eq_C7]
  rfl

theorem pair_eq_B7Block (u v : Fin 7 → ZMod 3) :
    pair u v = B7Block cartanE6ModThree canonicalCoupling 2
      (fun i => u (finSumFinEquiv i)) (fun i => v (finSumFinEquiv i)) := by
  rw [pair_eq_B7, B7_eq_B7Block]

private def acol (a : Fin 6 → ZMod 3) : Matrix (Fin 6) (Fin 1) (ZMod 3) :=
  Matrix.of fun i _ => a i

private def arow (a : Fin 6 → ZMod 3) : Matrix (Fin 1) (Fin 6) (ZMod 3) :=
  Matrix.of fun _ j => a j

private def ccol (c : Fin 6 → ZMod 3) : Matrix (Fin 6) (Fin 1) (ZMod 3) :=
  Matrix.of fun i _ => c i

private def crow (c : Fin 6 → ZMod 3) : Matrix (Fin 1) (Fin 6) (ZMod 3) :=
  Matrix.of fun _ j => c j

private def scM (x : ZMod 3) : Matrix (Fin 1) (Fin 1) (ZMod 3) :=
  Matrix.of fun _ _ => x

private def bcol (a : Fin 6 → ZMod 3) (lam : ZMod 3) : Matrix (Fin 6) (Fin 1) (ZMod 3) :=
  Matrix.of fun i _ => -(a i * lam⁻¹)

private lemma scM_add (x y : ZMod 3) : scM x + scM y = scM (x + y) := by
  ext i j
  fin_cases i; fin_cases j
  simp [scM]

private lemma scM_mul (x y : ZMod 3) : scM x * scM y = scM (x * y) := by
  ext i j
  fin_cases i; fin_cases j
  simp [scM, Matrix.mul_apply]

private lemma rowM_mul_colM (c a : Fin 6 → ZMod 3) :
    crow c * acol a = scM (c ⬝ᵥ a) := by
  ext i j
  fin_cases i; fin_cases j
  simp [crow, acol, scM, Matrix.mul_apply, dotProduct]

private def blockM (a : Fin 6 → ZMod 3) (lam : ZMod 3) :
    Matrix (Fin 6 ⊕ Fin 1) (Fin 6 ⊕ Fin 1) (ZMod 3) :=
  Matrix.fromBlocks 1 (acol a) 0 (scM lam)

private def blockMinv (a : Fin 6 → ZMod 3) (lam : ZMod 3) :
    Matrix (Fin 6 ⊕ Fin 1) (Fin 6 ⊕ Fin 1) (ZMod 3) :=
  Matrix.fromBlocks 1 (bcol a lam) 0 (scM lam⁻¹)

private lemma blockM_mul_blockMinv (a : Fin 6 → ZMod 3) {lam : ZMod 3} (hlam : lam ≠ 0) :
    blockM a lam * blockMinv a lam = 1 := by
  rw [blockM, blockMinv, Matrix.fromBlocks_multiply]
  simp only [add_zero, zero_add, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]
  rw [show bcol a lam + acol a * scM lam⁻¹ = 0 from by
    have ha : acol a * scM lam⁻¹ = - bcol a lam := by
      ext i j
      fin_cases j
      simp only [Matrix.mul_apply, Fin.sum_univ_one, acol, bcol, scM, Matrix.of_apply,
        Matrix.neg_apply]
      ring
    rw [ha, add_neg_cancel]]
  rw [show scM lam * scM lam⁻¹ = 1 from by
    rw [scM_mul, mul_inv_cancel₀ hlam, show scM (1 : ZMod 3) = 1 from by
      ext i j; fin_cases i; fin_cases j; simp [scM]]]
  rw [Matrix.fromBlocks_one]

private lemma blockMinv_mul_blockM (a : Fin 6 → ZMod 3) {lam : ZMod 3} (hlam : lam ≠ 0) :
    blockMinv a lam * blockM a lam = 1 := by
  rw [blockM, blockMinv, Matrix.fromBlocks_multiply]
  simp only [add_zero, zero_add, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]
  rw [show acol a + bcol a lam * scM lam = 0 from by
    have hb : bcol a lam * scM lam = - acol a := by
      ext i j
      fin_cases j
      simp only [Matrix.mul_apply, Fin.sum_univ_one, bcol, acol, scM, Matrix.of_apply,
        Matrix.neg_apply]
      rw [neg_mul, mul_assoc, inv_mul_cancel₀ hlam, mul_one]
    rw [hb, add_neg_cancel]]
  rw [show scM lam⁻¹ * scM lam = 1 from by
    rw [scM_mul, inv_mul_cancel₀ hlam, show scM (1 : ZMod 3) = 1 from by
      ext i j; fin_cases i; fin_cases j; simp [scM]]]
  rw [Matrix.fromBlocks_one]

theorem toBilin_block_congruence
    (c : Fin 6 → ZMod 3) (d : ZMod 3) (a : Fin 6 → ZMod 3) (lam : ZMod 3)
    (hlam : lam ≠ 0)
    (hCa : cartanE6ModThree *ᵥ a = canonicalCoupling - lam • c)
    (hD : a ⬝ᵥ (cartanE6ModThree *ᵥ a) + 2 * lam * (c ⬝ᵥ a) + lam ^ 2 * d = 2) :
    ∃ T : ((Fin 6 ⊕ Fin 1) → ZMod 3) ≃ₗ[ZMod 3] ((Fin 6 ⊕ Fin 1) → ZMod 3),
      (∀ i : Fin 6, T (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1) ∧
      T (Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3)) =
        Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3) ∧
      (∀ x y, B7Block cartanE6ModThree c d (T x) (T y) =
        B7Block cartanE6ModThree canonicalCoupling 2 x y) := by
  have hG : gram7Block cartanE6ModThree c d =
      Matrix.fromBlocks cartanE6ModThree (ccol c) (crow c) (scM d) := rfl
  have hGn : gram7Block cartanE6ModThree canonicalCoupling 2 =
      Matrix.fromBlocks cartanE6ModThree (ccol canonicalCoupling) (crow canonicalCoupling)
        (scM 2) := rfl
  have h1 : cartanE6ModThree * acol a + ccol c * scM lam = ccol canonicalCoupling := by
    ext i j
    fin_cases j
    have h := congr_fun hCa i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one,
      acol, ccol, scM]
    rw [h]
    ring
  have h2 : arow a * cartanE6ModThree + scM lam * crow c = crow canonicalCoupling := by
    ext i j
    fin_cases i
    have h := congr_fun hCa j
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one,
      arow, crow, scM]
    have hsym : (∑ x : Fin 6, a x * cartanE6ModThree x j) =
        ∑ x : Fin 6, cartanE6ModThree j x * a x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [cartanE6ModThree_symm x j, mul_comm]
    rw [hsym, h]
    ring
  have h3 : (arow a * cartanE6ModThree + scM lam * crow c) * acol a +
      (arow a * ccol c + scM lam * scM d) * scM lam = scM 2 := by
    rw [h2, Matrix.add_mul]
    rw [show crow canonicalCoupling * acol a = scM (canonicalCoupling ⬝ᵥ a) from
      rowM_mul_colM _ _]
    rw [show arow a * ccol c = scM (a ⬝ᵥ c) from rowM_mul_colM _ _]
    rw [show scM (a ⬝ᵥ c) * scM lam = scM (a ⬝ᵥ c * lam) from scM_mul _ _]
    rw [show scM lam * scM d = scM (lam * d) from scM_mul _ _]
    rw [show scM (lam * d) * scM lam = scM (lam * d * lam) from scM_mul _ _]
    have hDa : a ⬝ᵥ (cartanE6ModThree *ᵥ a) =
        canonicalCoupling ⬝ᵥ a - lam * (c ⬝ᵥ a) := by
      rw [hCa, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm a canonicalCoupling,
        dotProduct_comm a c]
    have hDa' : canonicalCoupling ⬝ᵥ a =
        a ⬝ᵥ (cartanE6ModThree *ᵥ a) + lam * (c ⬝ᵥ a) := by
      rw [hDa]; ring
    have hscalar : canonicalCoupling ⬝ᵥ a + (a ⬝ᵥ c * lam + lam * d * lam) = 2 := by
      rw [hDa']
      rw [show a ⬝ᵥ c = c ⬝ᵥ a from dotProduct_comm a c]
      linear_combination hD
    rw [show scM (canonicalCoupling ⬝ᵥ a) + (scM (a ⬝ᵥ c * lam) + scM (lam * d * lam)) =
        scM (canonicalCoupling ⬝ᵥ a + (a ⬝ᵥ c * lam + lam * d * lam)) from by
      rw [scM_add, scM_add], hscalar]
  have hMt : (blockM a lam)ᵀ = Matrix.fromBlocks 1 0 (arow a) (scM lam) := by
    rw [blockM, Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_one, Matrix.transpose_zero]
    rfl
  have hMG : Matrix.fromBlocks 1 0 (arow a) (scM lam) *
      gram7Block cartanE6ModThree c d =
      Matrix.fromBlocks cartanE6ModThree (ccol c)
        (arow a * cartanE6ModThree + scM lam * crow c)
        (arow a * ccol c + scM lam * scM d) := by
    rw [hG, Matrix.fromBlocks_multiply]
    simp only [add_zero, zero_add, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero]
  have hcong : (blockM a lam)ᵀ * gram7Block cartanE6ModThree c d * blockM a lam =
      gram7Block cartanE6ModThree canonicalCoupling 2 := by
    rw [hMt, hMG, blockM, Matrix.fromBlocks_multiply]
    simp only [add_zero, zero_add, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul]
    rw [h1, h3, h2, hGn]
  let TE : ((Fin 6 ⊕ Fin 1) → ZMod 3) ≃ₗ[ZMod 3] ((Fin 6 ⊕ Fin 1) → ZMod 3) :=
    Matrix.toLin'OfInv (M := blockMinv a lam) (M' := blockM a lam)
      (blockMinv_mul_blockM a hlam) (blockM_mul_blockMinv a hlam)
  have hTE : ∀ z : (Fin 6 ⊕ Fin 1) → ZMod 3, TE z = blockM a lam *ᵥ z := by
    intro z
    ext w
    rw [Matrix.toLin'OfInv_apply, Matrix.toLin'_apply]
  refine ⟨TE, ?_, ?_, ?_⟩
  · intro i
    have hcol : (blockM a lam).col (Sum.inl i) = Pi.single (Sum.inl i) (1 : ZMod 3) := by
      ext σ
      rcases σ with j | j
      · simp [blockM, Matrix.col_apply, Matrix.fromBlocks_apply₁₁, Matrix.one_apply,
          Pi.single_apply]
      · simp [blockM, Matrix.col_apply, Matrix.fromBlocks_apply₂₁, Pi.single_apply]
    rw [hTE, Matrix.mulVec_single_one, hcol]
  · have hrv : blockM a lam *ᵥ Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3) =
        Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3) := by
      have hci : (Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3)) ∘ Sum.inl = cartanE6KernelVec := rfl
      have hcr : (Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3)) ∘ Sum.inr = (0 : Fin 1 → ZMod 3) := rfl
      rw [blockM, Matrix.fromBlocks_mulVec, hci, hcr]
      simp only [Matrix.mulVec_zero, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
    rw [hTE, hrv]
  · intro x y
    rw [hTE, hTE]
    have hcomp := Matrix.toBilin'_comp (M := gram7Block cartanE6ModThree c d)
      (P := blockM a lam) (Q := blockM a lam)
    rw [hcong] at hcomp
    have hxy := congrArg (fun B : LinearMap.BilinForm (ZMod 3) ((Fin 6 ⊕ Fin 1) → ZMod 3) =>
      B x y) hcomp
    simpa only [B7Block, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using hxy

theorem exists_block_normalizer (c : Fin 6 → ZMod 3) (d : ZMod 3)
    (hc : c ⬝ᵥ cartanE6KernelVec ≠ 0) :
    ∃ T : ((Fin 6 ⊕ Fin 1) → ZMod 3) ≃ₗ[ZMod 3] ((Fin 6 ⊕ Fin 1) → ZMod 3),
      (∀ i : Fin 6, T (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1) ∧
      T (Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3)) =
        Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3) ∧
      (∀ x y, B7Block cartanE6ModThree c d (T x) (T y) =
        B7Block cartanE6ModThree canonicalCoupling 2 x y) := by
  let lam : ZMod 3 := 2 * (c ⬝ᵥ cartanE6KernelVec)⁻¹
  have hls : lam * (c ⬝ᵥ cartanE6KernelVec) = 2 := by
    change (2 * (c ⬝ᵥ cartanE6KernelVec)⁻¹) * (c ⬝ᵥ cartanE6KernelVec) = 2
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hlam : lam ≠ 0 := by
    intro h0
    have h := hls
    rw [h0, zero_mul] at h
    exact (by decide +kernel : (2 : ZMod 3) ≠ 0) h.symm
  let c' : Fin 6 → ZMod 3 := canonicalCoupling - lam • c
  have hc' : c' ⬝ᵥ cartanE6KernelVec = 0 := by
    change (canonicalCoupling - lam • c) ⬝ᵥ cartanE6KernelVec = 0
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, canonicalCoupling_dot_kernelVec, hls,
      sub_self]
  have hC : E6NormWordOrbit.C = cartanE6ModThree := by
    rw [E6NormWordOrbit.C_eq_mathlib]
    rfl
  have hr : E6NormWordOrbit.r = cartanE6KernelVec := rfl
  obtain ⟨u₀, hu₀⟩ := E6NormWordOrbit.exists_mulVec_eq_of_dot_radical_eq_zero c'
    (by simpa only [hr] using hc')
  rw [hC] at hu₀
  let u : Fin 6 → ZMod 3 := -u₀
  have hu : cartanE6ModThree *ᵥ u = c' := by
    change cartanE6ModThree *ᵥ (-u₀) = c'
    calc
      cartanE6ModThree *ᵥ (-u₀) = -(cartanE6ModThree *ᵥ u₀) :=
        Matrix.mulVec_neg _ cartanE6ModThree
      _ = -(-c') := congrArg Neg.neg hu₀
      _ = c' := by
        ext i
        exact neg_neg (c' i)
  let d' : ZMod 3 := u ⬝ᵥ c' + 2 * lam * (c ⬝ᵥ u) + lam ^ 2 * d
  let t : ZMod 3 := 2 - d'
  let a : Fin 6 → ZMod 3 := u + t • cartanE6KernelVec
  have hCa : cartanE6ModThree *ᵥ a = canonicalCoupling - lam • c := by
    change cartanE6ModThree *ᵥ (u + t • cartanE6KernelVec) = c'
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hu,
      cartanE6ModThree_mulVec_cartanE6KernelVec, smul_zero, add_zero]
  have hD : a ⬝ᵥ (cartanE6ModThree *ᵥ a) + 2 * lam * (c ⬝ᵥ a) + lam ^ 2 * d = 2 := by
    have hcr : cartanE6KernelVec ⬝ᵥ c' = 0 := by
      rw [dotProduct_comm]; exact hc'
    have h1 : a ⬝ᵥ (cartanE6ModThree *ᵥ a) = u ⬝ᵥ c' := by
      rw [hCa]
      change (u + t • cartanE6KernelVec) ⬝ᵥ c' = u ⬝ᵥ c'
      rw [add_dotProduct, smul_dotProduct, smul_eq_mul, hcr, mul_zero, add_zero]
    have h2 : c ⬝ᵥ a = c ⬝ᵥ u + t * (c ⬝ᵥ cartanE6KernelVec) := by
      change c ⬝ᵥ (u + t • cartanE6KernelVec) =
        c ⬝ᵥ u + t * (c ⬝ᵥ cartanE6KernelVec)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [h1, h2]
    have hkey : ∀ Y : ZMod 3, 2 * lam * (Y * (c ⬝ᵥ cartanE6KernelVec)) = Y := by
      intro Y
      have h22 : (2 : ZMod 3) * 2 = 1 := by decide +kernel
      calc 2 * lam * (Y * (c ⬝ᵥ cartanE6KernelVec))
          = 2 * Y * (lam * (c ⬝ᵥ cartanE6KernelVec)) := by ring
        _ = 2 * Y * 2 := by rw [hls]
        _ = (2 * 2) * Y := by ring
        _ = Y := by rw [h22, one_mul]
    have hexp : 2 * lam * (c ⬝ᵥ u + t * (c ⬝ᵥ cartanE6KernelVec)) =
        2 * lam * (c ⬝ᵥ u) + t := by
      rw [mul_add, hkey t]
    rw [hexp]
    change u ⬝ᵥ c' + (2 * lam * (c ⬝ᵥ u) +
      (2 - (u ⬝ᵥ c' + 2 * lam * (c ⬝ᵥ u) + lam ^ 2 * d))) + lam ^ 2 * d = 2
    ring
  exact toBilin_block_congruence c d a lam hlam hCa hD

theorem exists_seven_gram_normalize (c : Fin 6 → ZMod 3) (d : ZMod 3)
    (hc : c ⬝ᵥ cartanE6KernelVec ≠ 0) :
    ∃ T : (Fin 7 → ZMod 3) ≃ₗ[ZMod 3] (Fin 7 → ZMod 3),
      (∀ i : Fin 6, T (Pi.single (Fin.castSucc i) 1) = Pi.single (Fin.castSucc i) 1) ∧
      T rvec = rvec ∧
      (∀ u v, B7 cartanE6ModThree c d (T u) (T v) = pair u v) := by
  obtain ⟨TW, hfix6, hfixr, hcong⟩ := exists_block_normalizer c d hc
  let e : Fin 6 ⊕ Fin 1 ≃ Fin 7 := finSumFinEquiv
  let T : (Fin 7 → ZMod 3) ≃ₗ[ZMod 3] (Fin 7 → ZMod 3) :=
    (LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) e).trans
      (TW.trans (LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) e).symm)
  have hTapply : ∀ (x : Fin 7 → ZMod 3) (j : Fin 7),
      T x j = TW (fun k => x (e k)) (e.symm j) := by
    intro x j
    simp only [T, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
      LinearMap.funLeft_apply]
    rfl
  have hTcomp : ∀ x : Fin 7 → ZMod 3,
      (fun k => T x (e k)) = TW (fun k => x (e k)) := by
    intro x
    funext k
    rw [hTapply]
    simp
  have hsingle : ∀ i : Fin 6,
      (fun k : Fin 6 ⊕ Fin 1 =>
        (Pi.single (Fin.castSucc i) (1 : ZMod 3) : Fin 7 → ZMod 3) (e k)) =
      Pi.single (Sum.inl i) 1 := by
    intro i
    funext k
    rcases k with k | k
    · rw [show e (Sum.inl k) = Fin.castSucc k from finSumFinEquiv_apply_left k]
      simp only [Pi.single_apply, Fin.castSucc_inj, Sum.inl.injEq]
    · have hk : k = 0 := Fin.eq_zero k
      subst hk
      rw [show e (Sum.inr (0 : Fin 1)) = Fin.last 6 from by
        have h := finSumFinEquiv_apply_right (m := 6) (n := 1) (0 : Fin 1)
        simpa using h]
      rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne',
        Pi.single_eq_of_ne (by simp : (Sum.inr (0 : Fin 1) : Fin 6 ⊕ Fin 1) ≠ Sum.inl i)]
  have hrvW : (fun k : Fin 6 ⊕ Fin 1 => rvec (e k)) =
      Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3) := by
    funext k
    rcases k with k | k
    · rw [show e (Sum.inl k) = Fin.castSucc k from finSumFinEquiv_apply_left k]
      rw [← emb6_cartanE6KernelVec]
      simp [emb6]
    · have hk : k = 0 := Fin.eq_zero k
      subst hk
      rw [show e (Sum.inr (0 : Fin 1)) = Fin.last 6 from by
        have h := finSumFinEquiv_apply_right (m := 6) (n := 1) (0 : Fin 1)
        simpa using h]
      exact show rvec (Fin.last 6) = (0 : ZMod 3) from by decide +kernel
  refine ⟨T, ?_, ?_, ?_⟩
  · intro i
    ext j
    rw [hTapply, hsingle, hfix6]
    by_cases hj : j = Fin.castSucc i
    · subst hj
      rw [show e.symm (Fin.castSucc i) = Sum.inl i from
        finSumFinEquiv_symm_apply_castSucc i]
      simp
    · have hne : e.symm j ≠ Sum.inl i := by
        intro h
        apply hj
        rw [← Equiv.apply_symm_apply e j, h]
        exact finSumFinEquiv_apply_left i
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hj]
  · ext j
    rw [hTapply, hrvW, hfixr]
    have hcomp : Sum.elim cartanE6KernelVec (0 : Fin 1 → ZMod 3) (e.symm j) =
        rvec (e (e.symm j)) := by
      rw [← hrvW]
    rw [hcomp, Equiv.apply_symm_apply]
  · intro u v
    rw [B7_eq_B7Block]
    rw [show (fun i => T u (finSumFinEquiv i)) = TW (fun k => u (finSumFinEquiv k))
        from hTcomp u,
      show (fun i => T v (finSumFinEquiv i)) = TW (fun k => v (finSumFinEquiv k))
        from hTcomp v]
    rw [hcong]
    exact (pair_eq_B7Block u v).symm

theorem linearCombination_single_kernelVec :
    Fintype.linearCombination (ZMod 3)
      (fun i : Fin 6 => (Pi.single (Fin.castSucc i) 1 : Fin 7 → ZMod 3))
      cartanE6KernelVec = rvec := by
  decide +kernel

theorem map_fintypeLinearCombination {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3)) (h : Fin 6 → V) (f : Fin 6 → ZMod 3) :
    chart (Fintype.linearCombination (ZMod 3) h f) =
      Fintype.linearCombination (ZMod 3) (fun i => chart (h i)) f := by
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  simp only [map_smul]

theorem exists_normalized_chart
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chart : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    (h : Fin 6 → V) (c : Fin 6 → ZMod 3) (d : ZMod 3)
    (hchart_h : ∀ i, chart (h i) = Pi.single (Fin.castSucc i) 1)
    (hc : c ⬝ᵥ cartanE6KernelVec ≠ 0) :
    ∃ chart' : V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3),
      (∀ i, chart' (h i) = Pi.single (Fin.castSucc i) 1) ∧
      chart' (Fintype.linearCombination (ZMod 3) h cartanE6KernelVec) = rvec ∧
      chart' (chart.symm rvec) = rvec ∧
      (∀ u v, B7 cartanE6ModThree c d (chart u) (chart v) = pair (chart' u) (chart' v)) := by
  obtain ⟨T, hfix6, hfixr, hcong⟩ := exists_seven_gram_normalize c d hc
  have hsymm : ∀ x : Fin 7 → ZMod 3, T x = x → T.symm x = x := by
    intro x hx
    rw [← hx, LinearEquiv.symm_apply_apply]
    exact hx.symm
  have hw : chart (Fintype.linearCombination (ZMod 3) h cartanE6KernelVec) = rvec := by
    rw [map_fintypeLinearCombination,
      show (fun i => chart (h i)) =
        fun i => (Pi.single (Fin.castSucc i) 1 : Fin 7 → ZMod 3) from funext hchart_h]
    exact linearCombination_single_kernelVec
  refine ⟨chart.trans T.symm, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [LinearEquiv.trans_apply, hchart_h i]
    exact hsymm _ (hfix6 i)
  · rw [LinearEquiv.trans_apply, hw]
    exact hsymm _ hfixr
  · rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact hsymm _ hfixr
  · intro u v
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    rw [← hcong (T.symm (chart u)) (T.symm (chart v))]
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end CFSG.StandardType.E6Seven

public section
namespace CFSG.StandardType
namespace E6Seven

open CFSG.Assembly Module
open CFSG.StandardType.E7F3
open scoped Matrix

@[expose] noncomputable def chartConj
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V)
    (F : MulAut ↥Bs) : Equiv.Perm V7 :=
  (chi.symm.trans ((ggLin (p := 3) ι F).trans chi) : V7 ≃ V7)

theorem chartConj_apply
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V)
    (F : MulAut ↥Bs) (v : V7) :
    chartConj chi ι F v = chi (ggLin (p := 3) ι F (chi.symm v)) := by
  rfl

theorem chartConj_phiL_eq_s7
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V)
    (φL : Fin 6 → MulAut ↥Bs)
    (h' : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V)
    (Bform : LinearMap.BilinForm (ZMod 3) V)
    (hchi_h : ∀ i, chi (h' i) = e i.castSucc)
    (hform_pair : ∀ u v, Bform u v = pair (chi u) (chi v))
    (hB : ∀ i, Bform (h' i) = α i)
    (hlin : ∀ i v, ggLin (p := 3) ι (φL i) v = v - α i v • h' i)
    (i : Fin 6) :
    chartConj chi ι (φL i) = s7 i.castSucc := by
  apply Equiv.ext
  intro v
  rw [chartConj_apply, hlin i (chi.symm v), map_sub, map_smul,
    LinearEquiv.apply_symm_apply, hchi_h i]
  rw [s7, reflPerm_apply, reflFun]
  have halpha : α i (chi.symm v) = pair v (e i.castSucc) := by
    rw [← hB i, hform_pair, hchi_h i, LinearEquiv.apply_symm_apply, pair_comm]
  rw [halpha]

@[expose] noncomputable def chartConjHom
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V) :
    MulAut ↥Bs →* Equiv.Perm V7 where
  toFun := chartConj chi ι
  map_one' := by
    apply Equiv.ext
    intro v
    simp [chartConj, LinearEquiv.trans_apply]
  map_mul' := by
    intro F G
    apply Equiv.ext
    intro v
    simp [chartConj, map_mul, LinearEquiv.mul_apply, LinearEquiv.trans_apply]

theorem chartConj_map_closure_eq_literalL
    {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (chi : V ≃ₗ[ZMod 3] V7) (ι : Additive ↥Bs ≃+ V)
    (φL : Fin 6 → MulAut ↥Bs) (L : Subgroup G)
    (hgenAction : ∀ i, chartConj chi ι (φL i) = s7 i.castSucc)
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL)) :
    Subgroup.map (chartConjHom chi ι) (ggAutomizer L Bs) =
      Subgroup.closure (s7 '' {i : Fin 7 | i.val < 6}) := by
  rw [hclosL, MonoidHom.map_closure]
  have hset : (chartConjHom chi ι) '' (Set.range φL) =
      Set.range (fun i : Fin 6 => s7 i.castSucc) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simpa [chartConjHom] using (hgenAction i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨φL i, ⟨i, rfl⟩, by simpa [chartConjHom] using hgenAction i⟩
  have hset2 : s7 '' {i : Fin 7 | i.val < 6} =
      Set.range (fun i : Fin 6 => s7 i.castSucc) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hlt : j.val < 6 := hj
      let i : Fin 6 := ⟨j.val, hlt⟩
      exact ⟨i, by simp [i]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, by simp, rfl⟩
  rw [hset, hset2]

end E6Seven
end StandardType
end CFSG
end

