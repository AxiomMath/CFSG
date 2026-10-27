module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesReindex
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups TensorProduct

section Form

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def flipX (ι : Type*) : Equiv.Perm (ι → Fin 2) :=
  Equiv.piCongrRight fun _ => Fin.revPerm

@[expose] def tensorForm (u v : (ι → Fin 2) → k) : k := ∑ x, u x * v (flipX ι x)

theorem twistMat_eq (m : ℕ) (g : SL(2, F)) (i j : Fin 2) :
    twistMat k m g i j = (iterateFrobenius k 2 m) (algebraMap F k (g i j)) := by
  simp [twistMat]

theorem twistMat_col (m : ℕ) (g : SL(2, F)) (y z : Fin 2) :
    ∑ a : Fin 2, twistMat k m g a y * twistMat k m g (Fin.rev a) z =
      if z = Fin.rev y then 1 else 0 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.prop
    rwa [Matrix.det_fin_two] at this
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  set τ := (iterateFrobenius k 2 m).comp (algebraMap F k) with hτ
  have h1 : τ (g 0 0) * τ (g 1 1) - τ (g 0 1) * τ (g 1 0) = 1 := by
    have := congrArg τ hdet
    simpa [map_sub, map_mul] using this
  have h1' : τ (g 0 0) * τ (g 1 1) + τ (g 0 1) * τ (g 1 0) = 1 := by
    linear_combination h1 + (τ (g 0 1) * τ (g 1 0)) * h2
  simp only [twistMat_eq]
  fin_cases y <;> fin_cases z <;>
    simp [Fin.sum_univ_two, Fin.rev] <;>
    first
    | linear_combination (τ (g 0 0) * τ (g 1 0)) * h2
    | linear_combination (τ (g 0 1) * τ (g 1 1)) * h2
    | linear_combination h1'

theorem tmatE_col (e : ι → ℕ) (g : SL(2, F)) (y z : ι → Fin 2) :
    ∑ x : ι → Fin 2, tmatE k e g x y * tmatE k e g (flipX ι x) z =
      if z = flipX ι y then 1 else 0 := by
  have := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (Fin 2)))
    (fun i a => twistMat k (e i) g a (y i) * twistMat k (e i) g (Fin.rev a) (z i))
  simp only [Fintype.piFinset_univ] at this
  have h2 : ∀ x : ι → Fin 2, tmatE k e g x y * tmatE k e g (flipX ι x) z =
      ∏ i, (twistMat k (e i) g (x i) (y i) * twistMat k (e i) g (Fin.rev (x i)) (z i)) := by
    intro x
    simp only [tmatE, ← Finset.prod_mul_distrib]
    rfl
  simp only [h2]
  rw [← this]
  simp only [twistMat_col]
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    simpa [flipX] using h i (Finset.mem_univ i)
  · intro h i _
    have := congrFun h i
    simpa [flipX] using this

theorem tensorForm_invariant (e : ι → ℕ) (g : SL(2, F)) (u v : (ι → Fin 2) → k) :
    tensorForm (tensorRep F k e g u) (tensorRep F k e g v) = tensorForm u v := by
  simp only [tensorForm, tensorRep_apply]
  have h1 : ∀ x : ι → Fin 2, ((∑ y, tmatE k e g x y * u y) *
      ∑ z, tmatE k e g (flipX ι x) z * v z) =
      ∑ y, ∑ z, (u y * v z) * (tmatE k e g x y * tmatE k e g (flipX ι x) z) := by
    intro x
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, tmatE_col]
  simp [mul_ite]

end Form

section N3

open CFSG.Quasithin

local notation "K8" => GaloisField 2 3

def idx3 : (Fin 3 → Fin 2) ≃ Fin 2 × (Fin 2 × Fin 2) where
  toFun x := (x 0, x 1, x 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem toLin'_basisFun (M : Matrix (Fin 2) (Fin 2) K8) (a : Fin 2) :
    Matrix.toLin' M (Pi.basisFun K8 (Fin 2) a) = ∑ i, M i a • Pi.basisFun K8 (Fin 2) i := by
  funext j
  simp [Matrix.toLin'_apply, Pi.single_apply, Matrix.mulVec, dotProduct]

theorem sum_comm3 {M : Type*} [AddCommMonoid M] (f : Fin 2 → Fin 2 → Fin 2 → M) :
    ∑ k, ∑ j, ∑ i, f i j k = ∑ i, ∑ j, ∑ k, f i j k := by
  calc ∑ k, ∑ j, ∑ i, f i j k = ∑ j, ∑ k, ∑ i, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, f i j k := Finset.sum_comm

theorem exists_tensorN3_equiv :
    ∃ θ : (((Fin 3 → Fin 2) → K8) ≃ₗ[K8]
      ((Fin 2 → K8) ⊗[K8] ((Fin 2 → K8) ⊗[K8] (Fin 2 → K8)))),
      ∀ (g : SL(2, K8)) (v : (Fin 3 → Fin 2) → K8),
        θ (tensorRep K8 K8 (fun i : Fin 3 => (i : ℕ)) g v) =
          tensorN3Act (g : Matrix (Fin 2) (Fin 2) K8) (θ v) := by
  let bN : Module.Basis (Fin 2) K8 (Fin 2 → K8) := Pi.basisFun K8 (Fin 2)
  let B3 := bN.tensorProduct (bN.tensorProduct bN)
  let θ := (Pi.basisFun K8 (Fin 3 → Fin 2)).equiv B3 idx3
  have hθ : ∀ w, θ w = ∑ x', w x' • B3 (idx3 x') := by
    intro w
    conv_lhs => rw [← (Pi.basisFun K8 (Fin 3 → Fin 2)).sum_repr w]
    simp only [map_sum, map_smul, Pi.basisFun_repr]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact Module.Basis.equiv_apply _ _ _ _
  refine ⟨θ, fun g v => ?_⟩
  have key : θ.toLinearMap ∘ₗ tensorRep K8 K8 (fun i : Fin 3 => (i : ℕ)) g =
      tensorN3Act (g : Matrix (Fin 2) (Fin 2) K8) ∘ₗ θ.toLinearMap := by
    refine (Pi.basisFun K8 (Fin 3 → Fin 2)).ext fun y => ?_
    have hy : θ ((Pi.basisFun K8 (Fin 3 → Fin 2)) y) = B3 (idx3 y) :=
      Module.Basis.equiv_apply _ _ _ _
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hy]
    have hT : tensorRep K8 K8 (fun i : Fin 3 => (i : ℕ)) g
        ((Pi.basisFun K8 (Fin 3 → Fin 2)) y) = fun x' => tmatE K8 (fun i : Fin 3 => (i : ℕ)) g x' y := by
      funext x'
      simp [tensorRep_apply, Pi.single_apply]
    rw [hT, hθ]
    rw [show idx3 y = (y 0, y 1, y 2) from rfl]
    rw [Fintype.sum_equiv idx3 _
      (fun p : Fin 2 × (Fin 2 × Fin 2) =>
        tmatE K8 (fun i : Fin 3 => (i : ℕ)) g (idx3.symm p) y • B3 p) (fun x' => by simp)]
    simp only [B3, Module.Basis.tensorProduct_apply, tensorN3Act, TensorProduct.map_tmul,
      toLin'_basisFun, bN]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul_smul,
      Fintype.sum_prod_type]
    refine Eq.trans ?_ (sum_comm3 _).symm
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Module.Basis.tensorProduct_apply]
    congr 1
    have h0 : idx3.symm (i, j, k) 0 = i := rfl
    have h1 : idx3.symm (i, j, k) 1 = j := rfl
    have h2 : idx3.symm (i, j, k) 2 = k := rfl
    simp [tmatE, Fin.prod_univ_three, twistMat_apply, h0, h1, h2, mul_assoc]
  exact LinearMap.congr_fun key v

end N3

end CFSG.Quasithin.G11.Harris.L2
