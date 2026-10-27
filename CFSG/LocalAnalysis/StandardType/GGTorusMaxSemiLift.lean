module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

import CFSG.LieType.ChevTwo.OppCl.AutLiftsUnitary
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.ChevTwo.OppCl CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem semilinearSimilitudes_finite {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 1 K) (r ε : ℕ) : Finite (semilinearSimilitudes h r ε) := by
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
      (fun _ _ h => DFunLike.coe_injective h)
  haveI : Finite (GL (HypIndex r ε) K) := inferInstance
  haveI : Finite (SemiGL (HypIndex r ε) K) :=
    Finite.of_injective (fun x : SemiGL (HypIndex r ε) K => (x.left, x.right))
      (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  exact Subtype.finite

private noncomputable def semilinearLiftFibre {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) : Subgroup (X × semilinearSimilitudes h r ε) :=
  MonoidHom.eqLocus
    (ψ'.comp (MonoidHom.fst X (semilinearSimilitudes h r ε)))
    ((semilinearAutHom h hr hε).comp (MonoidHom.snd X (semilinearSimilitudes h r ε)))

private noncomputable def semilinearLiftFst {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) :
    ↥(semilinearLiftFibre h hr hε ψ') →* X :=
  (MonoidHom.fst X (semilinearSimilitudes h r ε)).comp
    (semilinearLiftFibre h hr hε ψ').subtype

private noncomputable def semilinearLiftSnd {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) :
    ↥(semilinearLiftFibre h hr hε ψ') →* semilinearSimilitudes h r ε :=
  (MonoidHom.snd X (semilinearSimilitudes h r ε)).comp
    (semilinearLiftFibre h hr hε ψ').subtype

private theorem semilinearLiftFst_surjective {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε))
    (hΦ : Function.Surjective (semilinearAutHom h hr hε)) :
    Function.Surjective (semilinearLiftFst h hr hε ψ') := by
  intro x
  obtain ⟨γ, hγ⟩ := hΦ (ψ' x)
  refine ⟨⟨(x, γ), ?_⟩, rfl⟩
  change (x, γ) ∈ semilinearLiftFibre h hr hε ψ'
  change ψ' x = (semilinearAutHom h hr hε) γ
  exact hγ.symm

private noncomputable def semilinearLiftField {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) :
    ↥(semilinearLiftFibre h hr hε ψ') →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp
    ((semilinearSimilitudes h r ε).subtype.comp (semilinearLiftSnd h hr hε ψ'))

private noncomputable def semilinearLiftLinear {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) :
    Subgroup ↥(semilinearLiftFibre h hr hε ψ') :=
  (semilinearLiftField h hr hε ψ').ker

private theorem semilinearLiftLinear_normal {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) :
    (semilinearLiftLinear h hr hε ψ').Normal :=
  MonoidHom.normal_ker (semilinearLiftField h hr hε ψ')

private theorem semilinearLiftLinear_index {X : Type} [Group X] {K : Type} [Field K]
    [Finite K] {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) (hK : Nat.card K = 4) :
    (semilinearLiftLinear h hr hε ψ').index ≤ 2 := by
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
      (fun _ _ h => DFunLike.coe_injective h)
  rw [semilinearLiftLinear, Subgroup.index_ker]
  calc Nat.card (semilinearLiftField h hr hε ψ').range ≤ Nat.card (K ≃+* K) :=
        Finite.card_subtype_le _
    _ = 2 := by
      simpa using (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
        (p := 2) (n := 2) Nat.prime_two K (by rw [hK]; norm_num)).1

private theorem semilinearLiftLinear_right {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε))
    (x : ↥(semilinearLiftLinear h hr hε ψ')) :
    (((semilinearLiftSnd h hr hε ψ' (x : ↥(semilinearLiftFibre h hr hε ψ')) :
        semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).right) = 1 := by
  have hx : semilinearLiftField h hr hε ψ'
      (x : ↥(semilinearLiftFibre h hr hε ψ')) = 1 := x.2
  simpa [semilinearLiftField] using hx

private noncomputable def semilinearLiftLinearFun {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε))
    (x : ↥(semilinearLiftLinear h hr hε ψ')) : GL (HypIndex r ε) K :=
  (((semilinearLiftSnd h hr hε ψ' (x : ↥(semilinearLiftFibre h hr hε ψ')) :
      semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).left)

private theorem semilinearLiftLinearFun_mul {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε))
    (x y : ↥(semilinearLiftLinear h hr hε ψ')) :
    semilinearLiftLinearFun h hr hε ψ' (x * y) =
      semilinearLiftLinearFun h hr hε ψ' x * semilinearLiftLinearFun h hr hε ψ' y := by
  have hx := semilinearLiftLinear_right h hr hε ψ' x
  have hy := semilinearLiftLinear_right h hr hε ψ' y
  change (((semilinearLiftSnd h hr hε ψ'
      (((x * y : ↥(semilinearLiftLinear h hr hε ψ')) :
        ↥(semilinearLiftFibre h hr hε ψ'))) :
      semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).left) =
    (((semilinearLiftSnd h hr hε ψ'
      (x : ↥(semilinearLiftFibre h hr hε ψ')) :
      semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).left) *
    (((semilinearLiftSnd h hr hε ψ'
      (y : ↥(semilinearLiftFibre h hr hε ψ')) :
      semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).left)
  rw [show ((x * y : ↥(semilinearLiftLinear h hr hε ψ')) :
        ↥(semilinearLiftFibre h hr hε ψ')) =
      (x : ↥(semilinearLiftFibre h hr hε ψ')) *
        (y : ↥(semilinearLiftFibre h hr hε ψ')) from rfl]
  rw [map_mul, Subgroup.coe_mul, SemidirectProduct.mul_left, hx, map_one, MulAut.one_apply]

private noncomputable def semilinearLiftMatrix {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) :
    ↥(semilinearLiftLinear h hr hε ψ') →* GL (HypIndex r ε) K where
  toFun := semilinearLiftLinearFun h hr hε ψ'
  map_one' := by simp [semilinearLiftLinearFun]
  map_mul' := semilinearLiftLinearFun_mul h hr hε ψ'

private theorem semilinearLiftMatrix_injective {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) (hψ' : Function.Injective ψ') :
    Function.Injective (semilinearLiftMatrix h hr hε ψ') := by
  intro x y hxy
  have hleft : (((semilinearLiftSnd h hr hε ψ'
      (x : ↥(semilinearLiftFibre h hr hε ψ')) :
      semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).left) =
    (((semilinearLiftSnd h hr hε ψ'
      (y : ↥(semilinearLiftFibre h hr hε ψ')) :
      semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).left) := hxy
  have hγ : semilinearLiftSnd h hr hε ψ'
      (x : ↥(semilinearLiftFibre h hr hε ψ')) =
      semilinearLiftSnd h hr hε ψ'
        (y : ↥(semilinearLiftFibre h hr hε ψ')) := by
    apply Subtype.ext
    exact SemidirectProduct.ext hleft
      ((semilinearLiftLinear_right h hr hε ψ' x).trans
        (semilinearLiftLinear_right h hr hε ψ' y).symm)
  have hxmem : ψ' (semilinearLiftFst h hr hε ψ'
      (x : ↥(semilinearLiftFibre h hr hε ψ'))) =
      (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ'
        (x : ↥(semilinearLiftFibre h hr hε ψ'))) :=
    (x : ↥(semilinearLiftFibre h hr hε ψ')).2
  have hymem : ψ' (semilinearLiftFst h hr hε ψ'
      (y : ↥(semilinearLiftFibre h hr hε ψ'))) =
      (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ'
        (y : ↥(semilinearLiftFibre h hr hε ψ'))) :=
    (y : ↥(semilinearLiftFibre h hr hε ψ')).2
  have hp : semilinearLiftFst h hr hε ψ'
      (x : ↥(semilinearLiftFibre h hr hε ψ')) =
      semilinearLiftFst h hr hε ψ'
        (y : ↥(semilinearLiftFibre h hr hε ψ')) := by
    apply hψ'
    calc ψ' (semilinearLiftFst h hr hε ψ'
          (x : ↥(semilinearLiftFibre h hr hε ψ'))) =
          (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ'
            (x : ↥(semilinearLiftFibre h hr hε ψ'))) := hxmem
      _ = (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ'
            (y : ↥(semilinearLiftFibre h hr hε ψ'))) := by rw [hγ]
      _ = ψ' (semilinearLiftFst h hr hε ψ'
            (y : ↥(semilinearLiftFibre h hr hε ψ'))) := hymem.symm
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hp hγ

private noncomputable def semilinearLiftReindex (r ε : ℕ) (K : Type) [Field K] :
    GL (HypIndex r ε) K ≃* GL (Fin (2 * r + ε)) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K
    (Fintype.equivFinOfCardEq (card_hypIndex (r := r) (ε := ε)))).toMulEquiv

private theorem semilinearLiftReindex_scalar (r ε : ℕ) (K : Type) [Field K] (c : Kˣ) :
    semilinearLiftReindex r ε K (GeneralLinearGroup.scalar (HypIndex r ε) c) =
      GeneralLinearGroup.scalar (Fin (2 * r + ε)) c := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((Matrix.reindexAlgEquiv K K
    (Fintype.equivFinOfCardEq (card_hypIndex (r := r) (ε := ε)))
    ((GeneralLinearGroup.scalar (HypIndex r ε) c : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) i j) =
    Matrix.scalar (Fin (2 * r + ε)) (c : K) i j
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.submatrix_apply]
  by_cases hij : i = j <;> simp [hij]

private noncomputable def semilinearLiftRepresentation {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (ψ' : X →* MulAut (hypPSU h r ε)) :
    ↥(semilinearLiftLinear h hr hε ψ') →* GL (Fin (2 * r + ε)) K :=
  (semilinearLiftReindex r ε K).toMonoidHom.comp (semilinearLiftMatrix h hr hε ψ')

private theorem semilinearLiftRepresentation_injective {X : Type} [Group X]
    {K : Type} [Field K] {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (ψ' : X →* MulAut (hypPSU h r ε)) (hψ' : Function.Injective ψ') :
    Function.Injective (semilinearLiftRepresentation h hr hε ψ') := by
  intro x y hxy
  exact semilinearLiftMatrix_injective h hr hε ψ' hψ'
    ((semilinearLiftReindex r ε K).injective hxy)

private theorem semilinearLiftRepresentation_kernel_scalar {X : Type} [Group X]
    {K : Type} [Field K] {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε))
    (z : ↥(semilinearLiftLinear h hr hε ψ'))
    (hz : semilinearLiftFst h hr hε ψ'
      (z : ↥(semilinearLiftFibre h hr hε ψ')) = 1) :
    ∃ c : K,
      ((semilinearLiftRepresentation h hr hε ψ' z : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
        Matrix.scalar (Fin (2 * r + ε)) c := by
  have hΦ : (semilinearAutHom h hr hε)
      (semilinearLiftSnd h hr hε ψ' (z : ↥(semilinearLiftFibre h hr hε ψ'))) = 1 := by
    have hmem : ψ' (semilinearLiftFst h hr hε ψ'
        (z : ↥(semilinearLiftFibre h hr hε ψ'))) =
        (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ'
          (z : ↥(semilinearLiftFibre h hr hε ψ'))) :=
      (z : ↥(semilinearLiftFibre h hr hε ψ')).2
    rw [hz, map_one] at hmem
    exact hmem.symm
  obtain ⟨-, c, hc⟩ := (semilinearAutHom_eq_one_iff h hr hε hn
    (semilinearLiftSnd h hr hε ψ'
      (z : ↥(semilinearLiftFibre h hr hε ψ')))).mp hΦ
  refine ⟨(c : K), ?_⟩
  have hlin : semilinearLiftMatrix h hr hε ψ' z =
      GeneralLinearGroup.scalar (HypIndex r ε) c := hc
  have hρ : semilinearLiftRepresentation h hr hε ψ' z =
      GeneralLinearGroup.scalar (Fin (2 * r + ε)) c := by
    change semilinearLiftReindex r ε K (semilinearLiftMatrix h hr hε ψ' z) = _
    rw [hlin, semilinearLiftReindex_scalar]
  rw [hρ, Matrix.GeneralLinearGroup.coe_scalar]

private noncomputable def semilinearLiftKerExists {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε))
    (z : (semilinearLiftFst h hr hε ψ').ker) : ∃ c : Kˣ,
      (((semilinearLiftSnd h hr hε ψ' z : semilinearSimilitudes h r ε) :
        SemiGL (HypIndex r ε) K).left) = GeneralLinearGroup.scalar (HypIndex r ε) c := by
  have hmem : ψ' (semilinearLiftFst h hr hε ψ' z) =
      (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ' z) :=
    (z : ↥(semilinearLiftFibre h hr hε ψ')).2
  have hΦ : (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ' z) = 1 := by
    rw [← hmem, MonoidHom.mem_ker.mp z.2, map_one]
  exact ((semilinearAutHom_eq_one_iff h hr hε hn
    (semilinearLiftSnd h hr hε ψ' z)).mp hΦ).2

private noncomputable def semilinearLiftKerCoeff {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε))
    (z : (semilinearLiftFst h hr hε ψ').ker) : Kˣ :=
  Classical.choose (semilinearLiftKerExists h hr hε hn ψ' z)

private theorem semilinearLiftKerCoeff_spec {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε))
    (z : (semilinearLiftFst h hr hε ψ').ker) :
    (((semilinearLiftSnd h hr hε ψ' z : semilinearSimilitudes h r ε) :
      SemiGL (HypIndex r ε) K).left) =
      GeneralLinearGroup.scalar (HypIndex r ε) (semilinearLiftKerCoeff h hr hε hn ψ' z) :=
  Classical.choose_spec (semilinearLiftKerExists h hr hε hn ψ' z)

private theorem semilinearLiftKerRight {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε))
    (z : (semilinearLiftFst h hr hε ψ').ker) :
    (((semilinearLiftSnd h hr hε ψ' z : semilinearSimilitudes h r ε) :
      SemiGL (HypIndex r ε) K).right) = 1 := by
  have hmem : ψ' (semilinearLiftFst h hr hε ψ' z) =
      (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ' z) :=
    (z : ↥(semilinearLiftFibre h hr hε ψ')).2
  have hΦ : (semilinearAutHom h hr hε) (semilinearLiftSnd h hr hε ψ' z) = 1 := by
    rw [← hmem, MonoidHom.mem_ker.mp z.2, map_one]
  exact ((semilinearAutHom_eq_one_iff h hr hε hn
    (semilinearLiftSnd h hr hε ψ' z)).mp hΦ).1

private theorem semilinearLiftAut_scalar {K : Type} [Field K] {r ε : ℕ}
    (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε)
    (c : Kˣ) :
    (semilinearAutHom h hr hε) ⟨SemidirectProduct.inl
      (GeneralLinearGroup.scalar (HypIndex r ε) c), scalarSim_mem h c⟩ = 1 := by
  rw [semilinearAutHom_eq_one_iff h hr hε hn _]
  exact ⟨rfl, c, rfl⟩

private theorem semilinearLiftFibre_scalar_mem {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε)) (c : Kˣ) :
    (1, ⟨SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex r ε) c),
      scalarSim_mem h c⟩) ∈ semilinearLiftFibre h hr hε ψ' := by
  change (ψ'.comp (MonoidHom.fst X (semilinearSimilitudes h r ε))) (1, _) =
    ((semilinearAutHom h hr hε).comp (MonoidHom.snd X (semilinearSimilitudes h r ε))) (1, _)
  simp [semilinearLiftAut_scalar h hr hε hn c]

private noncomputable def semilinearLiftScalarSection {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε)) (c : Kˣ) :
    (semilinearLiftFst h hr hε ψ').ker :=
  ⟨⟨(1, ⟨SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex r ε) c),
      scalarSim_mem h c⟩), semilinearLiftFibre_scalar_mem h hr hε hn ψ' c⟩, rfl⟩

private theorem semilinearLiftScalar_injective {K : Type} [Field K] {r ε : ℕ}
    (hr : 1 ≤ r) : Function.Injective
      (fun c : Kˣ => GeneralLinearGroup.scalar (HypIndex r ε) c) := by
  intro c d hcd
  have h' : (c : K) = (d : K) := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using
      congrArg (fun g : GL (HypIndex r ε) K =>
        ((g : Matrix (HypIndex r ε) (HypIndex r ε) K)
          (Sum.inl (⟨0, by omega⟩ : Fin r))
          (Sum.inl (⟨0, by omega⟩ : Fin r)))) hcd
  exact Units.ext h'

private theorem semilinearLiftKerCoeff_left_inv {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε))
    (z : (semilinearLiftFst h hr hε ψ').ker) :
    semilinearLiftScalarSection h hr hε hn ψ'
      (semilinearLiftKerCoeff h hr hε hn ψ' z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change (1 : X) = semilinearLiftFst h hr hε ψ' z
    exact (MonoidHom.mem_ker.mp z.2).symm
  · apply Subtype.ext
    apply SemidirectProduct.ext
    · exact (semilinearLiftKerCoeff_spec h hr hε hn ψ' z).symm
    · change (((⟨SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex r ε)
          (semilinearLiftKerCoeff h hr hε hn ψ' z)), scalarSim_mem h _⟩ :
          semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).right) =
        (((semilinearLiftSnd h hr hε ψ' z : semilinearSimilitudes h r ε) :
          SemiGL (HypIndex r ε) K).right)
      rw [semilinearLiftKerRight h hr hε hn ψ' z]
      rfl

private theorem semilinearLiftKerCoeff_right_inv {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε)) (c : Kˣ) :
    semilinearLiftKerCoeff h hr hε hn ψ'
      (semilinearLiftScalarSection h hr hε hn ψ' c) = c := by
  apply semilinearLiftScalar_injective (r := r) (ε := ε) hr
  change GeneralLinearGroup.scalar (HypIndex r ε)
      (semilinearLiftKerCoeff h hr hε hn ψ'
        (semilinearLiftScalarSection h hr hε hn ψ' c)) =
    GeneralLinearGroup.scalar (HypIndex r ε) c
  rw [← semilinearLiftKerCoeff_spec h hr hε hn ψ'
    (semilinearLiftScalarSection h hr hε hn ψ' c)]
  rfl

private noncomputable def semilinearLiftKerEquiv {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε)) :
    (semilinearLiftFst h hr hε ψ').ker ≃ Kˣ :=
  { toFun := semilinearLiftKerCoeff h hr hε hn ψ'
    invFun := semilinearLiftScalarSection h hr hε hn ψ'
    left_inv := semilinearLiftKerCoeff_left_inv h hr hε hn ψ'
    right_inv := semilinearLiftKerCoeff_right_inv h hr hε hn ψ' }

private theorem semilinearLiftKer_card {X : Type} [Group X] {K : Type} [Field K]
    {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) (ψ' : X →* MulAut (hypPSU h r ε)) (hK : Nat.card K = 4) :
    Nat.card (semilinearLiftFst h hr hε ψ').ker = 3 := by
  rw [Nat.card_congr (semilinearLiftKerEquiv h hr hε hn ψ'), Nat.card_units, hK]

private theorem semilinearLiftFibre_finite {X : Type} [Group X] [Finite X] {K : Type}
    [Field K] [Finite K] {r ε : ℕ} (h : UnitaryFieldData 2 1 K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (ψ' : X →* MulAut (hypPSU h r ε)) :
    Finite ↥(semilinearLiftFibre h hr hε ψ') := by
  haveI : Finite (semilinearSimilitudes h r ε) := semilinearSimilitudes_finite h r ε
  exact Subtype.finite

theorem exists_semilinearLift {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 4) (d : ℕ) (hd : 4 ≤ d)
    (ψ : X →* MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ 1) K)))
    (hψ : Function.Injective ψ) :
    ∃ (M : Type) (_ : Group M) (_ : Finite M) (p : M →* X) (M0 : Subgroup M)
      (ρ : ↥M0 →* GL (Fin d) K),
      Function.Surjective p ∧ Nat.card p.ker = 3 ∧ M0.Normal ∧ M0.index ≤ 2 ∧
        Function.Injective ρ ∧
        ∀ z : ↥M0, p z = 1 → ∃ c : K,
          ((ρ z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.scalar (Fin d) c := by
  classical
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ d = 2 * r + ε :=
    ⟨d / 2, d % 2, by omega, by omega⟩
  have hr2 : 2 ≤ r := by omega
  have hr : 1 ≤ r := by omega
  have hn : 3 ≤ 2 * r + ε := by omega
  have hn1 : 1 ≤ 2 * r + ε := by omega
  have h : UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_refl 1, by rw [hK]; norm_num⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  let e : StatedProj (StatedSU (2 * r + ε) (2 ^ 1) K) ≃* hypPSU h r ε :=
    (unitaryPSUEquiv h hn1).symm.trans (hypProjTransport h hR).symm
  let ψ' : X →* MulAut (hypPSU h r ε) := (MulAut.congr e).toMonoidHom.comp ψ
  have hψ' : Function.Injective ψ' := by
    intro a b hab
    exact hψ ((MulAut.congr e).injective (by simpa [ψ'] using hab))
  have hΦ_surj : Function.Surjective (semilinearAutHom h hr hε) :=
    semilinearAutHom_surjective' h hr hε (Or.inr hr2) hn
  haveI : Finite ↥(semilinearLiftFibre h hr hε ψ') :=
    semilinearLiftFibre_finite h hr hε ψ'
  refine ⟨↥(semilinearLiftFibre h hr hε ψ'), inferInstance, inferInstance,
    semilinearLiftFst h hr hε ψ', semilinearLiftLinear h hr hε ψ',
    semilinearLiftRepresentation h hr hε ψ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact semilinearLiftFst_surjective h hr hε ψ' hΦ_surj
  · exact semilinearLiftKer_card h hr hε hn ψ' hK
  · exact semilinearLiftLinear_normal h hr hε ψ'
  · exact semilinearLiftLinear_index h hr hε ψ' hK
  · exact semilinearLiftRepresentation_injective h hr hε ψ' hψ'
  · exact semilinearLiftRepresentation_kernel_scalar h hr hε hn ψ'

end CFSG.StandardType.FrameRoute
