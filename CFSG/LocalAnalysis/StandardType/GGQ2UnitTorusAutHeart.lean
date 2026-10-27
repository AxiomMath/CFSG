module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitNormalizerStatements
import CFSG.LocalAnalysis.StandardType.GGQ2UnitDiag
import CFSG.LocalAnalysis.StandardType.GGQ2CensusChainA
import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
import CFSG.Mathlib.Perm.FixingSubgroupSwap

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.SectionRank.OddCover (diagHom det_diagHom)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] {N : ℕ} (ζ : Multiplicative (ZMod 3) →* Kˣ)

private theorem uth_exists_rep_heart (x : ↥(UnitRaw.heart N)) :
    ∃ (w : UnitRaw.W N) (hw : (UnitRaw.oneLine N).mkQ w ∈ UnitRaw.heart N),
      (⟨(UnitRaw.oneLine N).mkQ w, hw⟩ : ↥(UnitRaw.heart N)) = x := by
  obtain ⟨u, hu, hueq⟩ := Submodule.mem_map.mp x.2
  exact ⟨u, hueq ▸ x.2, Subtype.ext hueq⟩

private theorem uth_projConj_diagOf_eq_iff (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N) (w w' : UnitRaw.W N)
    (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
    (hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) :
    TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ =
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ ↔
      (UnitRaw.oneLine N).mkQ w = (UnitRaw.oneLine N).mkQ w' := by
  rw [show (⟨diagOf ζ w, hD⟩ : Subgroup.normalizer
        (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ from Subtype.ext rfl,
    show (⟨diagOf ζ w', hD'⟩ : Subgroup.normalizer
        (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ from Subtype.ext rfl]
  exact projConj_diagOf_eq_iff ζ h hK hζ hN w w'

private theorem uth_mem_scalars_of_projConj_eq_one (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hN : 4 ≤ N)
    {M : Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))}
    (hM : TableB.projConj (unitarySU 2 1 K N) M = 1) :
    (M : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hdq : (N, 2 ^ 1) ≠ (3, 2) := by
    intro he
    have hN3 : N = 3 := by simpa using congrArg Prod.fst he
    omega
  exact TableBUE.mem_scalars_of_projConj_eq_one (n := 1) (d := N) (p := 3) h hK' (by omega) hdq
    Nat.prime_three (by norm_num) hM

private theorem uth_exists_scalar_mul_of_projConj_eq (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hN : 4 ≤ N)
    {A A' : Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))}
    (hAA' : TableB.projConj (unitarySU 2 1 K N) A =
      TableB.projConj (unitarySU 2 1 K N) A') :
    ∃ z : Kˣ, (A : GL (Fin N) K) = (A' : GL (Fin N) K) *
      Matrix.GeneralLinearGroup.scalar (Fin N) z := by
  have hmem : (A : GL (Fin N) K)⁻¹ * (A' : GL (Fin N) K) ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ A.2) A'.2
  have h1 : TableB.projConj (unitarySU 2 1 K N)
      (⟨(A : GL (Fin N) K)⁻¹ * (A' : GL (Fin N) K), hmem⟩ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) = 1 := by
    rw [show (⟨(A : GL (Fin N) K)⁻¹ * (A' : GL (Fin N) K), hmem⟩ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) = A⁻¹ * A' from
      Subtype.ext rfl, map_mul, map_inv, hAA', inv_mul_cancel]
  have hscal : (A : GL (Fin N) K)⁻¹ * (A' : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K :=
    uth_mem_scalars_of_projConj_eq_one h hK hN h1
  rw [largeEvenScalars_def, MonoidHom.mem_range] at hscal
  obtain ⟨c, hc⟩ := hscal
  refine ⟨c⁻¹, ?_⟩
  have hEq : (A' : GL (Fin N) K) = (A : GL (Fin N) K) *
      Matrix.GeneralLinearGroup.scalar (Fin N) c := by
    calc (A' : GL (Fin N) K) = (A : GL (Fin N) K) *
          ((A : GL (Fin N) K)⁻¹ * (A' : GL (Fin N) K)) := by group
      _ = (A : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) c := by rw [hc]
  calc (A : GL (Fin N) K) = (A : GL (Fin N) K) *
        Matrix.GeneralLinearGroup.scalar (Fin N) c *
        (Matrix.GeneralLinearGroup.scalar (Fin N) c)⁻¹ := by group
    _ = (A' : GL (Fin N) K) * (Matrix.GeneralLinearGroup.scalar (Fin N) c)⁻¹ := by
        rw [← hEq]
    _ = (A' : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ := by
        rw [map_inv]

private theorem uth_diagOf_single_sub {i j : Fin N} (hij : i ≠ j) :
    (((diagOf ζ (Pi.single i 1 - Pi.single j 1) : GL (Fin N) K)) :
        Matrix (Fin N) (Fin N) K) =
      Matrix.diagonal (CFSG.StandardType.TypeA.rootT
        ((ζ (Multiplicative.ofAdd (1 : ZMod 3))) : K) i j) := by
  rw [coe_diagOf]
  congr 1
  funext k
  by_cases hki : k = i
  · rw [hki]
    rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero,
      CFSG.StandardType.TypeA.rootT_left]
  · by_cases hkj : k = j
    · rw [hkj]
      have hneg : Multiplicative.ofAdd (-1 : ZMod 3) =
          (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ := ofAdd_neg 1
      rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_sub, hneg,
        map_inv, Units.val_inv_eq_inv_val, CFSG.StandardType.TypeA.rootT_right _ hij]
    · rw [Pi.sub_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, sub_zero,
        show Multiplicative.ofAdd (0 : ZMod 3) = 1 from ofAdd_zero, map_one,
        Units.val_one, CFSG.StandardType.TypeA.rootT_other _ hki hkj]

private theorem uth_permSU_conj_diagOf (h : UnitaryFieldData 2 1 K) (σ : Equiv.Perm (Fin N))
    (w : UnitRaw.W N) :
    ((LineU.permSU h σ : ↥(unitarySU 2 1 K N)) : GL (Fin N) K) * diagOf ζ w *
        (((LineU.permSU h σ : ↥(unitarySU 2 1 K N)) : GL (Fin N) K))⁻¹ =
      diagOf ζ (fun i => w (σ.symm i)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, LineU.coe_permSU, coe_diagOf, coe_diagOf,
    LineU.coe_permGL_matrix, LineU.coe_permGL_inv_matrix, LineU.permMatrix_conj_diag]
  rfl

private theorem uth_one_mem_unitTorusAutH (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N)
    (X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))) :
    (1 : ↥(UnitRaw.heart N) ≃ₗ[ZMod 3] ↥(UnitRaw.heart N)) ∈
      unitTorusAutH ζ N X := by
  refine ⟨1, X.one_mem, ?_⟩
  intro w w' hD hD' hw hw' hww'
  have hmk : (UnitRaw.oneLine N).mkQ w' = (UnitRaw.oneLine N).mkQ w := by
    simpa using congrArg Subtype.val hww'
  rw [map_one, one_mul, inv_one, mul_one]
  exact (uth_projConj_diagOf_eq_iff ζ h hK hζ hN w w' hD hD').mpr hmk.symm

private theorem uth_mul_mem_unitTorusAutH (h : UnitaryFieldData 2 1 K)
    {X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))}
    {φ ψ : ↥(UnitRaw.heart N) ≃ₗ[ZMod 3] ↥(UnitRaw.heart N)}
    (hφ : φ ∈ unitTorusAutH ζ N X) (hψ : ψ ∈ unitTorusAutH ζ N X) :
    φ * ψ ∈ unitTorusAutH ζ N X := by
  obtain ⟨y, hy, hyreal⟩ := hφ
  obtain ⟨z, hz, hzreal⟩ := hψ
  refine ⟨y * z, X.mul_mem hy hz, ?_⟩
  intro w w' hD hD' hw hw' hww'
  rw [LinearEquiv.mul_apply] at hww'
  obtain ⟨w'', hw'', hw''eq⟩ := uth_exists_rep_heart (N := N)
    (ψ ⟨(UnitRaw.oneLine N).mkQ w, hw⟩)
  have hD'' : diagOf ζ w'' ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    diagOf_mem_normalizer ζ h w''
  have h1 := hzreal w w'' hD hD'' hw hw'' hw''eq
  have h2 := hyreal w'' w' hD'' hD' hw'' hw' (by rw [hw''eq]; exact hww')
  calc MulAut.conj (y * z) * TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ *
        (MulAut.conj (y * z))⁻¹
      = MulAut.conj y * (MulAut.conj z * TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ *
          (MulAut.conj z)⁻¹) * (MulAut.conj y)⁻¹ := by
        rw [map_mul]
        group
    _ = MulAut.conj y * TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w'', hD''⟩ *
          (MulAut.conj y)⁻¹ := by rw [h1]
    _ = TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ := h2

private theorem uth_inv_mem_unitTorusAutH
    {X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))}
    {φ : ↥(UnitRaw.heart N) ≃ₗ[ZMod 3] ↥(UnitRaw.heart N)}
    (hφ : φ ∈ unitTorusAutH ζ N X) :
    φ⁻¹ ∈ unitTorusAutH ζ N X := by
  obtain ⟨y, hy, hyreal⟩ := hφ
  refine ⟨y⁻¹, X.inv_mem hy, ?_⟩
  intro w w' hD hD' hw hw' hww'
  have hclass : (⟨(UnitRaw.oneLine N).mkQ w, hw⟩ : ↥(UnitRaw.heart N)) =
      φ ⟨(UnitRaw.oneLine N).mkQ w', hw'⟩ := by
    have := congrArg φ hww'
    simpa using this.symm
  have h := hyreal w' w hD' hD hw' hw hclass
  calc MulAut.conj (y⁻¹) * TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ *
        (MulAut.conj (y⁻¹))⁻¹
      = MulAut.conj (y⁻¹) * (MulAut.conj y * TableB.projConj (unitarySU 2 1 K N)
          ⟨diagOf ζ w', hD'⟩ * (MulAut.conj y)⁻¹) * (MulAut.conj (y⁻¹))⁻¹ := by rw [h]
    _ = TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ := by
        rw [map_inv]
        group

private theorem uth_closure_subset_unitTorusAutH (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N)
    {X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))}
    {T : Set (↥(UnitRaw.heart N) ≃ₗ[ZMod 3] ↥(UnitRaw.heart N))}
    (hT : T ⊆ unitTorusAutH ζ N X) :
    ((Subgroup.closure T : Subgroup _) : Set _) ⊆ unitTorusAutH ζ N X := by
  intro φ hφ
  induction hφ using Subgroup.closure_induction with
  | mem x hx => exact hT hx
  | one => exact uth_one_mem_unitTorusAutH ζ h hK hζ hN X
  | mul x y _ _ hx hy => exact uth_mul_mem_unitTorusAutH ζ h hx hy
  | inv x _ hx => exact uth_inv_mem_unitTorusAutH ζ hx

private theorem uth_permEquivH_swap_mem_unitTorusAutH (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N)
    {X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))} {i j : Fin N}
    (hy : LargeEvenProjMk (unitarySU 2 1 K N) (LineU.permSU h (Equiv.swap i j)) ∈ X) :
    UnitRaw.permEquivH N (Equiv.swap i j) ∈ unitTorusAutH ζ N X := by
  set P : ↥(unitarySU 2 1 K N) := LineU.permSU h (Equiv.swap i j) with hP
  refine ⟨(P : LargeEvenProj (unitarySU 2 1 K N)), hy, ?_⟩
  intro w w' hD hD' hw hw' hww'
  set A : GL (Fin N) K := (P : GL (Fin N) K) * diagOf ζ w * (P : GL (Fin N) K)⁻¹ with hA
  have hAmem : A ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) := by
    rw [hA]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer P.2) hD)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer P.2))
  have hmk : (UnitRaw.oneLine N).mkQ (fun k => w ((Equiv.swap i j).symm k)) =
      (UnitRaw.oneLine N).mkQ w' := by
    have hval := congrArg (fun x : ↥(UnitRaw.heart N) => (x : UnitRaw.Vfull N)) hww'
    rw [UnitRaw.coe_permEquivH, UnitRaw.permEquivQ_mk] at hval
    exact hval.symm
  have hconj : MulAut.conj ((P : LargeEvenProj (unitarySU 2 1 K N))) =
      TableB.projConj (unitarySU 2 1 K N)
        ⟨(P : GL (Fin N) K), Subgroup.le_normalizer P.2⟩ :=
    (TableB.projConj_of_mem (unitarySU 2 1 K N) (P : GL (Fin N) K) P.2).symm
  calc MulAut.conj ((P : LargeEvenProj (unitarySU 2 1 K N))) *
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ *
        (MulAut.conj ((P : LargeEvenProj (unitarySU 2 1 K N))))⁻¹
      = TableB.projConj (unitarySU 2 1 K N) ⟨A, hAmem⟩ := by
        rw [hconj, ← map_mul, ← map_inv, ← map_mul]
        congr 1
    _ = TableB.projConj (unitarySU 2 1 K N)
          ⟨diagOf ζ (fun k => w ((Equiv.swap i j).symm k)),
            diagOf_mem_normalizer ζ h _⟩ := by
        rw [show (⟨A, hAmem⟩ : Subgroup.normalizer
            (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
            ⟨diagOf ζ (fun k => w ((Equiv.swap i j).symm k)),
              diagOf_mem_normalizer ζ h _⟩ from by
          apply Subtype.ext
          show A = diagOf ζ (fun k => w ((Equiv.swap i j).symm k))
          rw [hA, uth_permSU_conj_diagOf ζ h (Equiv.swap i j) w]]
    _ = TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ :=
        (uth_projConj_diagOf_eq_iff ζ h hK hζ hN _ _ (diagOf_mem_normalizer ζ h _) hD').mpr
          hmk

private theorem uth_permEquivH_mem_ambientNormalizerH (π : Equiv.Perm (Fin N)) :
    UnitRaw.permEquivH N π ∈ UnitRaw.ambientNormalizerH N := by
  refine Equiv.Perm.swap_induction_on π ?_ ?_
  · rw [← UnitRaw.permHomH_apply, map_one]
    exact Subgroup.one_mem _
  · intro f x y _ ih
    rw [← UnitRaw.permHomH_apply, map_mul, UnitRaw.permHomH_apply]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨x, y, rfl⟩) ih

private theorem uth_fixes_of_blockSU {S : Finset (Fin N)} {B : ↥(unitarySU 2 1 K N)}
    {π : Equiv.Perm (Fin N)} (hB : B ∈ TableBUE.blockSU S)
    (hπ : ∀ u : Fin N → K,
      ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * Matrix.diagonal u =
        Matrix.diagonal (u ∘ π) * ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) :
    ∀ k, k ∉ S → π k = k := by
  intro k hk
  by_contra hne
  have hBk : ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) k k = 1 := by
    rw [TableBUE.mem_blockSU] at hB
    simpa using hB k k (Or.inl hk)
  set u : Fin N → K := Pi.single (π k) (1 : K) with hu
  have hu1 : u (π k) = 1 := by rw [hu]; exact Pi.single_eq_same _ _
  have hu2 : u k = 0 := by rw [hu]; exact Pi.single_eq_of_ne (M := fun _ => K) (Ne.symm hne) (1 : K)
  have h := congrFun (congrFun (hπ u) k) k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  simp only [Function.comp_apply] at h
  rw [hu1, hu2, mul_zero, one_mul, hBk] at h
  exact zero_ne_one h

private theorem uth_permEquivH_mem_normalizerOfH {S : Finset (Fin N)} {π : Equiv.Perm (Fin N)}
    (hfix : ∀ k, k ∉ S → π k = k) :
    UnitRaw.permEquivH N π ∈ UnitRaw.normalizerOfH S := by
  classical
  set T : Set (Equiv.Perm (Fin N)) := {σ | ∃ i ∈ S, ∃ j ∈ S, σ = Equiv.swap i j} with hT
  have hπ : π ∈ Subgroup.closure T := by
    refine CFSG.Perm.fixingSubgroup_compl_le_of_swap_mem (S : Set (Fin N))
      (Subgroup.closure T) ?_ ?_
    · intro a ha b hb
      exact Subgroup.subset_closure ⟨a, ha, b, hb, rfl⟩
    · rw [mem_fixingSubgroup_iff (Equiv.Perm (Fin N))]
      intro x hx
      simpa using hfix x hx
  have himg : UnitRaw.permEquivH N π ∈ Subgroup.map (UnitRaw.permHomH N) (Subgroup.closure T) :=
    ⟨π, hπ, UnitRaw.permHomH_apply N π⟩
  have hset : (⇑(UnitRaw.permHomH N) '' T) =
      {U | ∃ i ∈ S, ∃ j ∈ S, U = UnitRaw.permEquivH N (Equiv.swap i j)} := by
    ext U
    constructor
    · rintro ⟨σ, ⟨i, hi, j, hj, rfl⟩, rfl⟩
      exact ⟨i, hi, j, hj, by rw [UnitRaw.permHomH_apply]⟩
    · rintro ⟨i, hi, j, hj, rfl⟩
      exact ⟨Equiv.swap i j, ⟨i, hi, j, hj, rfl⟩, by rw [UnitRaw.permHomH_apply]⟩
  rw [MonoidHom.map_closure, hset] at himg
  rw [UnitRaw.normalizerOfH]
  exact himg

private theorem uth_exists_perm_of_realizes (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N)
    (B : ↥(unitarySU 2 1 K N)) (φ : ↥(UnitRaw.heart N) ≃ₗ[ZMod 3] ↥(UnitRaw.heart N))
    (hreal : ∀ (w w' : UnitRaw.W N)
      (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
      (hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
      (hw : (UnitRaw.oneLine N).mkQ w ∈ UnitRaw.heart N)
      (hw' : (UnitRaw.oneLine N).mkQ w' ∈ UnitRaw.heart N),
      (⟨(UnitRaw.oneLine N).mkQ w', hw'⟩ : ↥(UnitRaw.heart N)) =
          φ ⟨(UnitRaw.oneLine N).mkQ w, hw⟩ →
        MulAut.conj ((B : ↥(unitarySU 2 1 K N)) :
            LargeEvenProj (unitarySU 2 1 K N)) *
          TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ *
          (MulAut.conj ((B : ↥(unitarySU 2 1 K N)) :
            LargeEvenProj (unitarySU 2 1 K N)))⁻¹ =
          TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩) :
    ∃ π : Equiv.Perm (Fin N), φ = UnitRaw.permEquivH N π⁻¹ ∧
      ∀ u : Fin N → K,
        ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * Matrix.diagonal u =
          Matrix.diagonal (u ∘ π) * ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  classical
  have hBconj : MulAut.conj ((B : ↥(unitarySU 2 1 K N)) :
        LargeEvenProj (unitarySU 2 1 K N)) =
      TableB.projConj (unitarySU 2 1 K N)
        ⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩ :=
    (TableB.projConj_of_mem (unitarySU 2 1 K N) (B : GL (Fin N) K) B.2).symm
  have hproj : ∀ (w w' : UnitRaw.W N)
      (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
      (hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
      (hw : (UnitRaw.oneLine N).mkQ w ∈ UnitRaw.heart N)
      (hw' : (UnitRaw.oneLine N).mkQ w' ∈ UnitRaw.heart N),
      (⟨(UnitRaw.oneLine N).mkQ w', hw'⟩ : ↥(UnitRaw.heart N)) =
          φ ⟨(UnitRaw.oneLine N).mkQ w, hw⟩ →
      TableB.projConj (unitarySU 2 1 K N)
        ⟨(B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer B.2) hD)
            (Subgroup.inv_mem _ (Subgroup.le_normalizer B.2))⟩ =
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ := by
    intro w w' hD hD' hw hw' heq
    have h1 := hreal w w' hD hD' hw hw' heq
    rw [hBconj] at h1
    calc TableB.projConj (unitarySU 2 1 K N)
          ⟨(B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹, _⟩
        = TableB.projConj (unitarySU 2 1 K N)
            (⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩ *
              ⟨diagOf ζ w, hD⟩ *
              ⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩⁻¹) :=
          congrArg (TableB.projConj (unitarySU 2 1 K N)) (Subtype.ext rfl)
      _ = TableB.projConj (unitarySU 2 1 K N)
            ⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩ *
          TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ *
          (TableB.projConj (unitarySU 2 1 K N)
            ⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ := h1
  set ξ : Kˣ := ζ (Multiplicative.ofAdd (1 : ZMod 3)) with hξdef
  have hξ3 : ξ ^ 3 = 1 := zeta_pow_three ζ _
  have hξinv : ξ ≠ ξ⁻¹ := by
    intro hinv
    have h2 : ξ * ξ = 1 := by
      have hc := congrArg (· * ξ) hinv
      simpa using hc
    have h1 : ξ = 1 := by
      calc ξ = ξ ^ 3 * (ξ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hξ3, sq, h2, inv_one, mul_one]
    have hof : Multiplicative.ofAdd (1 : ZMod 3) = 1 := by
      apply hζ
      rw [hξdef.symm, map_one]
      exact h1
    exact one_ne_zero (Multiplicative.ofAdd.injective hof)
  have hξval : (ξ : K) ≠ ((ξ : K))⁻¹ := by
    intro h'
    exact hξinv (Units.ext (by rwa [Units.val_inv_eq_inv_val]))
  have hmono : ∀ i j : Fin N, i ≠ j → ∃ D : Fin N → K,
      ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
          Matrix.diagonal (CFSG.StandardType.TypeA.rootT (ξ : K) i j) =
        Matrix.diagonal D * ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
    intro i j hij
    set w : UnitRaw.W N := Pi.single i 1 - Pi.single j 1 with hwdef
    have hw : (UnitRaw.oneLine N).mkQ w ∈ UnitRaw.heart N :=
      UnitRaw.mkQ_single_sub_single_mem_heart N i j
    have hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
      diagOf_mem_normalizer ζ h w
    obtain ⟨w', hw', hw'eq⟩ :=
      uth_exists_rep_heart (φ ⟨(UnitRaw.oneLine N).mkQ w, hw⟩)
    have hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
      diagOf_mem_normalizer ζ h w'
    obtain ⟨z, hz⟩ :=
      uth_exists_scalar_mul_of_projConj_eq h hK hN (hproj w w' hD hD' hw hw' hw'eq)
    have hz' : (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ =
        diagOf ζ w' * Matrix.GeneralLinearGroup.scalar (Fin N) z := hz
    have hBD : (B : GL (Fin N) K) * diagOf ζ w =
        (diagOf ζ w' * Matrix.GeneralLinearGroup.scalar (Fin N) z) *
          (B : GL (Fin N) K) := by
      calc (B : GL (Fin N) K) * diagOf ζ w =
            ((B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹) *
              (B : GL (Fin N) K) := by group
        _ = (diagOf ζ w' * Matrix.GeneralLinearGroup.scalar (Fin N) z) *
              (B : GL (Fin N) K) := by rw [hz']
    refine ⟨fun k => ((ζ (Multiplicative.ofAdd (w' k)) : Kˣ) : K) * ((z : Kˣ) : K), ?_⟩
    have hDmat : ((diagOf ζ w : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        Matrix.diagonal (CFSG.StandardType.TypeA.rootT (ξ : K) i j) := by
      rw [hwdef]
      exact uth_diagOf_single_sub ζ hij
    have hmat := congrArg (fun g : GL (Fin N) K => ((g : Matrix (Fin N) (Fin N) K))) hBD
    simp only [Units.val_mul] at hmat
    calc ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
          Matrix.diagonal (CFSG.StandardType.TypeA.rootT (ξ : K) i j)
        = (((B : GL (Fin N) K) * diagOf ζ w : GL (Fin N) K) :
            Matrix (Fin N) (Fin N) K) := by
          rw [← hDmat, Units.val_mul]
      _ = ((((diagOf ζ w' * Matrix.GeneralLinearGroup.scalar (Fin N) z) *
              (B : GL (Fin N) K)) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
          simpa only [Units.val_mul] using hmat
      _ = Matrix.diagonal
            (fun k => ((ζ (Multiplicative.ofAdd (w' k)) : Kˣ) : K) * ((z : Kˣ) : K)) *
            ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
          rw [Units.val_mul, Units.val_mul, coe_diagOf, Matrix.GeneralLinearGroup.coe_scalar,
            Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  obtain ⟨π, hπ⟩ := CFSG.StandardType.TypeA.exists_perm_mul_diagonal (ζ := (ξ : K)) hξval
    (B : GL (Fin N) K) hmono
  refine ⟨π, ?_, hπ⟩
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨w, hw, rfl⟩ := uth_exists_rep_heart x
  obtain ⟨w', hw', hw'eq⟩ :=
    uth_exists_rep_heart (φ ⟨(UnitRaw.oneLine N).mkQ w, hw⟩)
  have hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    diagOf_mem_normalizer ζ h w
  have hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    diagOf_mem_normalizer ζ h w'
  obtain ⟨z, hz⟩ :=
    uth_exists_scalar_mul_of_projConj_eq h hK hN (hproj w w' hD hD' hw hw' hw'eq)
  have hz' : (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ =
      diagOf ζ w' * Matrix.GeneralLinearGroup.scalar (Fin N) z := hz
  have hGL : (B : GL (Fin N) K) * diagOf ζ w =
      diagOf ζ (fun k => w (π k)) * (B : GL (Fin N) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagOf, coe_diagOf]
    have h := hπ (fun k => ((ζ (Multiplicative.ofAdd (w k)) : Kˣ) : K))
    rw [show (fun k => ((ζ (Multiplicative.ofAdd (w k)) : Kˣ) : K)) ∘ π =
      fun k => ((ζ (Multiplicative.ofAdd (w (π k))) : Kˣ) : K) from rfl] at h
    exact h
  have hBconjπ : (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ =
      diagOf ζ (fun k => w (π k)) := by
    calc (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹
        = (diagOf ζ (fun k => w (π k)) * (B : GL (Fin N) K)) *
            (B : GL (Fin N) K)⁻¹ := by rw [hGL]
      _ = diagOf ζ (fun k => w (π k)) := by group
  have hDconj : TableB.projConj (unitarySU 2 1 K N)
        ⟨diagOf ζ (fun k => w (π k)), diagOf_mem_normalizer ζ h _⟩ =
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ := by
    have hS : Matrix.GeneralLinearGroup.scalar (Fin N) z ∈ LargeEvenScalars (Fin N) K :=
      ⟨z, rfl⟩
    have hMeq : (⟨diagOf ζ (fun k => w (π k)), diagOf_mem_normalizer ζ h _⟩ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
        ⟨diagOf ζ w', hD'⟩ *
          ⟨Matrix.GeneralLinearGroup.scalar (Fin N) z, TableB.scalar_mem_normalizer _ hS⟩ := by
      apply Subtype.ext
      show diagOf ζ (fun k => w (π k)) =
        diagOf ζ w' * Matrix.GeneralLinearGroup.scalar (Fin N) z
      rw [← hBconjπ]
      exact hz'
    rw [hMeq, map_mul, TableB.projConj_of_scalar _ hS, mul_one]
  have hmk : (UnitRaw.oneLine N).mkQ (fun k => w (π k)) =
      (UnitRaw.oneLine N).mkQ w' :=
    (uth_projConj_diagOf_eq_iff ζ h hK hζ hN _ w'
      (diagOf_mem_normalizer ζ h _) hD').mp hDconj
  calc φ ⟨(UnitRaw.oneLine N).mkQ w, hw⟩ = ⟨(UnitRaw.oneLine N).mkQ w', hw'⟩ := hw'eq.symm
    _ = UnitRaw.permEquivH N π⁻¹ ⟨(UnitRaw.oneLine N).mkQ w, hw⟩ := by
        apply Subtype.ext
        rw [UnitRaw.coe_permEquivH, UnitRaw.permEquivQ_mk]
        show (UnitRaw.oneLine N).mkQ w' =
          (UnitRaw.oneLine N).mkQ (fun k => w ((π⁻¹).symm k))
        rw [Equiv.Perm.inv_def, Equiv.symm_symm]
        exact hmk.symm

theorem unitAmbientTorusAutH_holds : UnitAmbientTorusAutH := by
  intro K _ _ ζ N hK hζ hN h3N
  have h : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨y, -, hyreal⟩ := hφ
    obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin N) K).subgroupOf (unitarySU 2 1 K N)) y
    obtain ⟨π, hπeq, -⟩ := uth_exists_perm_of_realizes ζ h hK hζ (by omega) B φ hyreal
    rw [hπeq]
    exact uth_permEquivH_mem_ambientNormalizerH (N := N) π⁻¹
  · intro φ hφ
    refine uth_closure_subset_unitTorusAutH ζ h hK hζ (by omega) (X := ⊤) ?_ hφ
    rintro ψ ⟨i, j, rfl⟩
    exact uth_permEquivH_swap_mem_unitTorusAutH ζ h hK hζ (by omega)
      (i := i) (j := j) (Subgroup.mem_top _)

theorem unitComponentTorusAutH_holds : UnitComponentTorusAutH := by
  intro K _ _ ζ N hK hζ hN h3N S hS
  have h : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨y, hy, hyreal⟩ := hφ
    obtain ⟨B, hB, hBy⟩ := Subgroup.mem_map.mp hy
    rw [← hBy] at hyreal
    obtain ⟨π, hπeq, hπ⟩ := uth_exists_perm_of_realizes ζ h hK hζ (by omega) B φ hyreal
    have hfix : ∀ k, k ∉ S → π k = k := uth_fixes_of_blockSU hB hπ
    rw [hπeq]
    refine uth_permEquivH_mem_normalizerOfH (N := N) (S := S) ?_
    intro k hk
    rw [Equiv.Perm.inv_def]
    conv_lhs => rw [← hfix k hk]
    exact Equiv.symm_apply_apply π k
  · intro φ hφ
    refine uth_closure_subset_unitTorusAutH ζ h hK hζ (by omega) (X := blockPSU S) ?_ hφ
    rintro ψ ⟨i, hi, j, hj, rfl⟩
    refine uth_permEquivH_swap_mem_unitTorusAutH ζ h hK hζ (by omega) ?_
    refine Subgroup.mem_map.mpr ⟨LineU.permSU h (Equiv.swap i j), ?_, rfl⟩
    rw [TableBUE.mem_blockSU, LineU.coe_permSU]
    exact TableBUE.isBlockOn_permGL_swap hi hj

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement
