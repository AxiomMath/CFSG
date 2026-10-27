module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitNormalizerStatements
import CFSG.LocalAnalysis.StandardType.GGQ2UnitDiag
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeAMono
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInUniLift
import CFSG.Mathlib.Perm.FixingSubgroupSwap

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom det_diagHom coe_diagHom)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {N : ℕ} {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* Kˣ)

private theorem utf_projConj_eq_conj {B : ↥(unitarySU 2 1 K N)} :
    TableB.projConj (unitarySU 2 1 K N)
        ⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩ =
      MulAut.conj (LargeEvenProjMk (unitarySU 2 1 K N) B) := by
  rw [TableB.projConj_of_mem _ (B : GL (Fin N) K) B.2]
  rfl

private theorem utf_conj_mul_projConj {B : ↥(unitarySU 2 1 K N)}
    (A : Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) :
    MulAut.conj (LargeEvenProjMk (unitarySU 2 1 K N) B) * TableB.projConj _ A *
        (MulAut.conj (LargeEvenProjMk (unitarySU 2 1 K N) B))⁻¹ =
      TableB.projConj _
        (⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩ * A *
          ⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩⁻¹) := by
  rw [← utf_projConj_eq_conj (B := B), map_mul, map_mul, map_inv]

private theorem utf_projConj_diagOf_eq_of_mkQ_eq (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N) {w w' : UnitRaw.W N}
    (hw : (UnitRaw.oneLine N).mkQ w = (UnitRaw.oneLine N).mkQ w') :
    TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ =
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ :=
  (projConj_diagOf_eq_iff ζ h hK hζ hN w w').mpr hw

private theorem utf_one_mem_unitTorusAut (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N)
    (X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))) :
    (1 : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N) ∈ unitTorusAut ζ N X := by
  refine ⟨1, X.one_mem, ?_⟩
  intro w w' hD hD' hw
  have hcw : (⟨diagOf ζ w, hD⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ := Subtype.ext rfl
  have hcw' : (⟨diagOf ζ w', hD'⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ := Subtype.ext rfl
  rw [hcw, hcw']
  simpa using utf_projConj_diagOf_eq_of_mkQ_eq ζ h hK hζ hN (by simpa using hw.symm)

private theorem utf_mul_mem_unitTorusAut (h : UnitaryFieldData 2 1 K)
    {X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))}
    {φ ψ : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N}
    (hφ : φ ∈ unitTorusAut ζ N X) (hψ : ψ ∈ unitTorusAut ζ N X) :
    φ * ψ ∈ unitTorusAut ζ N X := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  obtain ⟨z, hz, hzψ⟩ := hψ
  refine ⟨y * z, X.mul_mem hy hz, ?_⟩
  intro w w' hD hD' hw
  obtain ⟨u, hu⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine N) (ψ ((UnitRaw.oneLine N).mkQ w))
  rw [LinearEquiv.mul_apply] at hw
  have h1 := hzψ w u (diagOf_mem_normalizer ζ h w) (diagOf_mem_normalizer ζ h u) hu
  have h2 := hyφ u w' (diagOf_mem_normalizer ζ h u) (diagOf_mem_normalizer ζ h w')
    (by rw [hu]; exact hw)
  have hcw : (⟨diagOf ζ w, hD⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ := Subtype.ext rfl
  have hcw' : (⟨diagOf ζ w', hD'⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ := Subtype.ext rfl
  rw [hcw, hcw']
  rw [show MulAut.conj (y * z) = MulAut.conj y * MulAut.conj z from map_mul _ y z]
  calc MulAut.conj y * MulAut.conj z *
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ *
        (MulAut.conj y * MulAut.conj z)⁻¹ =
      MulAut.conj y * (MulAut.conj z *
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ *
        (MulAut.conj z)⁻¹) * (MulAut.conj y)⁻¹ := by group
    _ = MulAut.conj y *
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ u, diagOf_mem_normalizer ζ h u⟩ *
        (MulAut.conj y)⁻¹ := by rw [h1]
    _ = TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ := h2

private theorem utf_inv_mem_unitTorusAut (h : UnitaryFieldData 2 1 K)
    {X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))}
    {φ : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N} (hφ : φ ∈ unitTorusAut ζ N X) :
    φ⁻¹ ∈ unitTorusAut ζ N X := by
  obtain ⟨y, hy, hyφ⟩ := hφ
  refine ⟨y⁻¹, X.inv_mem hy, ?_⟩
  intro w w' hD hD' hw
  have hcw : (⟨diagOf ζ w, hD⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ := Subtype.ext rfl
  have hcw' : (⟨diagOf ζ w', hD'⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ := Subtype.ext rfl
  rw [hcw, hcw']
  have h2 : (UnitRaw.oneLine N).mkQ w = φ ((UnitRaw.oneLine N).mkQ w') := by
    rw [hw]
    simp
  have h3 := hyφ w' w (diagOf_mem_normalizer ζ h w') (diagOf_mem_normalizer ζ h w) h2
  rw [show MulAut.conj y⁻¹ = (MulAut.conj y)⁻¹ from map_inv _ y, ← h3]
  group

private theorem utf_closure_subset_unitTorusAut (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N)
    {X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))}
    {T : Set (UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N)}
    (hT : T ⊆ unitTorusAut ζ N X) :
    ((Subgroup.closure T : Subgroup (UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N)) : Set _) ⊆
      unitTorusAut ζ N X := by
  intro φ hφ
  induction hφ using Subgroup.closure_induction with
  | mem x hx => exact hT hx
  | one => exact utf_one_mem_unitTorusAut ζ h hK hζ hN X
  | mul x y _ _ hx hy => exact utf_mul_mem_unitTorusAut ζ h hx hy
  | inv x _ hx => exact utf_inv_mem_unitTorusAut ζ h hx

private theorem utf_permGL_conj_diagOf (σ : Equiv.Perm (Fin N)) (w : UnitRaw.W N) :
    (CFSG.RankThree.Classical.permGL σ : GL (Fin N) K) * diagOf ζ w *
        ((CFSG.RankThree.Classical.permGL σ)⁻¹ : GL (Fin N) K) =
      diagOf ζ (fun i => w (σ.symm i)) := by
  have h := CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv (K := K) σ
    (fun i => ζ (Multiplicative.ofAdd (w i)))
  rw [show diagOf ζ w = diagHom N (fun i => ζ (Multiplicative.ofAdd (w i))) from rfl,
    show diagOf ζ (fun i => w (σ.symm i)) =
      diagHom N (fun i => ζ (Multiplicative.ofAdd (w (σ.symm i)))) from rfl, h]
  rfl

private theorem utf_permEquivQ_mem_unitTorusAut_of_conj (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N)
    {σ : Equiv.Perm (Fin N)} {B : ↥(unitarySU 2 1 K N)}
    (hB : (B : GL (Fin N) K) = CFSG.RankThree.Classical.permGL σ)
    {X : Subgroup (LargeEvenProj (unitarySU 2 1 K N))}
    (hy : LargeEvenProjMk (unitarySU 2 1 K N) B ∈ X) :
    UnitRaw.permEquivQ N σ ∈ unitTorusAut ζ N X := by
  refine ⟨LargeEvenProjMk (unitarySU 2 1 K N) B, hy, ?_⟩
  intro w w' hD hD' hw
  have hcw : (⟨diagOf ζ w, hD⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ := Subtype.ext rfl
  have hcw' : (⟨diagOf ζ w', hD'⟩ :
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ := Subtype.ext rfl
  rw [hcw, hcw', utf_conj_mul_projConj (B := B)]
  have hBeq : (⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩ *
        ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ *
        (⟨(B : GL (Fin N) K), Subgroup.le_normalizer B.2⟩)⁻¹ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ (fun i => w (σ.symm i)), diagOf_mem_normalizer ζ h _⟩ := by
    apply Subtype.ext
    show (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ =
      diagOf ζ (fun i => w (σ.symm i))
    rw [hB]
    exact utf_permGL_conj_diagOf ζ σ w
  rw [hBeq]
  refine utf_projConj_diagOf_eq_of_mkQ_eq ζ h hK hζ hN ?_
  rw [hw, UnitRaw.permEquivQ_mk]

private theorem utf_permGL_swap_mem_blockSU (h : UnitaryFieldData 2 1 K) {S : Finset (Fin N)}
    {i j : Fin N} (hi : i ∈ S) (hj : j ∈ S) :
    (⟨CFSG.RankThree.Classical.permGL (Equiv.swap i j), TableBUE.permGL_swap_mem h i j⟩ :
      ↥(unitarySU 2 1 K N)) ∈ TableBUE.blockSU S :=
  TableBUE.mem_blockSU.mpr (TableBUE.isBlockOn_permGL_swap hi hj)

private theorem utf_permEquivQ_swap_mem_blockPSU (h : UnitaryFieldData 2 1 K) {S : Finset (Fin N)}
    {i j : Fin N} (hi : i ∈ S) (hj : j ∈ S) :
    LargeEvenProjMk (unitarySU 2 1 K N)
        ⟨CFSG.RankThree.Classical.permGL (Equiv.swap i j), TableBUE.permGL_swap_mem h i j⟩ ∈
      blockPSU (K := K) (N := N) S :=
  Subgroup.mem_map.mpr ⟨_, utf_permGL_swap_mem_blockSU h hi hj, rfl⟩

private theorem utf_permEquivQ_swap_mem_unitTorusAut_top (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N) (i j : Fin N) :
    UnitRaw.permEquivQ N (Equiv.swap i j) ∈ unitTorusAut ζ N ⊤ :=
  utf_permEquivQ_mem_unitTorusAut_of_conj ζ h hK hζ hN (σ := Equiv.swap i j)
    (B := ⟨CFSG.RankThree.Classical.permGL (Equiv.swap i j), TableBUE.permGL_swap_mem h i j⟩)
    rfl (Subgroup.mem_top _)

private theorem utf_permEquivQ_swap_mem_unitTorusAut_block (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N) {S : Finset (Fin N)}
    {i j : Fin N} (hi : i ∈ S) (hj : j ∈ S) :
    UnitRaw.permEquivQ N (Equiv.swap i j) ∈ unitTorusAut ζ N (blockPSU (K := K) (N := N) S) :=
  utf_permEquivQ_mem_unitTorusAut_of_conj ζ h hK hζ hN (σ := Equiv.swap i j)
    (B := ⟨CFSG.RankThree.Classical.permGL (Equiv.swap i j), TableBUE.permGL_swap_mem h i j⟩)
    rfl (utf_permEquivQ_swap_mem_blockPSU h hi hj)


private def utfRealizes {K : Type} [Field K] (N : ℕ)
    (ζ : Multiplicative (ZMod 3) →* Kˣ) (B : ↥(unitarySU 2 1 K N))
    (φ : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N) : Prop :=
  ∀ (w w' : UnitRaw.W N)
    (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
    (hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))),
    (UnitRaw.oneLine N).mkQ w' = φ ((UnitRaw.oneLine N).mkQ w) →
      MulAut.conj (LargeEvenProjMk (unitarySU 2 1 K N) B) *
          TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ *
          (MulAut.conj (LargeEvenProjMk (unitarySU 2 1 K N) B))⁻¹ =
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩

private theorem utf_conj_diagOf_eq_scalar_mul {K : Type} [Field K] [Finite K] {N : ℕ}
    {h : UnitaryFieldData 2 1 K} {ζ : Multiplicative (ZMod 3) →* Kˣ} (hN : 5 ≤ N)
    {B : ↥(unitarySU 2 1 K N)}
    {φ : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N} (hB : utfRealizes N ζ B φ)
    (w : UnitRaw.W N) :
    ∃ (w' : UnitRaw.W N) (c : Kˣ),
      (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin N) c * diagOf ζ w' := by
  classical
  obtain ⟨w', hw'⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine N) (φ ((UnitRaw.oneLine N).mkQ w))
  have h1 := hB w w' (diagOf_mem_normalizer ζ h w) (diagOf_mem_normalizer ζ h w') hw'
  rw [utf_conj_mul_projConj (B := B)] at h1
  have hBn : (B : GL (Fin N) K) ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    (unitarySU 2 1 K N).le_normalizer B.2
  have hBinv : (B : GL (Fin N) K)⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    (Subgroup.normalizer _).inv_mem hBn
  have hDw : diagOf ζ w ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    diagOf_mem_normalizer ζ h w
  have hDw' : diagOf ζ w' ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    diagOf_mem_normalizer ζ h w'
  have hDw'inv : (diagOf ζ w')⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    (Subgroup.normalizer _).inv_mem hDw'
  have hMn : (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hBn hDw) hBinv
  have hMM : TableB.projConj (unitarySU 2 1 K N)
        ⟨(B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹, hMn⟩ =
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hDw'⟩ := by
    rw [← h1]
    exact congrArg (TableB.projConj (unitarySU 2 1 K N)) (Subtype.ext rfl)
  have hmem : (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ * (diagOf ζ w')⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    (Subgroup.normalizer _).mul_mem hMn hDw'inv
  have h2 : TableB.projConj (unitarySU 2 1 K N)
      ⟨(B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ * (diagOf ζ w')⁻¹, hmem⟩ = 1 := by
    have hprod : (⟨(B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ * (diagOf ζ w')⁻¹,
          hmem⟩ : Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
        (⟨(B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹, hMn⟩ :
          Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) *
        (⟨diagOf ζ w', hDw'⟩ :
          Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))⁻¹ := Subtype.ext rfl
    rw [hprod, map_mul, map_inv, hMM, mul_inv_cancel]
  have hscal := CFSG.LocalAnalysis.GLTheoremA.T171Sh.mem_scalars_of_projConj_eq_one
    (n := 1) (d := N) h (by omega)
    (by intro hc; have := congrArg Prod.fst hc; simp at this; omega) hmem h2
  obtain ⟨c, hc⟩ := hscal
  refine ⟨w', c, ?_⟩
  calc (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹
      = (B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹ * (diagOf ζ w')⁻¹ *
          diagOf ζ w' := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin N) c * diagOf ζ w' := by rw [hc.symm]

private theorem utf_ne_inv_of_pow_three {a : K} (h3 : a ^ 3 = 1) (h1 : a ≠ 1) : a ≠ a⁻¹ := by
  have h0 : a ≠ 0 := by
    rintro rfl
    simp at h3
  intro h
  apply h1
  have h2 : a * a = 1 := by
    nth_rewrite 2 [h]
    rw [mul_inv_cancel₀ h0]
  have e : a ^ 3 = a * (a * a) := by ring
  rw [h3, h2, mul_one] at e
  exact e.symm

private theorem utf_zeta_one_ne_one (hζ : Function.Injective ζ) :
    ((ζ (Multiplicative.ofAdd (1 : ZMod 3)) : Kˣ) : K) ≠ 1 := by
  intro h
  have hne : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 := by
    intro he
    exact one_ne_zero (congrArg Multiplicative.toAdd he)
  refine hne (hζ ?_)
  have h5 : (ζ (Multiplicative.ofAdd (1 : ZMod 3)) : Kˣ) = 1 := by
    refine Units.ext ?_
    simpa using h
  exact h5.trans (map_one ζ).symm

private theorem utf_zeta_one_ne_inv (hζ : Function.Injective ζ) :
    ((ζ (Multiplicative.ofAdd (1 : ZMod 3)) : Kˣ) : K) ≠
      (((ζ (Multiplicative.ofAdd (1 : ZMod 3)) : Kˣ) : K))⁻¹ :=
  utf_ne_inv_of_pow_three
    (a := ((ζ (Multiplicative.ofAdd (1 : ZMod 3)) : Kˣ) : K))
    (by
      have h := congrArg (fun u : Kˣ => (u : K)) (zeta_pow_three ζ (Multiplicative.ofAdd 1))
      simpa [Units.val_pow_eq_pow_val] using h)
    (utf_zeta_one_ne_one ζ hζ)

private theorem utf_exists_perm_mul_diagonal {K : Type} [Field K] [Finite K] {N : ℕ}
    {h : UnitaryFieldData 2 1 K} {ζ : Multiplicative (ZMod 3) →* Kˣ} (hK : Nat.card K = 4)
    (hζ : Function.Injective ζ) (hN : 5 ≤ N) {B : ↥(unitarySU 2 1 K N)}
    {φ : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N} (hB : utfRealizes N ζ B φ) :
    ∃ π : Equiv.Perm (Fin N), ∀ u : Fin N → K,
      (B : GL (Fin N) K) * Matrix.diagonal u =
        Matrix.diagonal (u ∘ ⇑π) * (B : GL (Fin N) K) := by
  classical
  set ζ₀ : Kˣ := ζ (Multiplicative.ofAdd (1 : ZMod 3)) with hζ₀def
  have hsurj : Function.Surjective ⇑ζ := zeta_surjective ζ hK hζ
  have hmono : ∀ i j : Fin N, i ≠ j → ∃ D : Fin N → K,
      (B : GL (Fin N) K) * Matrix.diagonal (TypeA.rootT (ζ₀ : K) i j) =
        Matrix.diagonal D * (B : GL (Fin N) K) := by
    intro i j hij
    set d : Fin N → Kˣ :=
      fun k => if k = i then ζ₀ else if k = j then ζ₀⁻¹ else 1 with hddef
    choose x hx using fun k => hsurj (d k)
    set w : UnitRaw.W N := fun k => Multiplicative.toAdd (x k) with hwdef
    obtain ⟨w', c, hc⟩ := utf_conj_diagOf_eq_scalar_mul (h := h) hN hB w
    have hdm : diagOf ζ w = diagHom N d := by
      apply Units.ext
      rw [coe_diagOf, coe_diagHom]
      congr 1
      funext k
      simpa [w] using congrArg (fun u : Kˣ => (u : K)) (hx k)
    have hdv : ∀ k, ((d k : Kˣ) : K) = TypeA.rootT (ζ₀ : K) i j k := by
      intro k
      by_cases hki : k = i
      · subst hki
        simp [d, TypeA.rootT]
      · by_cases hkj : k = j
        · subst hkj
          simp [d, TypeA.rootT, hki]
        · simp [d, TypeA.rootT, hki, hkj]
    refine ⟨fun k => (c : K) * ((ζ (Multiplicative.ofAdd (w' k)) : Kˣ) : K), ?_⟩
    have h1 : (B : GL (Fin N) K) * diagOf ζ w =
        Matrix.GeneralLinearGroup.scalar (Fin N) c * diagOf ζ w' * (B : GL (Fin N) K) := by
      rw [← hc]
      group
    have h2 := congrArg (fun g : GL (Fin N) K => ((g : Matrix (Fin N) (Fin N) K))) h1
    simp only [Units.val_mul] at h2
    rw [hdm, coe_diagHom, coe_diagOf, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] at h2
    rwa [show (fun k => ((d k : Kˣ) : K)) = TypeA.rootT (ζ₀ : K) i j from funext hdv] at h2
  exact TypeA.exists_perm_mul_diagonal (utf_zeta_one_ne_inv ζ hζ) (B : GL (Fin N) K) hmono

private theorem utf_permEquivQ_mul (N : ℕ) (σ τ : Equiv.Perm (Fin N)) :
    UnitRaw.permEquivQ N (σ * τ) = UnitRaw.permEquivQ N σ * UnitRaw.permEquivQ N τ := by
  refine LinearEquiv.ext fun v => ?_
  induction v using Submodule.Quotient.induction_on with
  | H w =>
    change UnitRaw.permEquivQ N (σ * τ) ((UnitRaw.oneLine N).mkQ w) =
      UnitRaw.permEquivQ N σ (UnitRaw.permEquivQ N τ ((UnitRaw.oneLine N).mkQ w))
    rw [UnitRaw.permEquivQ_mk, UnitRaw.permEquivQ_mk, UnitRaw.permEquivQ_mk]
    simp [Equiv.Perm.mul_def]

private theorem utf_permEquivQ_one (N : ℕ) : UnitRaw.permEquivQ N 1 = 1 := by
  have h : UnitRaw.permEquivQ N 1 * UnitRaw.permEquivQ N 1 = UnitRaw.permEquivQ N 1 := by
    rw [← utf_permEquivQ_mul, one_mul]
  have h2 := congrArg (fun e : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N =>
    e * (UnitRaw.permEquivQ N 1)⁻¹) h
  simpa using h2

private theorem utf_permEquivQ_inv (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    UnitRaw.permEquivQ N σ⁻¹ = (UnitRaw.permEquivQ N σ)⁻¹ := by
  have h : UnitRaw.permEquivQ N σ * UnitRaw.permEquivQ N σ⁻¹ = 1 := by
    rw [← utf_permEquivQ_mul, mul_inv_cancel, utf_permEquivQ_one]
  exact eq_inv_of_mul_eq_one_right h

private theorem utf_permEquivQ_mem_ambientNormalizer (N : ℕ) (π : Equiv.Perm (Fin N)) :
    UnitRaw.permEquivQ N π ∈ UnitRaw.ambientNormalizer N := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => rw [utf_permEquivQ_one]; exact Subgroup.one_mem _
  | swap_mul f x y _ ih =>
    rw [utf_permEquivQ_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨x, y, rfl⟩) ih

private theorem utf_permEquivQ_mem_normalizerOf {N : ℕ} {S : Finset (Fin N)}
    {π : Equiv.Perm (Fin N)} (hfix : ∀ k, k ∉ S → π k = k) :
    UnitRaw.permEquivQ N π ∈ UnitRaw.normalizerOf S := by
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
  have key : ∀ σ ∈ Subgroup.closure T,
      UnitRaw.permEquivQ N σ ∈ UnitRaw.normalizerOf S := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, j, hj, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨i, hi, j, hj, rfl⟩
    | one => rw [utf_permEquivQ_one]; exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [utf_permEquivQ_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [utf_permEquivQ_inv]; exact Subgroup.inv_mem _ hx
  exact key π hπ

private theorem utf_projConj_diagOf_eq_iff (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 4 ≤ N) (w w' : UnitRaw.W N)
    (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
    (hD' : diagOf ζ w' ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) :
    TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ =
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ ↔
      (UnitRaw.oneLine N).mkQ w = (UnitRaw.oneLine N).mkQ w' := by
  rw [show (⟨diagOf ζ w, hD⟩ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w, diagOf_mem_normalizer ζ h w⟩ from Subtype.ext rfl,
    show (⟨diagOf ζ w', hD'⟩ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
      ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ from Subtype.ext rfl]
  exact projConj_diagOf_eq_iff ζ h hK hζ hN w w'

private theorem utf_mem_scalars_of_projConj_eq_one (h : UnitaryFieldData 2 1 K) [Finite K]
    (hN : 4 ≤ N)
    {M : Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))}
    (hM : TableB.projConj (unitarySU 2 1 K N) M = 1) :
    (M : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K := by
  have hdq : (N, 2 ^ 1) ≠ (3, 2) := by
    intro he
    have hN3 : N = 3 := by simpa using congrArg Prod.fst he
    omega
  exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.mem_scalars_of_projConj_eq_one (n := 1) (d := N)
    h (by omega) hdq M.2 hM

private theorem utf_exists_scalar_mul_of_projConj_eq (h : UnitaryFieldData 2 1 K) [Finite K]
    (hN : 4 ≤ N)
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
    utf_mem_scalars_of_projConj_eq_one h hN h1
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

private theorem utf_fixes_of_blockSU {S : Finset (Fin N)} {B : ↥(unitarySU 2 1 K N)}
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
  have hu2 : u k = 0 := by rw [hu]; exact Pi.single_eq_of_ne (M := fun _ => K) (Ne.symm hne) 1
  have h := congrFun (congrFun (hπ u) k) k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  simp only [Function.comp_apply] at h
  rw [hu1, hu2, mul_zero, one_mul, hBk] at h
  exact zero_ne_one h


private theorem utf_exists_perm_of_realizes (h : UnitaryFieldData 2 1 K) [Finite K]
    (hK : Nat.card K = 4) (hζ : Function.Injective ζ) (hN : 5 ≤ N)
    {B : ↥(unitarySU 2 1 K N)} {φ : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N}
    (hB : utfRealizes N ζ B φ) :
    ∃ π : Equiv.Perm (Fin N), φ = UnitRaw.permEquivQ N π⁻¹ ∧
      ∀ u : Fin N → K,
        (B : GL (Fin N) K) * Matrix.diagonal u =
          Matrix.diagonal (u ∘ ⇑π) * (B : GL (Fin N) K) := by
  classical
  obtain ⟨π, hπ⟩ := utf_exists_perm_mul_diagonal (h := h) hK hζ hN hB
  have hproj : ∀ (w w' : UnitRaw.W N), (UnitRaw.oneLine N).mkQ w' = φ ((UnitRaw.oneLine N).mkQ w) →
      TableB.projConj (unitarySU 2 1 K N)
        ⟨(B : GL (Fin N) K) * diagOf ζ w * (B : GL (Fin N) K)⁻¹,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer B.2)
            (diagOf_mem_normalizer ζ h w))
          (Subgroup.inv_mem _ (Subgroup.le_normalizer B.2))⟩ =
      TableB.projConj (unitarySU 2 1 K N)
        ⟨diagOf ζ w', diagOf_mem_normalizer ζ h w'⟩ := by
    intro w w' hw
    have h1 := hB w w' (diagOf_mem_normalizer ζ h w) (diagOf_mem_normalizer ζ h w') hw
    rw [utf_conj_mul_projConj (B := B)] at h1
    exact (congrArg (TableB.projConj (unitarySU 2 1 K N)) (Subtype.ext rfl)).trans h1
  refine ⟨π, ?_, hπ⟩
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine N) x
  obtain ⟨w', hw'⟩ := Submodule.mkQ_surjective (UnitRaw.oneLine N)
    (φ ((UnitRaw.oneLine N).mkQ w))
  have hD' : diagOf ζ w' ∈
      Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)) :=
    diagOf_mem_normalizer ζ h w'
  obtain ⟨z, hz⟩ := utf_exists_scalar_mul_of_projConj_eq (h := h) (by omega)
    (hproj w w' hw')
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
    rw [hGL]
    group
  have hDconj : TableB.projConj (unitarySU 2 1 K N)
        ⟨diagOf ζ (fun k => w (π k)), diagOf_mem_normalizer ζ h _⟩ =
      TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w', hD'⟩ := by
    have hS : Matrix.GeneralLinearGroup.scalar (Fin N) z ∈ LargeEvenScalars (Fin N) K :=
      ⟨z, rfl⟩
    have hMeq : (⟨diagOf ζ (fun k => w (π k)), diagOf_mem_normalizer ζ h _⟩ :
        Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K))) =
        (⟨diagOf ζ w', hD'⟩ : Subgroup.normalizer
            (unitarySU 2 1 K N : Set (GL (Fin N) K))) *
          ⟨Matrix.GeneralLinearGroup.scalar (Fin N) z,
            TableB.scalar_mem_normalizer _ hS⟩ := by
      apply Subtype.ext
      show diagOf ζ (fun k => w (π k)) =
        diagOf ζ w' * Matrix.GeneralLinearGroup.scalar (Fin N) z
      rw [← hBconjπ]
      exact hz
    rw [hMeq, map_mul, TableB.projConj_of_scalar _ hS, mul_one]
  have hmk : (UnitRaw.oneLine N).mkQ (fun k => w (π k)) = (UnitRaw.oneLine N).mkQ w' :=
    (utf_projConj_diagOf_eq_iff ζ h hK hζ (by omega) _ w'
      (diagOf_mem_normalizer ζ h _) hD').mp hDconj
  calc φ ((UnitRaw.oneLine N).mkQ w) = (UnitRaw.oneLine N).mkQ w' := hw'.symm
    _ = UnitRaw.permEquivQ N π⁻¹ ((UnitRaw.oneLine N).mkQ w) := by
        rw [UnitRaw.permEquivQ_mk]
        show (UnitRaw.oneLine N).mkQ w' =
          (UnitRaw.oneLine N).mkQ (fun k => w ((π⁻¹).symm k))
        rw [Equiv.Perm.inv_def, Equiv.symm_symm]
        exact hmk.symm

theorem unitAmbientTorusAut_holds : UnitAmbientTorusAut := by
  intro K _ _ ζ N hK hζ hN
  have h : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨y, -, hyreal⟩ := hφ
    obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin N) K).subgroupOf (unitarySU 2 1 K N)) y
    obtain ⟨π, hπeq, -⟩ := utf_exists_perm_of_realizes (B := B) (φ := φ) ζ h hK hζ hN hyreal
    rw [hπeq]
    exact utf_permEquivQ_mem_ambientNormalizer N π⁻¹
  · intro φ hφ
    refine utf_closure_subset_unitTorusAut ζ h hK hζ (by omega) (X := ⊤) ?_ hφ
    rintro ψ ⟨i, j, rfl⟩
    exact utf_permEquivQ_swap_mem_unitTorusAut_top ζ h hK hζ (by omega) i j

theorem unitComponentTorusAut_holds : UnitComponentTorusAut := by
  intro K _ _ ζ N hK hζ hN S _
  have h : UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card (by rw [hK]; norm_num) le_rfl
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨y, hy, hyreal⟩ := hφ
    obtain ⟨B, hB, hBy⟩ := Subgroup.mem_map.mp hy
    rw [← hBy] at hyreal
    obtain ⟨π, hπeq, hπ⟩ := utf_exists_perm_of_realizes (B := B) (φ := φ) ζ h hK hζ hN hyreal
    have hfix : ∀ k, k ∉ S → π k = k := utf_fixes_of_blockSU hB hπ
    rw [hπeq]
    refine utf_permEquivQ_mem_normalizerOf (N := N) (S := S) ?_
    intro k hk
    rw [Equiv.Perm.inv_def]
    conv_lhs => rw [← hfix k hk]
    exact Equiv.symm_apply_apply π k
  · intro φ hφ
    refine utf_closure_subset_unitTorusAut ζ h hK hζ (by omega)
      (X := blockPSU (K := K) (N := N) S) ?_ hφ
    rintro ψ ⟨i, hi, j, hj, rfl⟩
    exact utf_permEquivQ_swap_mem_unitTorusAut_block ζ h hK hζ (by omega) hi hj


end

end CFSG.StandardType.GGQ2Frame.UnitPlacement
