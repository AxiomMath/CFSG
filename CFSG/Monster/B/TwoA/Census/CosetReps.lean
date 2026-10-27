module

public import CFSG.Monster.B.TwoA.Census.MonoClasses
public import CFSG.Monster.Visible.Kernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.Spin
  CFSG.Monster.Griess
open scoped Pointwise

@[expose] def cosetCode
    (i : ℕ) : C := ⟨monoWord i, monoWord_mem i⟩

@[expose] def cosetPair
    (i : ℕ) : Pvis :=
  ⟨(YU ⟨cosetCode i, 0⟩, gO (cosetCode i)) *
      (sU (seedAut (monoSeed.getD i 0)), PO (seedAut (monoSeed.getD i 0))),
    Pvis.mul_mem (YU_gO_mem_Pvis _) (sU_PO_mem_Pvis _)⟩

@[expose] def cosetRep
    (i : ℕ) : Gvis := ⟨thetaEquiv (cosetPair i), thetaEquiv_mem_Gvis _⟩

@[expose] def cosetR
    (i : ℕ) : Set Gvis :=
  cosetRep i • ((rhoQ.subgroupOf Gvis : Subgroup Gvis) : Set Gvis)

theorem coe_cosetPair
    (i : ℕ) : (cosetPair i : GL SpinIdx ℚ × latticeO) =
    (YU ⟨cosetCode i, 0⟩ * sU (seedAut (monoSeed.getD i 0)), monoAO i) := rfl

theorem coe_cosetRep
    (i : ℕ) : (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) = thetaEquiv (cosetPair i) :=
  rfl

theorem piVis_cosetRep (i : ℕ) :
    piVis (cosetRep i) = MulOpposite.op (QuotientGroup.mk (monoAO i)) :=
  piVis_thetaEquiv (cosetPair i)

theorem mk_monoAO_eq_one_iff (i : ℕ) :
    (QuotientGroup.mk (monoAO i) : latticeO ⧸ Subgroup.zpowers negOneO) = 1 ↔ monoN i = 1 := by
  rw [QuotientGroup.eq_one_iff, mem_zpowers_negOneO_iff, monoN, modTwoUnit_eq_one_iff]

theorem mk_monoAO_sq
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 7) :
    (QuotientGroup.mk (monoAO i * monoAO i) : latticeO ⧸ Subgroup.zpowers negOneO) = 1 := by
  rw [QuotientGroup.eq_one_iff, mem_zpowers_negOneO_iff, ← modTwoUnit_eq_one_iff,
    modTwoUnit_mul]
  exact (monomial_involution_classes.2.2.2.2.2.2.1 i hi1 hi).2

theorem cosetRep_sq_mem
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 7) :
    ((cosetRep i * cosetRep i : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ := by
  refine mem_rhoQ_of_piVis_eq_one ?_
  rw [map_mul, piVis_cosetRep, ← MulOpposite.op_mul, ← QuotientGroup.mk_mul, mk_monoAO_sq hi1 hi,
    MulOpposite.op_one]

theorem cosetRep_not_mem
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 7) :
    ((cosetRep i : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) ∉ rhoQ := by
  intro h
  have h1 : piVis (cosetRep i) = 1 := by
    rw [← MonoidHom.mem_ker, ker_piVis, Subgroup.mem_subgroupOf]
    exact h
  rw [piVis_cosetRep, MulOpposite.op_eq_one_iff, mk_monoAO_eq_one_iff] at h1
  exact (monomial_involution_classes.2.2.2.2.2.2.1 i hi1 hi).1 h1

theorem mem_cosetR_iff
    (i : ℕ) (f : Gvis) : f ∈ cosetR i ↔ piVis f = piVis (cosetRep i) := by
  rw [cosetR, mem_leftCoset_iff, SetLike.mem_coe, ← ker_piVis, MonoidHom.mem_ker, map_mul,
    map_inv, inv_mul_eq_one, eq_comm]

theorem mem_cosetR_iff_exists
    (i : ℕ) (f : Gvis) :
    f ∈ cosetR i ↔ ∃ r : Q, (f : SpaceB ≃ₗ[ℚ] SpaceB) = cosetRep i * rhoEquiv r := by
  rw [cosetR, mem_leftCoset_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_rhoQ]
  refine ⟨fun ⟨r, hr⟩ => ⟨r, ?_⟩, fun ⟨r, hr⟩ => ⟨r, ?_⟩⟩
  · rw [hr, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, hr, inv_mul_cancel_left]

theorem visible_involution_coset_representatives_data :
    ∀ i ∈ ({1, 2, 6} : Finset ℕ),
      ((cosetCode i : C) : Fin 24 → ZMod 2) = bvec 24 (monoSign.getD i 0) ∧
      (seedAut (monoSeed.getD i 0) : Equiv.Perm (Fin 24)) = decode (seedA (monoSeed.getD i 0)) ∧
      (YU ⟨cosetCode i, 0⟩, gO (cosetCode i)) ∈ Pvis ∧
      (sU (seedAut (monoSeed.getD i 0)), PO (seedAut (monoSeed.getD i 0))) ∈ Pvis ∧
      (cosetPair i : GL SpinIdx ℚ × latticeO) =
        (YU ⟨cosetCode i, 0⟩ * sU (seedAut (monoSeed.getD i 0)), monoAO i) ∧
      monoAO i = gO (cosetCode i) * PO (seedAut (monoSeed.getD i 0)) ∧
      mat (monoAO i) = monoA i ∧
      (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) = thetaEquiv (cosetPair i) ∧
      piVis (cosetRep i) = MulOpposite.op (QuotientGroup.mk (monoAO i)) ∧
      ((cosetRep i * cosetRep i : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ rhoQ ∧
      ((cosetRep i : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) ∉ rhoQ ∧
      (∀ f : Gvis, f ∈ cosetR i ↔
        ∃ r : Q, (f : SpaceB ≃ₗ[ℚ] SpaceB) = cosetRep i * rhoEquiv r) ∧
      (∀ f : Gvis, f ∈ cosetR i ↔ piVis f = piVis (cosetRep i)) := by
  intro i hi
  have hi' : 1 ≤ i ∧ i < 7 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  exact ⟨rfl, coe_seedAut_eq (monoSeed_lt i), YU_gO_mem_Pvis _, sU_PO_mem_Pvis _, rfl, rfl,
    mat_monoAO i, rfl, piVis_cosetRep i, cosetRep_sq_mem hi'.1 hi'.2,
    cosetRep_not_mem hi'.1 hi'.2, mem_cosetR_iff_exists i, mem_cosetR_iff i⟩

end CFSG.Monster.B.TwoA.Census
