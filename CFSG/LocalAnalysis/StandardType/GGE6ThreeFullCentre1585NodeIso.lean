module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585NodeDefs

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem coker_equiv_nodeCoker
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    Nonempty (((Fin ρ.tau.rank → ℤ) ⧸ (kernelLattice ρ ⊔ frobDefect ρ)) ≃+
      nodeCoker ρ.row ρ.epsilon ((2 ^ lab.n : ℕ) : ℤ)) := by
  classical
  let N : Type := Fin ρ.row.diagram.marks.length → ℤ
  let Λ : Type := Fin ρ.tau.rank → ℤ
  let ε : ℤ := ρ.epsilon
  let q : ℤ := ((2 ^ lab.n : ℕ) : ℤ)
  let W : Submodule ℤ N := nodeSub ρ.row ε q
  let p : Submodule ℤ Λ := Submodule.map ρ.nodeMap W

  have hperm : ∀ i : Fin ρ.row.diagram.marks.length,
      nodePermMap ρ.row (Pi.single i 1) = Pi.single (ρ.row.nodePerm i) 1 := by
    intro i
    ext j
    simp [nodePermMap, LinearMap.funLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]

  have hcomm_basis : ∀ i : Fin ρ.row.diagram.marks.length,
      ρ.frobLinear.toLinearMap (ρ.nodeMap (Pi.single i 1)) =
        ρ.nodeMap (ε • nodePermMap ρ.row (Pi.single i 1)) := by
    intro i
    rw [show ρ.frobLinear.toLinearMap (ρ.nodeMap (Pi.single i 1)) =
        ρ.frobLinear (ρ.nodeMap (Pi.single i 1)) from rfl]
    rw [ρ.frob_nodes i, hperm i]
    simpa only [map_smul, ε]

  have hcomm_single : ∀ (i : Fin ρ.row.diagram.marks.length) (x : ℤ),
      ρ.frobLinear.toLinearMap (ρ.nodeMap (Pi.single i x)) =
        ρ.nodeMap (ε • nodePermMap ρ.row (Pi.single i x)) := by
    intro i x
    have hx : (Pi.single i x : N) = x • (Pi.single i 1 : N) := by
      ext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    rw [hx]
    simp only [map_smul, smul_smul]
    rw [hcomm_basis i, hperm i]
    simp only [map_smul, smul_smul]
    rw [mul_comm]

  have hcomm : ρ.frobLinear.toLinearMap.comp ρ.nodeMap =
      ρ.nodeMap.comp (ε • nodePermMap ρ.row) := by
    refine LinearMap.pi_ext ?_
    intro i x
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using hcomm_single i x

  have hmarks : ρ.nodeMap (nodeMarks ρ.row) = 0 := by
    have hmem : nodeMarks ρ.row ∈ ρ.nodeMap.ker := by
      rw [ρ.nodeMap_ker]
      exact Submodule.mem_span_singleton_self _
    exact (LinearMap.mem_ker).mp hmem

  have hmapMarks : Submodule.map ρ.nodeMap (Submodule.span ℤ {nodeMarks ρ.row}) = ⊥ := by
    rw [Submodule.map_span]
    simp [hmarks]

  have hK : Submodule.map ρ.nodeMap (zeroNodeLattice ρ.row) = kernelLattice ρ := by
    rw [kernelLattice, zeroNodeLattice, ρ.kernel_span_eq, Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨x, ⟨i, hi, hx⟩, hxv⟩
      subst hx
      exact ⟨i, hi, hxv.symm⟩
    · rintro ⟨i, hi, hxv⟩
      exact ⟨Pi.single i 1, ⟨i, hi, rfl⟩, hxv.symm⟩

  have hmapRange : ∀ A : N →ₗ[ℤ] N,
      Submodule.map ρ.nodeMap (LinearMap.range A) = LinearMap.range (ρ.nodeMap.comp A) := by
    intro A
    ext v
    constructor
    · intro hv
      rw [Submodule.mem_map] at hv
      obtain ⟨y, hy, hvy⟩ := hv
      rw [LinearMap.mem_range] at hy
      obtain ⟨z, hz⟩ := hy
      rw [LinearMap.mem_range]
      exact ⟨z, by simpa [LinearMap.comp_apply, hz, hvy]⟩
    · intro hv
      rw [LinearMap.mem_range] at hv
      obtain ⟨z, hz⟩ := hv
      rw [Submodule.mem_map]
      exact ⟨A z, ⟨z, rfl⟩, hz⟩

  have hcomp : ρ.nodeMap.comp (ε • nodePermMap ρ.row - q • LinearMap.id) =
      (ρ.frobLinear.toLinearMap - q • LinearMap.id).comp ρ.nodeMap := by
    refine LinearMap.pi_ext ?_
    intro i x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [map_sub, map_smul, map_smul, hcomm_single i x]
    simp only [map_smul]

  have hrange_comp : LinearMap.range
      ((ρ.frobLinear.toLinearMap - q • LinearMap.id).comp ρ.nodeMap) =
      LinearMap.range (ρ.frobLinear.toLinearMap - q • LinearMap.id) := by
    ext v
    constructor
    · intro hv
      rw [LinearMap.mem_range] at hv ⊢
      obtain ⟨x, hx⟩ := hv
      exact ⟨ρ.nodeMap x, by simpa [LinearMap.comp_apply] using hx⟩
    · intro hv
      rw [LinearMap.mem_range] at hv ⊢
      obtain ⟨y, hy⟩ := hv
      obtain ⟨x, hx⟩ := ρ.nodeMap_surj y
      exact ⟨x, by simpa [LinearMap.comp_apply, hx] using hy⟩

  have hmapDefect : Submodule.map ρ.nodeMap (nodeDefect ρ.row ε q) = frobDefect ρ := by
    rw [nodeDefect, frobDefect]
    have hmapRangeA := hmapRange (ε • nodePermMap ρ.row - q • LinearMap.id)
    rw [hmapRangeA, hcomp, hrange_comp]

  have hmapSub : Submodule.map ρ.nodeMap W = kernelLattice ρ ⊔ frobDefect ρ := by
    change Submodule.map ρ.nodeMap (nodeSub ρ.row ε q) = kernelLattice ρ ⊔ frobDefect ρ
    rw [nodeSub]
    rw [Submodule.map_sup]
    rw [Submodule.map_sup]
    rw [hmapMarks, hK, hmapDefect]
    simp

  have hker_le_W : LinearMap.ker ρ.nodeMap ≤ W := by
    rw [ρ.nodeMap_ker]
    rw [show W = nodeSub ρ.row ε q from rfl]
    rw [nodeSub]
    exact le_sup_left.trans le_sup_left

  let g : N →ₗ[ℤ] (Λ ⧸ p) := (Submodule.mkQ p).comp ρ.nodeMap

  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective p y
    obtain ⟨v, hv⟩ := ρ.nodeMap_surj x
    refine ⟨v, ?_⟩
    simp [g, hv, hx]

  have hker : LinearMap.ker g = W := by
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      have hx' : (Submodule.mkQ p) (ρ.nodeMap x) = 0 := by
        simpa [g, LinearMap.comp_apply] using hx
      have hmem : ρ.nodeMap x ∈ p := (Submodule.Quotient.mk_eq_zero p).mp hx'
      have hmem' : x ∈ Submodule.comap ρ.nodeMap (Submodule.map ρ.nodeMap W) := by
        rw [Submodule.mem_comap]
        exact hmem
      rw [Submodule.comap_map_eq] at hmem'
      rwa [sup_eq_left.mpr hker_le_W] at hmem'
    · intro hx
      rw [LinearMap.mem_ker]
      have hmem : ρ.nodeMap x ∈ Submodule.map ρ.nodeMap W := by
        rw [Submodule.mem_map]
        exact ⟨x, hx, rfl⟩
      have hzero : (Submodule.mkQ p) (ρ.nodeMap x) = 0 := (Submodule.Quotient.mk_eq_zero p).mpr hmem
      simpa [g, LinearMap.comp_apply] using hzero

  have e : (Λ ⧸ p) ≃ₗ[ℤ] (N ⧸ W) :=
    (LinearMap.quotKerEquivOfSurjective g hg).symm.trans
      (Submodule.quotEquivOfEq (LinearMap.ker g) W hker)
  refine ⟨?_⟩
  simpa [W, ε, q, nodeCoker] using
    ((Submodule.quotEquivOfEq (kernelLattice ρ ⊔ frobDefect ρ) p hmapSub.symm).trans e).toAddEquiv

end CFSG.StandardType.E6Centralizer1585

end
