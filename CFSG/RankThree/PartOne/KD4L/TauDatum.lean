module

public import CFSG.RankThree.PartOne.KD4L.GenAdjacent
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenComponents
import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.RankThree.Chevalley.SteinbergBID4Restrict

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Chevalley
open CFSG.LieType.AlgebraicGroups

section Aux

theorem isAlgebraic_zmod_of_isAlgClosure' (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K]
    [CharP K p] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p] :
    letI := ZMod.algebra L p; Algebra.IsAlgebraic (ZMod p) L :=
  CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := K)


@[expose] def d4Aux : E6EvenFixedRootDatum (AlgebraicClosure (ZMod 2)) :=
  have hJ := (gammaStable_iff_mem_e6QpSupport (e6QpSupport 14)).2 ⟨14, rfl⟩
  have hi : (1 : Fin Tag.E6.rank) ∈ e6QpSupport 14 := by
    change (1 : Fin Tag.E6.rank) ∈ e6QpSupportList 14
    decide
  ⟨isAlgebraic_zmod_of_isAlgClosure' 2 (ZMod 2) (AlgebraicClosure (ZMod 2)), 2, le_rfl, e6QpSupport 14, hJ.1, hJ.2, 1, hi,
    (e6XiOrth_or_e6Supp24 14 hi).resolve_right fun h => by
      have := h.1
      omega⟩

@[expose] def d4Gen : GenFixedRootDatum Tag.E6 2 (AlgebraicClosure (ZMod 2))
    (Multiplicative (Fin Tag.E6.rank → ℤ)) :=
  d4Aux.gen

theorem e6QpSupport_eq_iff_fourteen (m : Fin 15) (h : e6QpSupport m = e6QpSupport 14) : m = 14 := by
  have h' : ∀ i : Fin Tag.E6.rank, i ∈ e6QpSupportList m ↔ i ∈ e6QpSupportList 14 := fun i =>
    Set.ext_iff.1 h i
  revert h'
  fin_cases m <;> decide

theorem d4Aux_qpIndex : d4Aux.qpIndex = 14 :=
  e6QpSupport_eq_iff_fourteen _ (d4Aux.J_eq.symm.trans rfl)

@[expose] def gam : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

theorem d4Gen_theta_toReal {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ kernelRoots d4Gen.χ) :
    d4Gen.θ (toReal α) = toReal (permLattice (τ := Tag.E6) gam α) := by
  have hΞ : α ∈ parabolicRoots Tag.E6 d4Aux.support := by
    rw [← d4Aux.Ξ_eq_parabolicRoots, ← d4Aux.kernelRoots_chi]
    exact hα
  have hsupp : ∀ i, i ∉ e6QpSupport 14 → α i = 0 := fun i hi =>
    hΞ.2 i fun hs => hi (d4Aux_qpIndex ▸ d4Aux.support_subset hs)
  change d4Aux.theta (toReal α) = _
  rw [d4Aux.theta_toReal, d4Aux.δ_eq, d4Aux_qpIndex,
    e6Delta_eq_permLattice 14 (hx := hsupp)]
  congr 1
  ext j
  have h0 : α 0 = 0 := hsupp 0 (by
    change ¬ (0 : Fin Tag.E6.rank) ∈ e6QpSupportList 14
    decide)
  have h5 : α 5 = 0 := hsupp 5 (by
    change ¬ (5 : Fin Tag.E6.rank) ∈ e6QpSupportList 14
    decide)
  have hA : ∀ j : Fin 6, (Equiv.swap (2 : Fin 6) 4).symm j = ![0, 1, 4, 3, 2, 5] j := by
    intro j
    fin_cases j <;> decide
  have hB : ∀ j : Fin 6,
      ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm) j = ![5, 1, 4, 3, 2, 0] j := by
    intro j
    fin_cases j <;> decide
  show α ((Equiv.swap (2 : Fin 6) 4).symm j) =
    α (((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm) j)
  rw [hA j, hB j]
  fin_cases j
  · exact h0.trans h5.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h5.trans h0.symm

theorem reflTransGen_one (j : Fin Tag.E6.rank) (h0 : j ≠ 0) (h5 : j ≠ 5) :
    Relation.ReflTransGen (e6JAdj (e6QpSupport 14)) 1 j := by
  have a13 : e6JAdj (e6QpSupport 14) 1 3 := by
    change (1 : Fin Tag.E6.rank) ∈ e6QpSupportList 14 ∧ (3 : Fin Tag.E6.rank) ∈ e6QpSupportList 14 ∧
      (1 : Fin Tag.E6.rank) ≠ 3 ∧ Tag.E6.cartan 1 3 ≠ 0
    decide
  have a32 : e6JAdj (e6QpSupport 14) 3 2 := by
    change (3 : Fin Tag.E6.rank) ∈ e6QpSupportList 14 ∧ (2 : Fin Tag.E6.rank) ∈ e6QpSupportList 14 ∧
      (3 : Fin Tag.E6.rank) ≠ 2 ∧ Tag.E6.cartan 3 2 ≠ 0
    decide
  have a34 : e6JAdj (e6QpSupport 14) 3 4 := by
    change (3 : Fin Tag.E6.rank) ∈ e6QpSupportList 14 ∧ (4 : Fin Tag.E6.rank) ∈ e6QpSupportList 14 ∧
      (3 : Fin Tag.E6.rank) ≠ 4 ∧ Tag.E6.cartan 3 4 ≠ 0
    decide
  revert h0 h5
  fin_cases j
  · intro h; exact absurd rfl h
  · intro _ _; exact Relation.ReflTransGen.refl
  · intro _ _; exact (Relation.ReflTransGen.single a13).tail a32
  · intro _ _; exact Relation.ReflTransGen.single a13
  · intro _ _; exact (Relation.ReflTransGen.single a13).tail a34
  · intro _ h; exact absurd rfl h

theorem d4Aux_support : d4Aux.support = d4Support := by
  ext j
  constructor
  · intro hj
    have h : j ∈ e6QpSupportList 14 := d4Aux_qpIndex ▸ d4Aux.support_subset hj
    change j ≠ 0 ∧ j ≠ 5
    revert h
    fin_cases j <;> decide
  · intro hj
    obtain ⟨h0, h5⟩ : j ≠ 0 ∧ j ≠ 5 := hj
    rw [d4Aux.mem_support_iff_component]
    left
    have hq : d4Aux.qpIndex = 14 := d4Aux_qpIndex
    rw [hq]
    exact reflTransGen_one j h0 h5

theorem kernelRoots_d4Gen : kernelRoots d4Gen.χ = parabolicRoots Tag.E6 d4Support := by
  rw [show d4Gen.χ = d4Aux.chi from rfl, d4Aux.kernelRoots_chi, d4Aux.Ξ_eq_parabolicRoots,
    d4Aux_support]

end Aux

section Datum

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_tauF (f : ℕ) (hf : 1 ≤ f) :
    ∃ S : MulAut (adjointGroup TwistTag.E6.tag L), ∀ g : adjointGroup TwistTag.E6.tag L,
      (S g : ModGL TwistTag.E6.tag L) =
        frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L) g := by
  obtain ⟨S, hS⟩ := ((exceptional_Lang_root_coordinate_surjectivity ℓ L).2.1 TwistTag.E6 f hf 1).1
  refine ⟨S, fun g => ?_⟩
  have h := hS g
  rw [zpow_one] at h
  exact h

variable (L ℓ) in
@[expose] def tauF (f : ℕ) (hf : 1 ≤ f) : MulAut (adjointGroup TwistTag.E6.tag L) :=
  (exists_tauF (L := L) (ℓ := ℓ) f hf).choose

theorem tauF_apply (f : ℕ) (hf : 1 ≤ f) (g : adjointGroup TwistTag.E6.tag L) :
    (tauF L ℓ f hf g : ModGL TwistTag.E6.tag L) =
      frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L) g :=
  (exists_tauF (L := L) (ℓ := ℓ) f hf).choose_spec g

omit [IsAlgClosed L] in
theorem exists_diagramMap_conj_pinnedX_unit' {γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.E6.tag γ) :
    ∃ μ : Lˣ, ∀ c : L, diagramMap TwistTag.E6 L * pinnedX TwistTag.E6.tag L γ c *
      (diagramMap TwistTag.E6 L)⁻¹ =
        pinnedX TwistTag.E6.tag L (permLattice TwistTag.E6.perm γ) (μ * c) := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.E6 hγ
  exact ⟨Units.mkOfMulEqOne ε ε hε, h⟩

omit [IsAlgClosed L] in
theorem frobTwist_simpleRootSL2 (f : ℕ) (j : Fin TwistTag.E6.tag.rank) (A : SL2 L) :
    frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L)
        (simpleRootSL2 TwistTag.E6.tag L j A) =
      simpleRootSL2 TwistTag.E6.tag L (TwistTag.E6.perm j)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f) A) := by
  have h : (frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L)).comp
      (simpleRootSL2 TwistTag.E6.tag L j) =
      (simpleRootSL2 TwistTag.E6.tag L (TwistTag.E6.perm j)).comp
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f)) :=
    MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
      fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L)
            (simpleRootSL2 TwistTag.E6.tag L j (uSL c)) =
          simpleRootSL2 TwistTag.E6.tag L (TwistTag.E6.perm j)
            (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f) (uSL c))
        rw [simpleRootSL2_uSL, map_uSL, simpleRootSL2_uSL]
        exact twistHom_xUnit TwistTag.E6 L (iterateFrobenius L ℓ f) j c
      · change frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L)
            (simpleRootSL2 TwistTag.E6.tag L j (vSL c)) =
          simpleRootSL2 TwistTag.E6.tag L (TwistTag.E6.perm j)
            (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f) (vSL c))
        rw [simpleRootSL2_vSL, map_vSL, simpleRootSL2_vSL]
        exact twistHom_yUnit TwistTag.E6 L (iterateFrobenius L ℓ f) j c
  exact DFunLike.congr_fun h A

theorem tauF_rootSL2 (f : ℕ) (hf : 1 ≤ f) (j : Fin TwistTag.E6.tag.rank) (A : SL2 L)
    (x : adjointGroup TwistTag.E6.tag L)
    (hx : (x : ModGL TwistTag.E6.tag L) = rootSL2 TwistTag.E6.tag L (Pi.single j 1) A) :
    (tauF L ℓ f hf x : ModGL TwistTag.E6.tag L) =
      rootSL2 TwistTag.E6.tag L (permLattice TwistTag.E6.perm (Pi.single j 1))
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f) A) := by
  rw [tauF_apply, hx, rootSL2_single', frobTwist_simpleRootSL2, permLattice_single,
    rootSL2_single']

variable (L ℓ) in
@[expose] def tauDatum (f : ℕ) (hf : 1 ≤ f) :
    GenFixedRootDatum Tag.E6 ℓ L (Multiplicative (Fin Tag.E6.rank → ℤ)) where
  simplyLaced := d4Gen.simplyLaced
  e := f
  one_le_e := hf
  χ := d4Gen.χ
  θ := d4Gen.θ
  isometry := d4Gen.isometry
  bijOn_kernelRoots := d4Gen.bijOn_kernelRoots
  bijOn_simpleRoots := d4Gen.bijOn_simpleRoots
  orbit_orthogonal := d4Gen.orbit_orthogonal
  orbit_reflection := d4Gen.orbit_reflection
  F := tauF L ℓ f hf
  map_torusGroup := map_subgroupOf_adjointGroup (tauF_apply f hf) torusGroup_le_adjointGroup
    (map_frobTwistGL_torusGroup ℓ f (diagramMap_mem_normalizer TwistTag.E6))
  map_rootSubgroup := fun α hα α' hα' => by
    have hα'' : α' = permLattice TwistTag.E6.perm α :=
      toReal_injective (hα'.symm.trans (d4Gen_theta_toReal hα))
    subst hα''
    exact map_subgroupOf_adjointGroup (tauF_apply f hf) (rootSubgroup_le_adjointGroup α)
      (map_frobTwistGL_rootSubgroup_of_conj ℓ f (θ := permLattice TwistTag.E6.perm)
        (fun _ hγ => exists_diagramMap_conj_pinnedX_unit' hγ) hα.1)
  map_rootSL2 := fun β hβ β' hβ' A x hx => by
    obtain ⟨j, hj, rfl⟩ := d4Aux.mem_unionSimpleRoots_iff.1 hβ
    have hβK : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots d4Gen.χ :=
      d4Aux.single_mem_kernelRoots hj
    have hβ'' : β' = permLattice TwistTag.E6.perm (Pi.single j 1) :=
      toReal_injective (hβ'.symm.trans (d4Gen_theta_toReal hβK))
    subst hβ''
    exact tauF_rootSL2 f hf j A x hx
  J := d4Gen.J
  isThetaOrbit := d4Gen.isThetaOrbit

end Datum

end CFSG.RankThree.PartOne.KD4L
