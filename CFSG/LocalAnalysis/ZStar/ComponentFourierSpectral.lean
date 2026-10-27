module

public import CFSG.LocalAnalysis.ZStar.FourierBrauerExactness
public import CFSG.LocalAnalysis.ZStar.ComponentResidueFourier

public section

namespace CFSG

namespace ZStar.ComponentFourierSpectral

open ZStar.AbstractStepV
open ZStar.ComponentIntegralLattice
open ZStar.ComponentResidueFourier
open ZStar.FourierBrauerExactness
open ZStar.ModularBrauerQuotient
open ZStar.OddFourierProjectors
open ZStar.OddRootResidue
open ZStar.PadicBlockField
open ZStar.PrincipalBlockCharacterStability
open ZStar.PrincipalBlockKernel
open ZStar.RegularBrauerQuotient
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnBlock

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

attribute [local instance 2000] CommRing.toCommSemiring

noncomputable local instance residue2AlgebraZModTwo :
    Algebra (ZMod 2) Residue2 :=
  OddRootResidue.zmod2ToResidue.toAlgebra

def cyclicPowersEquiv (v : G) :
    Multiplicative (ZMod (orderOf v)) ≃* Subgroup.zpowers v :=
  zmodMulEquivOfGenerator
    (g := (⟨v, Subgroup.mem_zpowers v⟩ : Subgroup.zpowers v))
    (fun x ↦ by
      obtain ⟨n, hn⟩ := x.property
      refine ⟨n, ?_⟩
      exact Subtype.ext hn)
    (Nat.card_zpowers v)

@[expose] def cyclicPowerHom (v : G) :
    Multiplicative (ZMod (orderOf v)) →* G :=
  (Subgroup.zpowers v).subtype.comp (cyclicPowersEquiv v).toMonoidHom

@[simp]
theorem cyclicPowerHom_generator (v : G) :
    cyclicPowerHom v (Multiplicative.ofAdd 1) = v := by
  change ((cyclicPowersEquiv v) (Multiplicative.ofAdd 1) : G) = v
  exact congrArg Subtype.val
    (zmodMulEquivOfGenerator_apply_ofAdd_one
      (g := (⟨v, Subgroup.mem_zpowers v⟩ : Subgroup.zpowers v))
      (fun x ↦ by
        obtain ⟨n, hn⟩ := x.property
        refine ⟨n, ?_⟩
        exact Subtype.ext hn)
      (Nat.card_zpowers v))

private def componentCyclicIntegralRepresentation
    (D : Decomposition G) (i : Fin D.blockCount) (v : G) :
    Representation OddRootResidue.O2
      (Multiplicative (ZMod (orderOf v)))
      (componentOrbitLattice D i) :=
  (componentIntegralRepresentation D i).comp (cyclicPowerHom v)

private theorem componentCyclicIntegralRepresentation_generator_toMatrix
    (D : Decomposition G) (i : Fin D.blockCount) (v : G) :
    LinearMap.toMatrix (componentIntegralBasis D i)
        (componentIntegralBasis D i)
        (componentCyclicIntegralRepresentation D i v
          (Multiplicative.ofAdd 1)) =
      componentIntegralMatrix D i v := by
  change LinearMap.toMatrix (componentIntegralBasis D i)
      (componentIntegralBasis D i)
      (componentIntegralRepresentation D i
        (cyclicPowerHom v (Multiplicative.ofAdd 1))) = _
  rw [cyclicPowerHom_generator]
  exact componentIntegralRepresentation_toMatrix D i v

theorem componentIntegralMatrix_commute_cyclicPower
    (D : Decomposition G) (i : Fin D.blockCount) {w v : G}
    (hwv : Commute w v)
    (a : Multiplicative (ZMod (orderOf v))) :
    Commute (componentIntegralMatrix D i w)
      (componentIntegralMatrix D i (cyclicPowerHom v a)) := by
  let y : Subgroup.zpowers v := cyclicPowersEquiv v a
  have hy : (y : G) = cyclicPowerHom v a := rfl
  obtain ⟨n, hn⟩ := y.property
  have hwy : Commute w (y : G) := by
    rw [← hn]
    exact hwv.zpow_right n
  rw [commute_iff_eq, ← componentIntegralMatrix_mul,
    ← componentIntegralMatrix_mul]
  exact congrArg (componentIntegralMatrix D i) (by simpa [hy] using hwy.eq)

private theorem componentIntegralRepresentation_commute_cyclicPower
    (D : Decomposition G) (i : Fin D.blockCount) {w v : G}
    (hwv : Commute w v)
    (a : Multiplicative (ZMod (orderOf v))) :
    Commute ((componentIntegralRepresentation D i) w)
      ((componentCyclicIntegralRepresentation D i v) a) := by
  let y : Subgroup.zpowers v := cyclicPowersEquiv v a
  have hy : (y : G) = cyclicPowerHom v a := rfl
  obtain ⟨n, hn⟩ := y.property
  have hwy : Commute w (y : G) := by
    rw [← hn]
    exact hwv.zpow_right n
  change Commute ((componentIntegralRepresentation D i) w)
    ((componentIntegralRepresentation D i) (cyclicPowerHom v a))
  have hwy' : Commute w (cyclicPowerHom v a) := by
    simpa [hy] using hwy
  exact hwy'.map (componentIntegralRepresentation D i)

private theorem odd_orderOf_of_mem_odd_subgroup
    {H : Subgroup G} (N : Subgroup H) (hNodd : Odd (Nat.card N))
    (v : H) (hv : v ∈ N) :
    Odd (orderOf (v : G)) := by
  let n : N := ⟨v, hv⟩
  have hn : Odd (orderOf n) :=
    hNodd.of_dvd_nat (orderOf_dvd_natCard n)
  have hnH : Odd (orderOf (n : H)) := by
    rw [Subgroup.orderOf_coe]
    exact hn
  rw [Subgroup.orderOf_coe]
  simpa only [n] using hnH

private theorem odd_natCast_isUnit_o2 {m : ℕ} (hm : Odd m) :
    IsUnit (m : OddRootResidue.O2) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  rw [map_natCast, odd_natCast_residue2 hm]
  exact one_ne_zero

private theorem componentIntegralMatrix_mul_fourierProjectorMatrix
    (D : Decomposition G) (i : Fin D.blockCount) (v : G)
    [NeZero (orderOf v)]
    [Invertible (orderOf v : OddRootResidue.O2)]
    (z : OddRootResidue.O2) (hz : z ^ orderOf v = 1)
    (s : ZMod (orderOf v)) :
    componentIntegralMatrix D i v *
        fourierProjectorMatrix (componentIntegralBasis D i)
          (componentCyclicIntegralRepresentation D i v) z hz s =
      z ^ s.val •
        fourierProjectorMatrix (componentIntegralBasis D i)
          (componentCyclicIntegralRepresentation D i v) z hz s := by
  have h := congrArg
    (LinearMap.toMatrix (componentIntegralBasis D i)
      (componentIntegralBasis D i))
    (generator_mul_fourierProjector
      (componentCyclicIntegralRepresentation D i v) z hz s)
  simpa only [LinearMap.toMatrix_mul, map_smul,
    fourierProjectorMatrix,
    componentCyclicIntegralRepresentation_generator_toMatrix] using h

private theorem mapped_componentFourierProjectorMatrix_eigen
    {k : Type*} [Field k]
    (D : Decomposition G) (i : Fin D.blockCount) (v : G)
    [NeZero (orderOf v)]
    [Invertible (orderOf v : OddRootResidue.O2)]
    (z : OddRootResidue.O2) (hz : z ^ orderOf v = 1)
    (s : ZMod (orderOf v)) (q : OddRootResidue.O2 →+* k)
    (y : Fin (D.blockSize i) → k) :
    Matrix.toLin' ((componentIntegralMatrix D i v).map q)
        (Matrix.toLin'
          ((fourierProjectorMatrix (componentIntegralBasis D i)
            (componentCyclicIntegralRepresentation D i v) z hz s).map q) y) =
      q (z ^ s.val) •
        Matrix.toLin'
          ((fourierProjectorMatrix (componentIntegralBasis D i)
            (componentCyclicIntegralRepresentation D i v) z hz s).map q) y := by
  have h0 :=
    componentIntegralMatrix_mul_fourierProjectorMatrix D i v z hz s
  have hmap :
      (componentIntegralMatrix D i v).map q *
          (fourierProjectorMatrix (componentIntegralBasis D i)
            (componentCyclicIntegralRepresentation D i v) z hz s).map q =
        q (z ^ s.val) •
          (fourierProjectorMatrix (componentIntegralBasis D i)
            (componentCyclicIntegralRepresentation D i v) z hz s).map q := by
    rw [← Matrix.map_mul, h0]
    ext j k
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [← Matrix.toLin'_mul_apply, hmap]
  simp [Matrix.toLin'_apply]

private theorem selectedComponentOrbitLatticeSpectralDataAvailable
    (D : Decomposition G) :
    SelectedComponentOrbitLatticeSpectralDataAvailable D
      (IsLocalRing.residue OddRootResidue.O2) := by
  intro i hi w _hwne hw2 H hH N hNnormal hNodd v hv
  subst H
  let : N.Normal := hNnormal
  let nN : N := ⟨v, hv⟩
  have hm : Odd (orderOf (v : G)) :=
    odd_orderOf_of_mem_odd_subgroup N hNodd v hv
  let : NeZero (orderOf (v : G)) :=
    ⟨(orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite (v : G)))⟩
  let : Invertible (orderOf (v : G) : OddRootResidue.O2) :=
    (odd_natCast_isUnit_o2 hm).invertible
  obtain ⟨z, hz⟩ :=
    exists_primitiveRoot_o2 (orderOf (v : G))
  let S := NonzeroFourierSector (orderOf (v : G))
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let ES : S →
      Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i))
        OddRootResidue.O2 := fun s ↦
    fourierProjectorMatrix (componentIntegralBasis D i)
      (componentCyclicIntegralRepresentation D i (v : G))
      z hz.pow_eq_one s.1
  let E : Fin (Fintype.card S) →
      Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i))
        OddRootResidue.O2 := fun s ↦ ES (e s)
  let cS : S → TwoAdicComplex := fun s ↦
    algebraMap OddRootResidue.O2 TwoAdicComplex
      (z ^ s.1.val - 1)
  let c : Fin (Fintype.card S) → TwoAdicComplex := fun s ↦ cS (e s)
  have hwv : Commute w (v : G) := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_centralizer_singleton_iff.mp v.property).symm
  have hEidemS : ∀ s : S, ES s * ES s = ES s := by
    intro s
    exact fourierProjectorMatrix_idempotent
      (componentIntegralBasis D i)
      (componentCyclicIntegralRepresentation D i (v : G))
      z hz.pow_eq_one s.1
  have hEcommS : ∀ s : S,
      ES s * componentIntegralMatrix D i w =
        componentIntegralMatrix D i w * ES s := by
    intro s
    simpa only [ES, componentIntegralRepresentation_toMatrix] using
      (fourierProjectorMatrix_commute
        (componentIntegralBasis D i)
        (componentCyclicIntegralRepresentation D i (v : G))
        z hz.pow_eq_one s.1
        ((componentIntegralRepresentation D i) w)
        (fun a ↦ componentIntegralRepresentation_commute_cyclicPower
          D i hwv a))
  have hEidem : ∀ s, E s * E s = E s := by
    intro s
    exact hEidemS (e s)
  have hEcomm : ∀ s,
      E s * componentIntegralMatrix D i w =
        componentIntegralMatrix D i w * E s := by
    intro s
    exact hEcommS (e s)
  have hmodular : ∀ s,
      (Matrix.toLin'
          ((componentIntegralMatrix D i w).map
            (IsLocalRing.residue OddRootResidue.O2) - 1)).ker ⊓
          (Matrix.toLin' ((E s).map
            (IsLocalRing.residue OddRootResidue.O2))).range ≤
        (Matrix.toLin'
          ((componentIntegralMatrix D i w).map
            (IsLocalRing.residue OddRootResidue.O2) - 1)).range := by
    intro s
    have hsval : (e s).1.val ≠ 0 := by
      intro hs0
      exact (e s).2 ((ZMod.val_eq_zero _).mp hs0)
    have hzeta :
        IsLocalRing.residue OddRootResidue.O2 (z ^ (e s).1.val) ≠ 1 :=
      residue_pow_ne_one_of_primitive_odd hm hz
        ⟨(e s).1.val, ZMod.val_lt _⟩ hsval
    refine modular_exact_of_nontrivial_eigenvalue
      ((componentIntegralMatrix D i w).map
        (IsLocalRing.residue OddRootResidue.O2))
      ((componentIntegralMatrix D i (v : G)).map
        (IsLocalRing.residue OddRootResidue.O2))
      ((E s).map (IsLocalRing.residue OddRootResidue.O2))
      (IsLocalRing.residue OddRootResidue.O2 (z ^ (e s).1.val))
      hzeta ?_ ?_
    · intro x hx
      have hxker : x ∈
          brauerKernel (componentResidueRepresentationZMod D i) w := by
        change involutionDifference
          (componentResidueRepresentationZMod D i) w x = 0
        rw [involutionDifference_componentResidueRepresentationZMod_apply]
        exact hx
      let xker : brauerKernel
          (componentResidueRepresentationZMod D i) w := ⟨x, hxker⟩
      have hrange :=
        oddNormal_action_sub_mem_involutionDifference_range
          (componentResidueRepresentationZMod D i) w hw2
          (selected_componentResidueRepresentation_principalBlockActsAsIdentity
            D i hi)
          N hNodd nN xker
      obtain ⟨y, hy⟩ := hrange
      refine ⟨y, ?_⟩
      rw [← involutionDifference_componentResidueRepresentationZMod_apply
          D i w y,
        ← involutionDifference_componentResidueRepresentationZMod_apply
          D i (v : G) x]
      simpa [involutionDifference] using hy
    · intro y
      simpa only [E, ES] using
        mapped_componentFourierProjectorMatrix_eigen
          D i (v : G) z hz.pow_eq_one (e s).1
          (IsLocalRing.residue OddRootResidue.O2) y
  have hfourierO := generatorMatrix_sub_one_eq_sum_nonzero
    (componentIntegralBasis D i)
    (componentCyclicIntegralRepresentation D i (v : G)) z hz
  rw [componentCyclicIntegralRepresentation_generator_toMatrix] at hfourierO
  have hfourierK :
      (componentIntegralMatrix D i (v : G)).map
            (algebraMap OddRootResidue.O2 TwoAdicComplex) - 1 =
        ∑ s : S, cS s •
          (ES s).map (algebraMap OddRootResidue.O2 TwoAdicComplex) := by
    calc
      (componentIntegralMatrix D i (v : G)).map
            (algebraMap OddRootResidue.O2 TwoAdicComplex) - 1 =
          (componentIntegralMatrix D i (v : G) - 1).map
            (algebraMap OddRootResidue.O2 TwoAdicComplex) := by
        simpa only [RingHom.mapMatrix_apply, map_one] using
          (((algebraMap OddRootResidue.O2 TwoAdicComplex).mapMatrix).map_sub
            (componentIntegralMatrix D i (v : G)) 1).symm
      _ = (∑ s : S, (z ^ s.1.val - 1) • ES s).map
            (algebraMap OddRootResidue.O2 TwoAdicComplex) := by
        exact congrArg
          (fun M => M.map (algebraMap OddRootResidue.O2 TwoAdicComplex))
          hfourierO
      _ = ∑ s : S, cS s •
          (ES s).map (algebraMap OddRootResidue.O2 TwoAdicComplex) := by
        ext j k
        simp [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, cS]
  have hspectral :
      (componentIntegralMatrix D i w).map
            (algebraMap OddRootResidue.O2 TwoAdicComplex) *
          ((componentIntegralMatrix D i (v : G)).map
            (algebraMap OddRootResidue.O2 TwoAdicComplex) - 1) =
        ∑ s, c s •
          ((E s).map (algebraMap OddRootResidue.O2 TwoAdicComplex) *
            (componentIntegralMatrix D i w).map
              (algebraMap OddRootResidue.O2 TwoAdicComplex)) := by
    calc
      (componentIntegralMatrix D i w).map
            (algebraMap OddRootResidue.O2 TwoAdicComplex) *
          ((componentIntegralMatrix D i (v : G)).map
            (algebraMap OddRootResidue.O2 TwoAdicComplex) - 1) =
          (componentIntegralMatrix D i w).map
              (algebraMap OddRootResidue.O2 TwoAdicComplex) *
            (∑ s : S, cS s •
              (ES s).map
                (algebraMap OddRootResidue.O2 TwoAdicComplex)) := by
        rw [hfourierK]
      _ = ∑ s : S, cS s •
          ((ES s).map (algebraMap OddRootResidue.O2 TwoAdicComplex) *
            (componentIntegralMatrix D i w).map
              (algebraMap OddRootResidue.O2 TwoAdicComplex)) := by
        rw [Matrix.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [Matrix.mul_smul]
        have hc := congrArg
          (fun M => M.map (algebraMap OddRootResidue.O2 TwoAdicComplex))
          (hEcommS s)
        rw [show
          (componentIntegralMatrix D i w).map
                (algebraMap OddRootResidue.O2 TwoAdicComplex) *
              (ES s).map (algebraMap OddRootResidue.O2 TwoAdicComplex) =
            (ES s).map (algebraMap OddRootResidue.O2 TwoAdicComplex) *
              (componentIntegralMatrix D i w).map
                (algebraMap OddRootResidue.O2 TwoAdicComplex) by
          simpa only [Matrix.map_mul] using hc.symm]
      _ = ∑ s : Fin (Fintype.card S), cS (e s) •
          ((ES (e s)).map
              (algebraMap OddRootResidue.O2 TwoAdicComplex) *
            (componentIntegralMatrix D i w).map
              (algebraMap OddRootResidue.O2 TwoAdicComplex)) := by
        exact (Equiv.sum_comp e (fun s : S ↦ cS s •
          ((ES s).map (algebraMap OddRootResidue.O2 TwoAdicComplex) *
            (componentIntegralMatrix D i w).map
              (algebraMap OddRootResidue.O2 TwoAdicComplex)))).symm
      _ = ∑ s, c s •
          ((E s).map (algebraMap OddRootResidue.O2 TwoAdicComplex) *
            (componentIntegralMatrix D i w).map
              (algebraMap OddRootResidue.O2 TwoAdicComplex)) := by
        rfl
  exact ⟨{
    sectorCount := Fintype.card S
    E := E
    c := c
    E_idempotent := hEidem
    E_commutes_P := hEcomm
    modular_exact := hmodular
    spectral_decomposition := hspectral }⟩

theorem selected_componentCharacter_centralizerOddCoreStable
    (D : Decomposition G) (i : Fin D.blockCount)
    (hi : i ∈ selectedIndices D.equiv
      (principalBlockTwoAdic (G := G))) :
    CentralizerOddCoreStable (componentRepresentation D i).character := by
  exact selected_componentCharacter_centralizerOddCoreStable_of_orbitLattice
    D (IsLocalRing.residue OddRootResidue.O2)
      IsLocalRing.residue_surjective
      (selectedComponentOrbitLatticeSpectralDataAvailable D) i hi

end

end ZStar.ComponentFourierSpectral

end CFSG
