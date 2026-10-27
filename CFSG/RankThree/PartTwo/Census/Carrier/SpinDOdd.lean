module

import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
import all TauCeti.Algebra.CharP.Frobenius.Fixed
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDPoints
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.FixedPoints

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti TauCeti.TypeDSpinCarrier SpinFrame CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin
open scoped commutatorElement

section CentralKernel

variable {G : Type*} [Group G]

theorem commutatorElement_mul_right_of_mem_center {x a b : G}
    (hb : ⁅x, b⁆ ∈ Subgroup.center G) : ⁅x, a * b⁆ = ⁅x, b⁆ * ⁅x, a⁆ := by
  have hc := Subgroup.mem_center_iff.mp hb
  calc ⁅x, a * b⁆ = (x * a * x⁻¹) * ⁅x, b⁆ * a⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, b⁆ * (x * a * x⁻¹) * a⁻¹ := by rw [hc (x * a * x⁻¹)]
    _ = ⁅x, b⁆ * ⁅x, a⁆ := by
        simp only [commutatorElement_def]
        group

theorem commutator_le_centralizer_of_mem_center (P : Subgroup G) {x : G}
    (hx : ∀ y ∈ P, ⁅x, y⁆ ∈ Subgroup.center G) : ⁅P, P⁆ ≤ Subgroup.centralizer {x} := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hmul : ∀ {y z : G}, z ∈ P → ⁅x, y * z⁆ = ⁅x, z⁆ * ⁅x, y⁆ := fun hz =>
    commutatorElement_mul_right_of_mem_center (hx _ hz)
  have hinv : ∀ {y : G}, y ∈ P → ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := fun {y} hy => by
    have h := hmul (y := y) (inv_mem hy)
    rw [mul_inv_cancel, commutatorElement_one_right] at h
    exact (eq_inv_of_mul_eq_one_left h.symm)
  have hcomm : ∀ {y z : G}, y ∈ P → z ∈ P → ⁅x, y⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅x, y⁆ :=
    fun {_ z} hy _ => (Subgroup.mem_center_iff.mp (hx _ hy) ⁅x, z⁆).symm
  have key : ⁅x, ⁅a, b⁆⁆ = 1 := by
    rw [commutatorElement_def a b, hmul (inv_mem hb), hmul (inv_mem ha), hmul hb, hinv ha,
      hinv hb]
    have h1 := hcomm ha hb
    calc ⁅x, b⁆⁻¹ * (⁅x, a⁆⁻¹ * (⁅x, b⁆ * ⁅x, a⁆))
        = ⁅x, b⁆⁻¹ * (⁅x, a⁆⁻¹ * (⁅x, a⁆ * ⁅x, b⁆)) := by rw [h1]
      _ = 1 := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((commutatorElement_eq_one_iff_mul_comm).mp key).symm

def dcqEquivOfCentralKernel {H M : Type*} [Group H] [Group M] (ψ : H →* M)
    (hker : ψ.ker ≤ Subgroup.center H) {Ω : Subgroup M} (h : ⁅ψ.range, ψ.range⁆ = Ω)
    (hperf : ⁅Ω, Ω⁆ = Ω) : DerivedCentralQuotient H ≃* ↥Ω ⧸ Subgroup.center ↥Ω := by
  have hmap : (_root_.commutator H).map ψ = Ω := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, h]
  have hmem : ∀ x : _root_.commutator H, ψ x ∈ Ω := fun x => hmap ▸ ⟨x, x.2, rfl⟩
  let ψP : _root_.commutator H →* Ω := (ψ.comp (_root_.commutator H).subtype).codRestrict Ω hmem
  have hsurj : Function.Surjective ψP := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let f : _root_.commutator H →* ↥Ω ⧸ Subgroup.center ↥Ω :=
    (QuotientGroup.mk' (Subgroup.center ↥Ω)).comp ψP
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp hsurj
  have hkerf : Subgroup.center (_root_.commutator H) = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro ω
      obtain ⟨y, rfl⟩ := hsurj ω
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    · intro hx
      have hcom : ∀ y ∈ _root_.commutator H, ⁅(x : H), y⁆ ∈ Subgroup.center H := by
        intro y hy
        apply hker
        rw [MonoidHom.mem_ker, map_commutatorElement]
        have h1 := Subgroup.mem_center_iff.mp hx (ψP ⟨y, hy⟩)
        have h2 : ψ (x : H) * ψ y = ψ y * ψ (x : H) :=
          (congrArg Subtype.val h1).symm
        exact (commutatorElement_eq_one_iff_mul_comm).mpr h2
      have hcent := commutator_le_centralizer_of_mem_center (_root_.commutator H) hcom
      rw [Subgroup.mem_center_iff]
      intro y
      have hy' : ψ (y : H) ∈ (⁅_root_.commutator H, _root_.commutator H⁆).map ψ := by
        rw [Subgroup.map_commutator, hmap, hperf]
        exact hmem y
      obtain ⟨y', hy'm, hy'e⟩ := hy'
      have hz : y'⁻¹ * (y : H) ∈ Subgroup.center H := by
        apply hker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hy'e, inv_mul_cancel]
      have hxy' : (x : H) * y' = y' * (x : H) :=
        ((Subgroup.mem_centralizer_singleton_iff).mp (hcent hy'm)).symm
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      calc (y : H) * (x : H) = y' * (y'⁻¹ * (y : H)) * (x : H) := by group
        _ = y' * ((x : H) * (y'⁻¹ * (y : H))) := by
            rw [mul_assoc, (Subgroup.mem_center_iff.mp hz (x : H))]
        _ = (x : H) * (y : H) := by
            rw [← mul_assoc, ← hxy', mul_assoc, ← mul_assoc y', mul_inv_cancel, one_mul]
  exact (QuotientGroup.quotientMulEquivOfEq hkerf).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

end CentralKernel

section Kernel

variable (n : ℕ) (hn : 4 ≤ n)

theorem orthPoints_ker_le_center (K : Type) [Field K] :
    (orthPoints n hn K).ker ≤ Subgroup.center (points n hn K) := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hρ : (frame n).rho K (g : GL (Fin (dimension n)) K) = 1 := by
    rw [← coe_orthPoints, hg, Units.val_one]
  have hcomm : ∀ a, ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) K) * (frame n).gamA K a =
      (frame n).gamA K a * ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) K) := fun a => by
    have h := (frame n).conj_eq_of_rho_eq_one (points_le_normGroup n hn K g.2) hρ a
    have hgg : (↑(g : Matrix.GeneralLinearGroup (Fin (dimension n)) K)⁻¹ :
        Matrix (Fin (dimension n)) (Fin (dimension n)) K) *
        ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) K) * (frame n).gamA K a
        = ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
            Matrix (Fin (dimension n)) (Fin (dimension n)) K) * (frame n).gamA K a *
          ((↑(g : Matrix.GeneralLinearGroup (Fin (dimension n)) K)⁻¹ :
            Matrix (Fin (dimension n)) (Fin (dimension n)) K) *
          ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) K) :
            Matrix (Fin (dimension n)) (Fin (dimension n)) K)) := by rw [hgg, mul_one]
      _ = _ := by rw [← mul_assoc, h]
  have hs := eq_smul_one_of_commute n _ hcomm
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hs, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

end Kernel

def typeDGroupEquivStatedProj_of_valid (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) :
    ValidLieTypeIndex.Group ⟨.D r q, hv⟩ ≃*
      StatedProj (StatedOmega
        (StatedQuadPlus r ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩))) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hperf := isPerfect_statedOmega_quadPlus (n := r)
    (K := ↥(frobeniusFixedSubfield (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩))) (by omega)
  have hperf' : ⁅StatedOmega (StatedQuadPlus r ↥(frobeniusFixedSubfield
        (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩) (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩))),
      StatedOmega (StatedQuadPlus r ↥(frobeniusFixedSubfield
        (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩) (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩)))⁆ =
      StatedOmega (StatedQuadPlus r ↥(frobeniusFixedSubfield
        (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩) (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩))) := by
    rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
      Subgroup.range_subtype]
  let e1 : ValidLieTypeIndex.Group ⟨.D r q, hv⟩ ≃* DerivedCentralQuotient
      ↥(TypeDSpinCarrier.points r hr ↥(frobeniusFixedSubring
        (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩) (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩))) :=
    DerivedCentralQuotient.congr (TypeDSpinCarrier.pointsMulEquivFixedSubgroupFrobenius r hr
      (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩)).symm
  let e2 := dcqEquivOfCentralKernel (orthPoints r hr _) (orthPoints_ker_le_center r hr _)
    (commutator_range r hr) hperf'
  let e3 := QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadPlus (K := ↥(
    frobeniusFixedSubfield (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩))) (n := r) (by omega))
  exact e1.trans (e2.trans e3)

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD

namespace CFSG.RankThree.PartTwo.Census

open TauCeti CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_typeD (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩) :
    StatedClassicalModel G .POmegaPlus r q.p q.exponent := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  refine ⟨⟨q.prime_p, q.exponent_pos, hr⟩,
    ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩), inferInstance,
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, ?_,
    ⟨e.trans (Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv)⟩⟩
  rw [ValidLieTypeIndex.card_fixedField]
  simp [ValidLieTypeIndex.fieldOrder]

theorem catalogBridgeFor_D (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) :
    CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.D r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_typeD r q hv e⟩))

theorem catalogBridgeFor_D_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (_hp : q.p ≠ 2) : CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.D r q, hv⟩) :=
  catalogBridgeFor_D r q hv

end CFSG.RankThree.PartTwo.Census
