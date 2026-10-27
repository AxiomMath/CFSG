module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDPoints
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface
public import CFSG.RankThree.PartTwo.Census.Assembly
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.FixedPoints
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
import all TauCeti.Algebra.CharP.Frobenius.Fixed

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

def dcqEquivOfInjective {H M : Type*} [Group H] [Group M] (ψ : H →* M)
    (hψ : Function.Injective ψ) {Ω : Subgroup M} (h : ⁅ψ.range, ψ.range⁆ = Ω) :
    DerivedCentralQuotient H ≃* ↥Ω ⧸ Subgroup.center ↥Ω :=
  let e : ↥(_root_.commutator H) ≃* ↥Ω :=
    ((_root_.commutator H).equivMapOfInjective ψ hψ).trans (MulEquiv.subgroupCongr (by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, h]))
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem two_eq_zero_frobeniusFixedSubfield {A : Type} [Field A] {p : ℕ} [Fact p.Prime] [CharP A p]
    (hp : p = 2) (k : ℕ) : (2 : ↥(frobeniusFixedSubfield A p k)) = 0 := by
  subst hp
  have h := CharP.cast_eq_zero (↥(frobeniusFixedSubfield A 2 k)) 2
  rwa [Nat.cast_ofNat] at h

def typeDGroupEquivStatedProj (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p = 2) :
    ValidLieTypeIndex.Group ⟨.D r q, hv⟩ ≃*
      StatedProj (StatedOmega
        (StatedQuadPlus r ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩))) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have h2 := two_eq_zero_frobeniusFixedSubfield (A := ValidLieTypeIndex.Closure ⟨.D r q, hv⟩)
    ((show ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩ = q.p from
      LieTypeIndex.characteristic_D r q).trans hp)
    (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩)
  let e1 : ValidLieTypeIndex.Group ⟨.D r q, hv⟩ ≃* DerivedCentralQuotient
      ↥(TypeDSpinCarrier.points r hr ↥(frobeniusFixedSubring
        (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩) (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩))) :=
    DerivedCentralQuotient.congr (TypeDSpinCarrier.pointsMulEquivFixedSubgroupFrobenius r hr
      (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩)).symm
  let e2 := dcqEquivOfInjective (orthPoints r hr _) (orthPoints_injective r hr h2)
    (commutator_range r hr)
  let e3 := QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadPlus (K := ↥(
    frobeniusFixedSubfield (ValidLieTypeIndex.Closure ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩))) (n := r) (by omega))
  exact e1.trans (e2.trans e3)

open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars)
open CFSG.Assembly.RankThreeEven (projImage projOmegaPlus)

theorem statedQuadPlus_comp {K L : Type} [Field K] [Field L] (φ : K ≃+* L) (r : ℕ)
    (v : Fin r ⊕ Fin r → K) : StatedQuadPlus r L (φ ∘ v) = φ (StatedQuadPlus r K v) := by
  simp only [StatedQuadPlus, Function.comp_apply, map_sum, map_mul]

theorem projImage_statedOmegaPlus_eq_projOmegaPlus (r : ℕ) (K : Type) [Field K] :
    projImage (StatedOmega (StatedQuadPlus r K)) = projOmegaPlus r K :=
  rfl

def typeDGroupEquivProjOmegaPlus (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p = 2) [Fact q.p.Prime] :
    ValidLieTypeIndex.Group ⟨.D r q, hv⟩ ≃* projOmegaPlus r (GaloisField q.p q.exponent) :=
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.D r q, hv⟩
  let φ : ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) ≃+* GaloisField q.p q.exponent :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField _ q.p q.exponent q.exponent_pos (by
      rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
        show ValidLieTypeIndex.characteristic ⟨.D r q, hv⟩ = q.p from
          LieTypeIndex.characteristic_D r q,
        show ValidLieTypeIndex.fieldExponent ⟨.D r q, hv⟩ = q.exponent from
          LieTypeIndex.fieldExponent_D r q])
  (typeDGroupEquivStatedProj r q hv hp).trans
    (CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv (glCongr φ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ (statedQuadPlus_comp φ r))
      (glCongr_statedScalars φ) (projImage_statedOmegaPlus_eq_projOmegaPlus r _))

theorem nonempty_typeDGroupEquivProjOmegaPlus (r f : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (hp : q.p = 2) (he : q.exponent = f) :
    Nonempty (ValidLieTypeIndex.Group ⟨.D r q, hv⟩ ≃* projOmegaPlus r (GaloisField 2 f)) := by
  rcases q with ⟨p, e, hpp, hep⟩
  dsimp only at hp he
  subst hp
  subst he
  have : Fact (Nat.Prime 2) := ⟨hpp⟩
  exact ⟨typeDGroupEquivProjOmegaPlus r ⟨2, e, hpp, hep⟩ hv rfl⟩

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD

namespace CFSG.RankThree.PartTwo.Census

open TauCeti CFSG.Assembly.LowTwoRank

theorem bridgeOmega8PlusTwo : BridgeOmega8PlusTwo := fun q hv hp he =>
  Carrier.SpinD.nonempty_typeDGroupEquivProjOmegaPlus 4 1 q hv hp he

theorem statedClassicalModel_typeD_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p = 2) {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩) :
    StatedClassicalModel G .POmegaPlus r q.p q.exponent := by
  have hr : 4 ≤ r := TypeDDiagramLieIndex.four_le_rank ⟨⟨.D r q, hv⟩, by simp⟩
  refine ⟨⟨q.prime_p, q.exponent_pos, hr⟩,
    ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩), inferInstance,
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, ?_,
    ⟨e.trans (Carrier.SpinD.typeDGroupEquivStatedProj r q hv hp)⟩⟩
  rw [ValidLieTypeIndex.card_fixedField]
  simp [ValidLieTypeIndex.fieldOrder]

theorem catalogBridgeFor_D_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid)
    (hp : q.p = 2) : CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.D r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_typeD_even r q hv hp e⟩))

end CFSG.RankThree.PartTwo.Census
