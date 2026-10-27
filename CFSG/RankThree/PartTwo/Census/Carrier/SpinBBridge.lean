module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBPoints
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface
public import CFSG.RankThree.PartTwo.Census.Assembly
public import CFSG.RankThree.PartTwo.Sec4.Census.Bridges
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.FixedPoints
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
import all TauCeti.Algebra.CharP.Frobenius.Fixed

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinB

open TauCeti CFSG.Assembly.LowTwoRank

theorem exists_mul_self_eq_frobeniusFixedSubfield {A : Type} [Field A] [ExpChar A 2] {k : ℕ}
    (hk : 0 < k)
    (c : ↥(frobeniusFixedSubfield A 2 k)) : ∃ u : ↥(frobeniusFixedSubfield A 2 k), u * u = c := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have hc : (c : A) ^ 2 ^ (0 + j + 1) = c := (mem_frobeniusFixedSubfield).1 c.2
  refine ⟨c ^ 2 ^ j, Subtype.ext ?_⟩
  rw [Subfield.coe_mul, SubmonoidClass.coe_pow, ← pow_add, ← two_mul, ← pow_succ']
  simpa using hc

def spinBFixedEquiv (n p k : ℕ) [Fact p.Prime] (A : Type) [Field A] [CharP A p] (hp : p = 2)
    (hk : 0 < k) :
    ↥(fixedSubgroup (TypeBSpinCarrier.frobenius n p k A)) ≃*
      GLSymplecticFin (n + 1) ↥(frobeniusFixedSubfield A p k) := by
  subst hp
  have h2 : (2 : ↥(frobeniusFixedSubfield A 2 k)) = 0 := by
    have h := CharP.cast_eq_zero (↥(frobeniusFixedSubfield A 2 k)) 2
    rwa [Nat.cast_ofNat] at h
  exact (TypeBSpinCarrier.pointsMulEquivFixedSubgroupFrobenius n 2 k A).symm.trans
    (pointsEquivSp n h2 (exists_mul_self_eq_frobeniusFixedSubfield hk))

def typeBGroupEquivStatedProj (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p = 2) (hr : 3 ≤ r) :
    ValidLieTypeIndex.Group ⟨.B r q, hv⟩ ≃*
      StatedProj (StatedSp r ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) := by
  cases r with
  | zero => exact absurd hr (by omega)
  | succ m =>
    have hperf : Group.IsPerfect ↥(GLSymplecticFin (m + 1)
        ↥(frobeniusFixedSubfield (ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩)
          (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩))) :=
      ⟨CFSG.ClassicalGroups.Symplectic.commutator_GLSymplecticFin_eq_top_of_three_le _ _ hr⟩
    letI := hperf
    exact (DerivedCentralQuotient.congr (spinBFixedEquiv m
        (ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩)
        (ValidLieTypeIndex.Closure ⟨.B (m + 1) q, hv⟩)
        ((show ValidLieTypeIndex.characteristic ⟨.B (m + 1) q, hv⟩ = q.p from
          LieTypeIndex.characteristic_B (m + 1) q).trans hp)
        ((show ValidLieTypeIndex.fieldExponent ⟨.B (m + 1) q, hv⟩ = q.exponent from
          LieTypeIndex.fieldExponent_B (m + 1) q) ▸ q.exponent_pos))).trans
      ((CFSG.ClassicalModels.derivedCentralQuotientEquivCenterQuotient _).trans
        ((QuotientGroup.congr _ _
            (CFSG.LieType.Universal.Symplectic.equivStatedSp (m + 1) _)
            (Subgroup.map_center_eq _)).trans
          (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv (m + 1) _)))

open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr
  statedProjEquivMapMk)
open CFSG.Assembly.RankThreeEven (projSp)

def typeBGroupEquivProjSp (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p = 2) (hr : 3 ≤ r) [Fact q.p.Prime] :
    ValidLieTypeIndex.Group ⟨.B r q, hv⟩ ≃* projSp r (GaloisField q.p q.exponent) :=
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B r q, hv⟩
  let φ : ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) ≃+* GaloisField q.p q.exponent :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField _ q.p q.exponent q.exponent_pos (by
      rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
        show ValidLieTypeIndex.characteristic ⟨.B r q, hv⟩ = q.p from
          LieTypeIndex.characteristic_B r q,
        show ValidLieTypeIndex.fieldExponent ⟨.B r q, hv⟩ = q.exponent from
          LieTypeIndex.fieldExponent_B r q])
  (typeBGroupEquivStatedProj r q hv hp hr).trans
    ((statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ r)
      (glCongr_statedScalars φ)).trans (statedProjEquivMapMk (StatedSp r _)))

theorem nonempty_typeBGroupEquivProjSp (r f : ℕ) (hr : 3 ≤ r) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (hp : q.p = 2) (he : q.exponent = f) :
    Nonempty (ValidLieTypeIndex.Group ⟨.B r q, hv⟩ ≃* projSp r (GaloisField 2 f)) := by
  rcases q with ⟨p, e, hpp, hep⟩
  dsimp only at hp he
  subst hp
  subst he
  have : Fact (Nat.Prime 2) := ⟨hpp⟩
  exact ⟨typeBGroupEquivProjSp r ⟨2, e, hpp, hep⟩ hv rfl hr⟩

end CFSG.RankThree.PartTwo.Census.Carrier.SpinB

namespace CFSG.RankThree.PartTwo.Census

open TauCeti CFSG.Assembly.LowTwoRank

theorem bridgeSp8Two : BridgeSp8Two := fun q hv hp he =>
  Carrier.SpinB.nonempty_typeBGroupEquivProjSp 4 1 (by norm_num) q hv hp he

theorem bridgeSp6Four : BridgeSp6Four := fun q hv hp he =>
  Carrier.SpinB.nonempty_typeBGroupEquivProjSp 3 2 le_rfl q hv hp he

theorem bridgeSp6Two : CFSG.RankThree.PartTwo.Sec4.Census.BridgeSp6Two := fun q hv hp he =>
  Carrier.SpinB.nonempty_typeBGroupEquivProjSp 3 1 le_rfl q hv hp he

theorem statedClassicalModel_typeB_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p = 2) (hr : 3 ≤ r) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    StatedClassicalModel G .PSp r q.p q.exponent := by
  refine ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_⟩,
    ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩), inferInstance,
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, ?_,
    ⟨e.trans (Carrier.SpinB.typeBGroupEquivStatedProj r q hv hp hr)⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder]

theorem catalogBridgeFor_B_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hr : 3 ≤ r) (hp : q.p = 2) : CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.B r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_typeB_even r q hv hp hr e⟩))

end CFSG.RankThree.PartTwo.Census
