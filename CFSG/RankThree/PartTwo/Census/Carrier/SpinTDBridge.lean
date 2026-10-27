module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDGroup
public import CFSG.LieType.Universal.IrreducibleQuadratic
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
import all TauCeti.Algebra.CharP.Frobenius.Fixed
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDTwist

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti TauCeti.TypeDSpinCarrier CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open SpinFrame

theorem exists_twist_root {L : Type} [Field L] [IsAlgClosed L] (θ : L →+* L) (S : Subfield L)
    [Finite S] (hS : ∀ x, x ∈ S ↔ θ x = x) : ∃ ω : L, ω ≠ θ ω ∧ θ (θ ω) = ω := by
  obtain ⟨b, c, hbc⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic S
  have hdeg : (Polynomial.C (1 : L) * Polynomial.X ^ 2 + Polynomial.C (b : L) * Polynomial.X +
      Polynomial.C (c : L)).degree ≠ 0 := by
    rw [Polynomial.degree_quadratic one_ne_zero]
    decide
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root _ hdeg
  have hroot : ω ^ 2 + (b : L) * ω + c = 0 := by
    simpa [Polynomial.IsRoot] using hω
  have hθb : θ b = b := (hS b).1 b.2
  have hθc : θ c = c := (hS c).1 c.2
  have hroot' : θ ω ^ 2 + (b : L) * θ ω + c = 0 := by
    have h := congrArg θ hroot
    rwa [map_add, map_add, map_mul, map_pow, hθb, hθc, map_zero] at h
  have hne : ω ≠ θ ω := by
    intro h
    have hmem : ω ∈ S := (hS ω).2 h.symm
    refine hbc ⟨ω, hmem⟩ (Subtype.ext ?_)
    simpa using hroot
  refine ⟨ω, hne, ?_⟩
  have hsum : ω + θ ω = -b := by
    have h : (ω - θ ω) * (ω + θ ω + b) = 0 := by linear_combination hroot - hroot'
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hne
    · linear_combination h1
  have h := congrArg θ hsum
  rw [map_add, map_neg, hθb] at h
  linear_combination h - hsum

theorem two_eq_zero_of_charP {L : Type} [Field L] {p : ℕ} [CharP L p] (hp : p = 2) :
    (2 : L) = 0 := by
  have h := CharP.cast_eq_zero L p
  rwa [hp, Nat.cast_ofNat] at h

theorem mem_fixedSubgroup_iff_orthPoints {m : ℕ} (hn : 4 ≤ m + 1) {L : Type} [Field L]
    {p : ℕ} [ExpChar L p] (k : ℕ) (h2 : (2 : L) = 0) (g : points (m + 1) hn L) :
    g ∈ fixedSubgroup ((graphAutPoints (m + 1) hn L).toMonoidHom.comp
        (frobenius (m + 1) hn p k L)) ↔
      (((orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) :
        Matrix (DI (m + 1)) (DI (m + 1)) L).map (iterateFrobenius L p k)).submatrix (tauM m)
          (tauM m) =
        ((orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) :
          Matrix (DI (m + 1)) (DI (m + 1)) L) := by
  have key : ((orthPoints (m + 1) hn L (graphAutPoints (m + 1) hn L
      (frobenius (m + 1) hn p k L g)) : GL (DI (m + 1)) L) :
        Matrix (DI (m + 1)) (DI (m + 1)) L) =
      (((orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) :
        Matrix (DI (m + 1)) (DI (m + 1)) L).map (iterateFrobenius L p k)).submatrix (tauM m)
          (tauM m) := by
    rw [orthPoints_graphAutPoints, orthPoints_frobenius]
    rfl
  rw [mem_fixedSubgroup, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h
    rw [← key, h]
  · intro h
    apply orthPoints_injective (m + 1) hn h2
    apply Units.ext
    rw [key, h]

theorem exists_typeTwistedDGroupEquivStatedProj (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (hp : q.p = 2) :
    ∃ b c : ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩),
      (∀ s, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩ ≃*
          StatedProj (StatedOmega
            (StatedQuadMinus r ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c))) := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hS : ∀ x, x ∈ ValidLieTypeIndex.fixedField ⟨.twistedD (m + 1) q, hv⟩ ↔
      iterateFrobenius (ValidLieTypeIndex.Closure ⟨.twistedD (m + 1) q, hv⟩)
        (ValidLieTypeIndex.characteristic ⟨.twistedD (m + 1) q, hv⟩)
        (ValidLieTypeIndex.fieldExponent ⟨.twistedD (m + 1) q, hv⟩) x = x := by
    intro x
    rw [ValidLieTypeIndex.mem_fixedField, iterateFrobenius_def,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.twistedD (m + 1) q, hv⟩
  obtain ⟨ω, hω, hθω⟩ := exists_twist_root _ _ hS
  have h2 : (2 : ValidLieTypeIndex.Closure ⟨.twistedD (m + 1) q, hv⟩) = 0 :=
    two_eq_zero_of_charP ((show ValidLieTypeIndex.characteristic ⟨.twistedD (m + 1) q, hv⟩ = q.p
      from LieTypeIndex.characteristic_twistedD (m + 1) q).trans hp)
  exact ⟨coefB _ _ hS hθω, coefC _ _ hS hθω, coef_irreducible _ _ hS hθω hω,
    ⟨dcqEquivTwisted hr _ _ hS hω hθω _
      (mem_fixedSubgroup_iff_orthPoints hr _ h2) h2⟩⟩

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD

namespace CFSG.RankThree.PartTwo.Census

open TauCeti CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_typeTwistedD_even (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (hp : q.p = 2) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) :
    StatedClassicalModel G .POmegaMinus r q.p q.exponent := by
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨b, c, hbc, ⟨φ⟩⟩ := Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj r q hv hp
  refine ⟨⟨q.prime_p, q.exponent_pos, hr⟩,
    ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩), inferInstance,
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, ?_, b, c, hbc, ⟨e.trans φ⟩⟩
  rw [ValidLieTypeIndex.card_fixedField]
  simp [ValidLieTypeIndex.fieldOrder]

theorem bridgeOmega8MinusTwo : BridgeOmega8MinusTwo := fun q hv hp he => by
  have h := statedClassicalModel_typeTwistedD_even 4 q hv hp (MulEquiv.refl _)
  rw [hp, he] at h
  exact CFSG.RankThree.PartOne.projOmegaMinus_of_statedClassicalModel h

theorem catalogBridgeFor_twistedD_even (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (hp : q.p = 2) :
    CFSG.QuasithinUnique.B1.CatalogBridgeFor (.lie ⟨.twistedD r q, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_typeTwistedD_even r q hv hp e⟩))

end CFSG.RankThree.PartTwo.Census
