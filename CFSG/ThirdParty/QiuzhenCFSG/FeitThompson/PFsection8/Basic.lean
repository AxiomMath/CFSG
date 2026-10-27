module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.theorem_16_II
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 8: basic notation

This file records book-facing vocabulary for Peterfalvi, Section 8,
`Structure of a Minimal Simple Group of Odd Order`.

The heavy structural notation from BG Section 16 is reused whenever possible,
and a few PF-specific bundles are packaged here so that the numbered
statements stay readable.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section8

universe u

/-- Transport a class function on an ambient subgroup to the same subgroup viewed inside
an overgroup. -/
@[expose] public def classFunctionOnSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G)
    (θ : Section1.ClassFunction MF) :
    Section1.ClassFunction (MF.subgroupOf M) :=
  fun x => θ ⟨((x : M) : G), Subgroup.mem_subgroupOf.mp x.property⟩

/-- The source conclusion `I(θ) ∩ U ≤ U₁` from PF `(8.2)(c)`, with inertia
taken inside the group `M`. -/
@[expose] public def inertiaIntersectionInComplement
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 : Subgroup G)
    (θ : Section1.ClassFunction MF) : Prop :=
  ∀ hMFNormal : (MF.subgroupOf M).Normal,
    letI : (MF.subgroupOf M).Normal := hMFNormal
    let θM : Section1.ClassFunction (MF.subgroupOf M) :=
      classFunctionOnSubgroupOf M MF θ
    ((Section1.inertiaSubgroup (MF.subgroupOf M) θM).map M.subtype ⊓ U) ≤ U1

/-- The data from PF Definition `(8.1)`: `M` is of type `F` with `H = M_F`. -/
@[expose] public def typeFData
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 U0 : Subgroup G) : Prop :=
  IsSolvable M ∧
    Odd (Nat.card M) ∧
    section16MFSubgroup M MF ∧
    ⊥ < MF ∧
    MF < M ∧
    U ≠ ⊥ ∧
    section12ComplementIn M MF U ∧
    U1 ≤ U ∧
    IsMulCommutative U1 ∧
    section10NormalIn U1 U ∧
    (∀ x : G, x ∈ MF → x ≠ 1 → elementCentralizerIn U x ≤ U1) ∧
    U0 ≤ U ∧
    Monoid.exponent U0 = Monoid.exponent U ∧
    section12FrobeniusJoinWithKernel MF U0

/-- BG16-aligned Type `P` common data used by later PF sections. This is intentionally
stronger/coarser than the literal PF Definition `(8.4)`; the source-facing definition is
`typePDefinitionData`. -/
@[expose] public def typePData
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) : Prop :=
  section16MFSubgroup M MF ∧ section16TypeCommon M MF U W1 W2

/-- The source-facing data from PF Definition `(8.4)`: `M` is of type `P` with
`H = M_F`, `M' = [M,M]`, and `M'' = [M',M']`. -/
@[expose] public def typePDefinitionData
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) : Prop :=
  section16MFSubgroup M MF ∧
    IsCyclic W1 ∧
    W1 ≠ ⊥ ∧
    section16HallSubgroupOf W1 M ∧
    section12ComplementIn M (ambientDerivedSubgroup M) W1 ∧
    U ≤ ambientDerivedSubgroup M ∧
    Group.IsNilpotent U ∧
    W1 ≤ subgroupNormalizerIn M (U : Set G) ∧
    section12ComplementIn (ambientDerivedSubgroup M) MF U ∧
    ¬ IsCyclic MF ∧
    section16SecondDerivedSubgroup M ≤ MF ⊔ subgroupCentralizerIn M MF ∧
    MF ⊔ subgroupCentralizerIn M MF = section8FittingSubgroup M ∧
    section8FittingSubgroup M ≤ ambientDerivedSubgroup M ∧
    W2 ≤ MF ⊓ section16SecondDerivedSubgroup M ∧
    IsCyclic W2 ∧
    W2 ≠ ⊥ ∧
    (∀ x : G, x ∈ W1 → x ≠ 1 →
      elementCentralizerIn (ambientDerivedSubgroup M) x = W2) ∧
    ∀ X : Set G,
      X.Nonempty →
        X ⊆ section16HatW W1 W2 →
          Subgroup.normalizer X = W1 ⊔ W2

/-- Source-facing PF Definition `(8.3)`: `M` is of Type I.

The project README records the standard correction to `(8.3.c)`: the cyclic
`p'`-core condition is imposed on `H = M_F`, not on all of `M`. -/
@[expose] public def typeIDefinitionData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  ∃ U U1 U0 : Subgroup G,
    typeFData M MF U U1 U0 ∧
      (section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (IsMulCommutative MF ∧ groupRank MF = 2) ∨
          ((∀ p : Nat.Primes, p ∈ subgroupPrimeSet MF →
            Monoid.exponent U ∣ p.val - 1) ∧
            ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
              IsCyclic (section10PPrimeCore p MF)))

/-- The common source condition `(8.6)(a)` for Types II, III and IV. -/
@[expose] public def typeIIToIVSourceCondition
    {G : Type u} [Group G] [Finite G]
    (M U W1 : Subgroup G) : Prop :=
  U ≠ ⊥ ∧
    section16HasPrimeOrder W1 ∧
    section16TISubset (section16NonidentityElements (section8FittingSubgroup M : Set G))

/-- Source-facing PF Definition `(8.6)`, Type II. -/
@[expose] public def typeIIDefinitionData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  ∃ U W1 W2 U1 U0 : Subgroup G,
    typePDefinitionData M MF U W1 W2 ∧
      typeIIToIVSourceCondition M U W1 ∧
      IsMulCommutative U ∧
      ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
      typeFData (ambientDerivedSubgroup M) MF U U1 U0

/-- Source-facing PF Definition `(8.6)`, Type III. -/
@[expose] public def typeIIIDefinitionData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  ∃ U W1 W2 : Subgroup G,
    typePDefinitionData M MF U W1 W2 ∧
      typeIIToIVSourceCondition M U W1 ∧
      IsMulCommutative U ∧
      Subgroup.normalizer (U : Set G) ≤ M

/-- Source-facing PF Definition `(8.6)`, Type IV. -/
@[expose] public def typeIVDefinitionData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  ∃ U W1 W2 : Subgroup G,
    typePDefinitionData M MF U W1 W2 ∧
      typeIIToIVSourceCondition M U W1 ∧
      ¬ IsMulCommutative U ∧
      Subgroup.normalizer (U : Set G) ≤ M

/-- Source-facing PF Definition `(8.7)`, Type V. -/
@[expose] public def typeVDefinitionData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G) : Prop :=
  ∃ U W1 W2 : Subgroup G,
    typePDefinitionData M MF U W1 W2 ∧
      U = ⊥ ∧
      (section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))

/-- Source-facing PF `(8.8)(b)` package. -/
@[expose] public def theorem_8_8_source_case_b_data
    {G : Type u} [Group G] [Finite G]
    (W W1 W2 S T SF TF : Subgroup G) : Prop :=
  section12InternalDirectProduct W1 W2 W ∧
    IsCyclic W ∧
    W1 ≠ ⊥ ∧
    W2 ≠ ⊥ ∧
    (∀ W0 : Set G,
      W0.Nonempty →
        W0 ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) →
          Subgroup.normalizer W0 = W) ∧
    S ∈ section9MaximalSubgroups G ∧
    T ∈ section9MaximalSubgroups G ∧
    section16MFSubgroup S SF ∧
    section16MFSubgroup T TF ∧
    S = ambientDerivedSubgroup S ⊔ W1 ∧
    T = ambientDerivedSubgroup T ⊔ W2 ∧
    Disjoint (ambientDerivedSubgroup S) W1 ∧
    Disjoint (ambientDerivedSubgroup T) W2 ∧
    S ⊓ T = W ∧
    (typeIIDefinitionData S SF ∨ typeIIDefinitionData T TF) ∧
    (typeIIDefinitionData S SF ∨ typeIIIDefinitionData S SF ∨
      typeIVDefinitionData S SF ∨ typeVDefinitionData S SF) ∧
    (typeIIDefinitionData T TF ∨ typeIIIDefinitionData T TF ∨
      typeIVDefinitionData T TF ∨ typeVDefinitionData T TF) ∧
    ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      (∃ g : G, M = S.conjBy g) ∨
        (∃ g : G, M = T.conjBy g) ∨
          ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF

/-- BG16-aligned strengthening of PF `(8.8)(b)` used by downstream PF13/final
wiring. The literal PF statement is `theorem_8_8_source_case_b_data`. -/
@[expose] public def theorem_8_8_case_b_data
    {G : Type u} [Group G] [Finite G]
    (W W1 W2 S T SF TF : Subgroup G) : Prop :=
  section12InternalDirectProduct W1 W2 W ∧
    IsCyclic W ∧
    W1 ≠ ⊥ ∧
    W2 ≠ ⊥ ∧
    (∀ W0 : Set G,
      W0.Nonempty →
        W0 ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) →
          Subgroup.normalizer W0 = W) ∧
    S ∈ section9MaximalSubgroups G ∧
    T ∈ section9MaximalSubgroups G ∧
    section16MFSubgroup S SF ∧
    section16MFSubgroup T TF ∧
    ¬ section16TypeI S SF ∧
    ¬ section16TypeI T TF ∧
    S = W1 ⊔ ambientDerivedSubgroup S ∧
    T = W2 ⊔ ambientDerivedSubgroup T ∧
    ambientDerivedSubgroup S ⊓ W1 = ⊥ ∧
    ambientDerivedSubgroup T ⊓ W2 = ⊥ ∧
    W2 ≤ section16SecondDerivedSubgroup S ∧
    W1 ≤ section16SecondDerivedSubgroup T ∧
    S ⊓ T = W ∧
    (∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      (∃ g : G, M = S.conjBy g) ∨
        (∃ g : G, M = T.conjBy g) ∨
          ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ section16TypeI M MF) ∧
    (section16TypeII S SF ∨ section16TypeII T TF) ∧
    (section16TypeII S SF ∨ section16TypeIII S SF ∨
      section16TypeIV S SF ∨ section16TypeV S SF) ∧
    (section16TypeII T TF ∨ section16TypeIII T TF ∨
      section16TypeIV T TF ∨ section16TypeV T TF) ∧
    ∃ U V : Subgroup G,
      section16TypeCommon S SF U W1 W2 ∧
        section16TypeCommon T TF V W2 W1

/-- The notation `M_s` from PF `(8.10)`. -/
@[expose] public def msChoice
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G) : Prop :=
  ((section16TypeI M MF ∨ section16TypeII M MF ∨ section16TypeV M MF) ∧ Ms = MF) ∨
    ((section16TypeIII M MF ∨ section16TypeIV M MF) ∧
      Ms = ambientDerivedSubgroup M)

/-- The set `A_1(M) = M_s#` from PF `(8.10)`. -/
@[expose] public def a1Set
    {G : Type u} [Group G]
    (Ms : Subgroup G) : Set G :=
  section16NonidentityElements (Ms : Set G)

/-- A book-facing package for the PF `(8.10)` notation `M_s`, `A(M)`, `A_0(M)`. -/
@[expose] public def notation_8_10_data
    {G : Type u} [Group G] [Finite G]
    (M MF K U Ms : Subgroup G)
    (A A0 : Set G) : Prop :=
  msChoice M MF Ms ∧
    (A = section16ASet M U ∨ A = a1Set Ms) ∧
    (A0 = section16AZeroSet M K ∨ A0 = A)

/-- The literal source convention for `M_s` in PF `(8.10)`, using the PF
Section 8 definitions without adding mutual-exclusion data.

This matches the displayed Type I/II/V versus Type III/IV cases. -/
@[expose] public def msChoiceSourceLiteral
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G) : Prop :=
  ((typeIDefinitionData M MF ∨ typeIIDefinitionData M MF ∨
      typeVDefinitionData M MF) ∧ Ms = MF) ∨
    ((typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF) ∧
      Ms = ambientDerivedSubgroup M)

/-- Proof-support strengthening of the PF `(8.10)` convention for `M_s`.

The five PF types are recorded as an exclusive case split so the value of
`M_s` is determined before mutual exclusivity of the source type predicates is
available as a theorem. This is stronger than the literal displayed notation. -/
@[expose] public def msChoiceSource
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G) : Prop :=
  (typeIDefinitionData M MF ∧
      ¬ typeIIDefinitionData M MF ∧
      ¬ typeIIIDefinitionData M MF ∧
      ¬ typeIVDefinitionData M MF ∧
      ¬ typeVDefinitionData M MF ∧
      Ms = MF) ∨
    (¬ typeIDefinitionData M MF ∧
      typeIIDefinitionData M MF ∧
      ¬ typeIIIDefinitionData M MF ∧
      ¬ typeIVDefinitionData M MF ∧
      ¬ typeVDefinitionData M MF ∧
      Ms = MF) ∨
    (¬ typeIDefinitionData M MF ∧
      ¬ typeIIDefinitionData M MF ∧
      typeIIIDefinitionData M MF ∧
      ¬ typeIVDefinitionData M MF ∧
      ¬ typeVDefinitionData M MF ∧
      Ms = ambientDerivedSubgroup M) ∨
    (¬ typeIDefinitionData M MF ∧
      ¬ typeIIDefinitionData M MF ∧
      ¬ typeIIIDefinitionData M MF ∧
      typeIVDefinitionData M MF ∧
      ¬ typeVDefinitionData M MF ∧
      Ms = ambientDerivedSubgroup M) ∨
    (¬ typeIDefinitionData M MF ∧
      ¬ typeIIDefinitionData M MF ∧
      ¬ typeIIIDefinitionData M MF ∧
      ¬ typeIVDefinitionData M MF ∧
      typeVDefinitionData M MF ∧
      Ms = MF)

public theorem msChoiceSource.to_literal
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G} :
    msChoiceSource M MF Ms → msChoiceSourceLiteral M MF Ms := by
  intro h
  rcases h with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨hTypeI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs⟩
    exact Or.inl ⟨Or.inl hTypeI, hMs⟩
  · rcases hII with ⟨_hnotI, hTypeII, _hnotIII, _hnotIV, _hnotV, hMs⟩
    exact Or.inl ⟨Or.inr (Or.inl hTypeII), hMs⟩
  · rcases hIII with ⟨_hnotI, _hnotII, hTypeIII, _hnotIV, _hnotV, hMs⟩
    exact Or.inr ⟨Or.inl hTypeIII, hMs⟩
  · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, hTypeIV, _hnotV, hMs⟩
    exact Or.inr ⟨Or.inr hTypeIV, hMs⟩
  · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, hTypeV, hMs⟩
    exact Or.inl ⟨Or.inr (Or.inr hTypeV), hMs⟩

/-- In the Type-I branch of the strengthened PF `(8.10)` source convention,
the selected subgroup `M_s` is the Frobenius kernel `M_F`. -/
public theorem msChoiceSource_eq_mf_of_typeI
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hTypeI : typeIDefinitionData M MF) :
    Ms = MF := by
  rcases hChoice with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs⟩
    exact hMs
  · exact False.elim (hII.1 hTypeI)
  · exact False.elim (hIII.1 hTypeI)
  · exact False.elim (hIV.1 hTypeI)
  · exact False.elim (hV.1 hTypeI)

/-- In the Type-II branch of the strengthened PF `(8.10)` source convention,
the selected subgroup `M_s` is the Frobenius kernel `M_F`. -/
public theorem msChoiceSource_eq_mf_of_typeII
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hTypeII : typeIIDefinitionData M MF) :
    Ms = MF := by
  rcases hChoice with hI | hII | hIII | hIV | hV
  · exact False.elim (hI.2.1 hTypeII)
  · exact hII.2.2.2.2.2
  · exact False.elim (hIII.2.1 hTypeII)
  · exact False.elim (hIV.2.1 hTypeII)
  · exact False.elim (hV.2.1 hTypeII)

/-- If the Type-P complement inside `M'` is trivial, then the Frobenius kernel
`M_F` is all of `M'`. -/
public theorem typePDefinitionData_mf_eq_ambientDerived_of_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hU : U = ⊥) :
    MF = ambientDerivedSubgroup M := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hCompM, _hUle, _hUnil,
      _hW1norm, hCompD, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLe, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hHatW⟩
  have hDer : ambientDerivedSubgroup M = MF ⊔ U := hCompD.2.2.1
  rw [hU, sup_bot_eq] at hDer
  exact hDer.symm

/-- In the PF source Type-V case, `U = 1`, hence `M_F = M'`. -/
public theorem typeVDefinitionData_mf_eq_ambientDerived
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hTypeV : typeVDefinitionData M MF) :
    MF = ambientDerivedSubgroup M := by
  rcases hTypeV with ⟨U, W1, W2, hP, hU, _halt⟩
  exact typePDefinitionData_mf_eq_ambientDerived_of_eq_bot hP hU


/-- If a Type-P source witness with `U = 1` gives `M_F = M'`, then any
complement to `M_F` inside `M'` is trivial. -/
public theorem typePDefinitionData_bot_complement_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hcomp : section12ComplementIn (ambientDerivedSubgroup M) MF U) :
    U = ⊥ := by
  rcases hcomp with ⟨_hMFleD, hUleD, _hDsup, hdisj⟩
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    typePDefinitionData_mf_eq_ambientDerived_of_eq_bot hPbot rfl
  apply le_antisymm ?_ bot_le
  intro x hxU
  have hxMF : x ∈ MF := by
    simpa [hMF_eq_D] using hUleD hxU
  exact hdisj.le_bot ⟨hxMF, hxU⟩

/-- A source Type-P witness with trivial complement excludes Type II. -/
public theorem not_typeIIDefinitionData_of_typeP_bot
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2) :
    ¬ typeIIDefinitionData M MF := by
  rintro ⟨U, _W1, _W2, _U1, _U0, hP, hExtra, _hUcomm, _hUnorm, _hF⟩
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD, _hUnil,
      _hW1norm, hCompMFU, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hHatW⟩
  exact hExtra.1 (typePDefinitionData_bot_complement_eq_bot hPbot hCompMFU)

/-- A source Type-P witness with trivial complement excludes Type III. -/
public theorem not_typeIIIDefinitionData_of_typeP_bot
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2) :
    ¬ typeIIIDefinitionData M MF := by
  rintro ⟨U, _W1, _W2, hP, hExtra, _hUcomm, _hUnorm⟩
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD, _hUnil,
      _hW1norm, hCompMFU, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hHatW⟩
  exact hExtra.1 (typePDefinitionData_bot_complement_eq_bot hPbot hCompMFU)

/-- A source Type-P witness with trivial complement excludes Type IV. -/
public theorem not_typeIVDefinitionData_of_typeP_bot
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2) :
    ¬ typeIVDefinitionData M MF := by
  rintro ⟨U, _W1, _W2, hP, hExtra, _hUncomm, _hUnorm⟩
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD, _hUnil,
      _hW1norm, hCompMFU, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hHatW⟩
  exact hExtra.1 (typePDefinitionData_bot_complement_eq_bot hPbot hCompMFU)

/-- In the Type-V branch of the strengthened PF `(8.10)` source convention,
the selected subgroup `M_s` is the Frobenius kernel `M_F`. -/
public theorem msChoiceSource_eq_mf_of_typeV
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hTypeV : typeVDefinitionData M MF) :
    Ms = MF := by
  rcases hChoice with hI | hII | hIII | hIV | hV
  · exact False.elim (hI.2.2.2.2.1 hTypeV)
  · exact False.elim (hII.2.2.2.2.1 hTypeV)
  · exact False.elim (hIII.2.2.2.2.1 hTypeV)
  · exact False.elim (hIV.2.2.2.2.1 hTypeV)
  · exact hV.2.2.2.2.2

/-- In any late PF source case (Types III, IV, or V), the strengthened
`M_s` choice is `M'`.  For Type V this uses `U = 1`, so `M_F = M'`. -/
public theorem msChoiceSource_eq_ambientDerived_of_late
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hLate :
      typeIIIDefinitionData M MF ∨
        typeIVDefinitionData M MF ∨
          typeVDefinitionData M MF) :
    Ms = ambientDerivedSubgroup M := by
  rcases hLate with hIII | hLate
  · rcases hChoice with hI | hII | hIIIbranch | hIV | hV
    · exact False.elim (hI.2.2.1 hIII)
    · exact False.elim (hII.2.2.1 hIII)
    · exact hIIIbranch.2.2.2.2.2
    · exact False.elim (hIV.2.2.1 hIII)
    · exact False.elim (hV.2.2.1 hIII)
  · rcases hLate with hIVsrc | hVsrc
    · rcases hChoice with hI | hII | hIIIbranch | hIVbranch | hV
      · exact False.elim (hI.2.2.2.1 hIVsrc)
      · exact False.elim (hII.2.2.2.1 hIVsrc)
      · exact False.elim (hIIIbranch.2.2.2.1 hIVsrc)
      · exact hIVbranch.2.2.2.2.2
      · exact False.elim (hV.2.2.2.1 hIVsrc)
    · rcases hChoice with hI | hII | hIIIbranch | hIVbranch | hVbranch
      · exact False.elim (hI.2.2.2.2.1 hVsrc)
      · exact False.elim (hII.2.2.2.2.1 hVsrc)
      · exact False.elim (hIIIbranch.2.2.2.2.1 hVsrc)
      · exact False.elim (hIVbranch.2.2.2.2.1 hVsrc)
      · exact hVbranch.2.2.2.2.2.trans
          (typeVDefinitionData_mf_eq_ambientDerived hVsrc)

/-- The union `⋃ x ∈ X#, C_C(x)#` used in PF `(8.10)`. -/
@[expose] public def section8CentralizerUnion
    {G : Type u} [Group G]
    (C X : Subgroup G) : Set G :=
  {y | ∃ x : G, x ∈ section16NonidentityElements (X : Set G) ∧
    y ∈ section16NonidentityElements (elementCentralizerIn C x : Set G)}


/-- The literal source notation from PF `(8.10)`: `M_s`, `A_1(M)`, `A(M)`,
and `A_0(M)`, including the Type I / Type `P` case split. -/
@[expose] public def notation_8_10_literal_source_data
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 : Set G) : Prop :=
  M ∈ section9MaximalSubgroups G ∧
    section16MFSubgroup M MF ∧
    msChoiceSourceLiteral M MF Ms ∧
    A1 = a1Set Ms ∧
    ((typeIDefinitionData M MF ∧
        A = section8CentralizerUnion M MF ∧
        A0 = A) ∨
      (∃ U W1 W2 : Subgroup G,
        typePDefinitionData M MF U W1 W2 ∧
          (typeIIDefinitionData M MF ∨ typeIIIDefinitionData M MF ∨
            typeIVDefinitionData M MF ∨ typeVDefinitionData M MF) ∧
          A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms ∧
          A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) ∧
          ((typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
              typeVDefinitionData M MF) →
            A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
              A = A1)))

/-- Proof-support strengthening of PF `(8.10)`.

This uses `msChoiceSource`, the exclusive Type I/II/III/IV/V split used by
downstream Section 8 proofs to connect the source type predicates with the
BG16-aligned type predicates. -/
@[expose] public def notation_8_10_source_data
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 : Set G) : Prop :=
  M ∈ section9MaximalSubgroups G ∧
    section16MFSubgroup M MF ∧
    msChoiceSource M MF Ms ∧
    A1 = a1Set Ms ∧
    ((typeIDefinitionData M MF ∧
        A = section8CentralizerUnion M MF ∧
        A0 = A) ∨
      (∃ U W1 W2 : Subgroup G,
        typePDefinitionData M MF U W1 W2 ∧
          (typeIIDefinitionData M MF ∨ typeIIIDefinitionData M MF ∨
            typeIVDefinitionData M MF ∨ typeVDefinitionData M MF) ∧
          A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms ∧
          A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) ∧
          ((typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
              typeVDefinitionData M MF) →
            A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
              A = A1)))

public theorem notation_8_10_source_data.to_literal
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G} :
    notation_8_10_source_data M MF Ms A A0 A1 →
      notation_8_10_literal_source_data M MF Ms A A0 A1 := by
  intro h
  rcases h with ⟨hM, hMF, hMs, hA1, hcases⟩
  exact ⟨hM, hMF, hMs.to_literal, hA1, hcases⟩

public instance instCoeOutNotation_8_10_source_dataLiteral
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G} :
    CoeOut (notation_8_10_source_data M MF Ms A A0 A1)
      (notation_8_10_literal_source_data M MF Ms A A0 A1) where
  coe h := h.to_literal

public theorem notation_8_10_source_data_ms_eq_ambientDerived_of_late
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hLate :
      typeIIIDefinitionData M MF ∨
        typeIVDefinitionData M MF ∨
          typeVDefinitionData M MF) :
    Ms = ambientDerivedSubgroup M :=
  msChoiceSource_eq_ambientDerived_of_late hNotation.2.2.1 hLate

/-- The Type `P` witness actually used by the PF `(8.10)` source notation.

The public `(8.15)` Hypothesis `(4.6)` conclusion must be tied to this
chosen Definition `(8.4)` data, since `A₀(M)` contains the corresponding
`V^M` term. -/
@[expose] public def notation_8_10_source_typeP_witness
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 : Set G)
    (U W1 W2 : Subgroup G) : Prop :=
  typePDefinitionData M MF U W1 W2 ∧
    (typeIIDefinitionData M MF ∨ typeIIIDefinitionData M MF ∨
      typeIVDefinitionData M MF ∨ typeVDefinitionData M MF) ∧
    A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms ∧
    A0 = A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) ∧
    ((typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
        typeVDefinitionData M MF) →
      A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
        A = A1)

/-- The membership part of the PF `(8.10)` source notation for Type I/II cases.
This is kept separate from `notation_8_10_source_data` so later source packages
can request the exact `A(M)` membership bridge they need without changing older
statement wrappers. -/
@[expose] public def notation_8_10_source_membership_data
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G)
    (A : Set G) : Prop :=
  (∀ x : G, typeIDefinitionData M MF →
    x ∈ section8CentralizerUnion M MF → x ∈ A) ∧
  (∀ x : G, typeIIDefinitionData M MF →
    x ∈ section8CentralizerUnion (ambientDerivedSubgroup M) MF → x ∈ A)

public theorem notation_8_10_source_membership_data_of_source_data
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G} :
    notation_8_10_source_data M MF Ms A A0 A1 →
      notation_8_10_source_membership_data M MF A := by
  intro h
  rcases h with ⟨_hM, _hMF, hMs, _hA1, hcases⟩
  constructor
  · intro x hTypeI hx
    rcases hcases with hI | hP
    · rcases hI with ⟨_hTypeI', hA, _hA0⟩
      rw [hA]
      exact hx
    · exfalso
      rcases hP with ⟨_U, _W1, _W2, _hP, htypeP, _hA, _hA0, _hLate⟩
      rcases hMs with hMsI | hMsII | hMsIII | hMsIV | hMsV
      · rcases hMsI with ⟨_hI, hnotII, hnotIII, hnotIV, hnotV, _hMs⟩
        rcases htypeP with hII | hIII | hIV | hV
        · exact hnotII hII
        · exact hnotIII hIII
        · exact hnotIV hIV
        · exact hnotV hV
      · exact hMsII.1 hTypeI
      · exact hMsIII.1 hTypeI
      · exact hMsIV.1 hTypeI
      · exact hMsV.1 hTypeI
  · intro x hTypeII hx
    rcases hcases with hI | hP
    · exfalso
      rcases hI with ⟨hTypeI, _hA, _hA0⟩
      rcases hMs with hMsI | hMsII | hMsIII | hMsIV | hMsV
      · exact hMsI.2.1 hTypeII
      · exact hMsII.1 hTypeI
      · exact hMsIII.1 hTypeI
      · exact hMsIV.1 hTypeI
      · exact hMsV.1 hTypeI
    · rcases hP with ⟨_U, _W1, _W2, _hP, _htypeP, hA, _hA0, _hLate⟩
      have hMs_eq : Ms = MF := by
        rcases hMs with hMsI | hMsII | hMsIII | hMsIV | hMsV
        · exact False.elim (hMsI.2.1 hTypeII)
        · exact hMsII.2.2.2.2.2
        · exact False.elim (hMsIII.2.1 hTypeII)
        · exact False.elim (hMsIV.2.1 hTypeII)
        · exact False.elim (hMsV.2.1 hTypeII)
      rw [hA, hMs_eq]
      exact hx

/-- A semidirect-product assertion in the ambient subgroup language. -/
@[expose] public def section8SemidirectProductIn
    {G : Type u} [Group G]
    (H K L : Subgroup G) : Prop :=
  section12ComplementIn H K L ∧
    ∃ _hKH : K ≤ H, (K.subgroupOf H).Normal

/-- `H` is a Frobenius kernel in `M`, with some complement. -/
@[expose] public def section8FrobeniusGroupWithKernel
    {G : Type u} [Group G]
    (M H : Subgroup G) : Prop :=
  ∃ U : Subgroup G, section12ComplementIn M H U ∧ section12FrobeniusJoinWithKernel H U

/-- The source data from PF `(8.12)`: the Type I/II hypotheses and the
appropriate complement `U`.

The complement is tied to the actual source witness: for Type I it comes from
the Type `F` data for `M`, while for Type II it comes from the Type `F` data
for `M'`. -/
@[expose] public def theorem_8_12_source_data
    {G : Type u} [Group G] [Finite G]
    (M MF U Ms : Subgroup G)
    (A A0 A1 : Set G) : Prop :=
  notation_8_10_source_data M MF Ms A A0 A1 ∧
    (((∃ U1 U0 : Subgroup G,
        typeFData M MF U U1 U0 ∧
          (section16TISubset (section16NonidentityElements (MF : Set G)) ∨
            (IsMulCommutative MF ∧ groupRank MF = 2) ∨
              ((∀ p : Nat.Primes, p ∈ subgroupPrimeSet MF →
                Monoid.exponent U ∣ p.val - 1) ∧
                ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
                  IsCyclic (section10PPrimeCore p MF)))) ∧
        A = section8CentralizerUnion M MF ∧
        A1 = a1Set MF) ∨
      ((∃ W1 W2 U1 U0 : Subgroup G,
        typePDefinitionData M MF U W1 W2 ∧
          typeIIToIVSourceCondition M U W1 ∧
          IsMulCommutative U ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
        typeFData (ambientDerivedSubgroup M) MF U U1 U0) ∧
        A = section8CentralizerUnion (ambientDerivedSubgroup M) MF ∧
        A1 = a1Set MF))

/-- The literal conclusions of PF `(8.12)`. -/
@[expose] public def theorem_8_12_source_conclusion
    {G : Type u} [Group G] [Finite G]
    (M MF U : Subgroup G)
    (A A1 : Set G) : Prop :=
  section16HasAbelianSylowRankAtMostTwo U ∧
    (∀ X : Set G, X.Nonempty →
      X ⊆ section16NonidentityElements (U : Set G) →
        section16CentralizerInSet MF X ≠ ⊥ →
          section9MaximalSubgroupsContaining (Subgroup.centralizer X) = {M}) ∧
    section16TISubset (A \ A1)

/-- The set `D = {x ∈ X | C_G(x) is not contained in M}` from PF `(8.13)`. -/
@[expose] public def section8DSet
    {G : Type u} [Group G]
    (M : Subgroup G) (X : Set G) : Set G :=
  {x | x ∈ X ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}

/-- The detailed source conclusions in PF `(8.13)(c)` for the maximal subgroup
`L` containing `C_G(x)`. -/
@[expose] public def supportConclusionDataSource
    {G : Type u} [Group G] [Finite G]
    (M MF _X : Subgroup G)
    (Xset : Set G)
    (x : G) (L LF : Subgroup G) : Prop :=
  L ∈ section9MaximalSubgroups G ∧
    section16MFSubgroup L LF ∧
    section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {L} ∧
    section8SemidirectProductIn L LF (M ⊓ L) ∧
    section8SemidirectProductIn (Subgroup.centralizer ({x} : Set G))
      (elementCentralizerIn LF x) (elementCentralizerIn M x) ∧
    (∀ y : G, y ∈ Xset →
      Nat.Coprime (Nat.card LF) (Nat.card (elementCentralizerIn M y))) ∧
    ((typeIDefinitionData L LF ∧
        x ∈ section8CentralizerUnion L LF \ a1Set LF) ∨
      (typeIIDefinitionData L LF ∧
        x ∈ section8CentralizerUnion (ambientDerivedSubgroup L) LF \ a1Set LF ∧
          section8FrobeniusGroupWithKernel M MF))


/-- The support relation from PF `(8.14)`: `L` is maximal and contains
`C_G(x)` for some `x ∈ D`. -/
@[expose] public def supportsSubgroupSource
    {G : Type u} [Group G] [Finite G]
    (_M L : Subgroup G)
    (D : Set G) : Prop :=
  L ∈ section9MaximalSubgroups G ∧
    ∃ x : G, x ∈ D ∧ Subgroup.centralizer ({x} : Set G) ≤ L


/-- The literal PF `(8.14)` notation of `R_M(x)` and the associated tilde sets
for one fixed maximal subgroup `M`.

For `x ∈ D`, the statement includes the unique maximal subgroup supporting
`C_G(x)` from `(8.13)` and identifies this local `R_M(x)` with `C_{L_F}(x)` for that
supporting subgroup. -/
@[expose] public def notation_8_14_source_data
    {G : Type u} [Group G] [Finite G]
    (_M : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G) : Prop :=
  A1 ⊆ A ∧
    A ⊆ A0 ∧
    D = section8DSet _M A0 ∧
    (∀ x : G, x ∈ A0 \ D → R x = ⊥) ∧
    (∀ x : G, x ∈ D →
      ∃! L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G))) ∧
    (∀ x : G, x ∈ D →
      ∀ L LF : Subgroup G,
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {L} →
          section16MFSubgroup L LF →
            R x = elementCentralizerIn LF x) ∧
    tildeA = {y | ∃ a : G, a ∈ A ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ} ∧
    tildeA0 = {y | ∃ a : G, a ∈ A0 ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ} ∧
    tildeA1 = {y | ∃ a : G, a ∈ A1 ∧ y ∈ section16ConjugatesOfSetBySet
      (section16LeftCosetSet a (R a)) Set.univ}

/-- Pull back an ambient subset to a subgroup carrier. -/
@[expose] public def section8SubgroupSetPreimage
    {G : Type u} [Group G]
    (M : Subgroup G) (A : Set G) : Set M :=
  {x : M | (x : G) ∈ A}

/-- The PF `(8.15)` carrier version of `A₀ = A ∪ V^M` for Type `P`.

This is deliberately separate from `Section4Scratch.a0Set`, whose Section 4
definition uses the larger set `W \ W₂`. -/
@[expose] public def section8CyclicA0Set
    {G : Type u} [Group G]
    (M W1 W2 : Subgroup G) (A : Set G) : Set M :=
  section8SubgroupSetPreimage M A ∪
    Section2.conjugateSet
      (Section3.cyclicTISet
        (W1.subgroupOf M) (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M))

/-- PF `(8.15)`'s Hypothesis `(4.6)` assertion for
`L = M`, `K = M'`, `A = A(M)`, `A₀ = A₀(M)`, and the given choice of `H`. -/
@[expose] public def section8Hypothesis46Source
    {G : Type u} [Group G] [Finite G]
    (M W1 W2 H : Subgroup G)
    (A A0 : Set G) : Prop :=
  section8SubgroupSetPreimage M A0 = section8CyclicA0Set M W1 W2 A ∧
  Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M)
      (H.subgroupOf M)
      (section8SubgroupSetPreimage M A) ∧
    A ⊆ A0

/-- `M_s` is contained in the kernel of a character of `M'`, expressed on the
derived subgroup carrier of `M`. -/
@[expose] public def section8MsInKernelOfDerivedCharacter
    {G : Type u} [Group G] [Finite G]
    (M Ms : Subgroup G)
    (θ : Section1.ClassFunction (derivedSubgroup M)) : Prop :=
  ∀ m : derivedSubgroup M, ((m : M) : G) ∈ Ms → θ m = θ 1

/-- The source antecedent for the PF `(8.15)` Hypothesis `(5.2)` clause. -/
@[expose] public def section8InducedNonkernelFamily
    {G : Type u} [Group G] [Finite G]
    (M Ms : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  S.Nonempty ∧
    (∀ χ : Section1.ClassFunction M, χ ∈ S →
      Section1.conjugateCharacter χ ∈ S) ∧
    ∀ χ : Section1.ClassFunction M, χ ∈ S →
      ∃ θ : Section1.ClassFunction (derivedSubgroup M),
        Section1.IsIrreducibleCharacterOnGroup θ ∧
          ¬ section8MsInKernelOfDerivedCharacter M Ms θ ∧
          χ = Section1.inducedCF (derivedSubgroup M) θ

/-- The full Section `(4.6)`/Dade-isometry package needed to invoke
PF `(5.3)(b)` in the Type `P` branch of PF `(8.15)`.  The narrow
`section8Hypothesis46Source` records the source-facing `(4.6)` assertion; this
package records the extra proof infrastructure consumed by the formal PF5
theorem. -/
public structure section8Hypothesis52FullData
    {G : Type u} [Group G] [Finite G]
    (M Ms W1 W2 : Subgroup G)
    (A : Set G) : Type (u + 1) where
  W : Subgroup M
  I : Type u
  J : Type u
  instFintypeI : Fintype I
  instFintypeJ : Fintype J
  instDecidableEqI : DecidableEq I
  instDecidableEqJ : DecidableEq J
  i0 : I
  j0 : J
  omega : I → J → Section1.ClassFunction W
  sigmaM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M
  sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G
  piChar : I → J → Section1.ClassFunction M
  xChar : J → Section1.ClassFunction (derivedSubgroup M)
  deltaSign : J → ℂ
  tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G
  H_A : G → Subgroup G
  H_A0 : G → Subgroup G
  cyclicA0Hypothesis :
    Section2.hypothesis_2_2_statement
      (Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A))
      M H_A0
  tau_cyclicA0 :
    ∀ α : Section1.ClassFunction M,
      Section2.CFOn M
          (Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A))
          α →
        tau α =
          Section2.dadeTransform H_A0 cyclicA0Hypothesis.subset_L α
  sigma_agrees_cyclicTI :
    ∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
      ∀ x : M, ∀ hx : x ∈
        Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W,
          sigma α (x : G) =
            α ⟨x, Section3.cyclicTISet_subset
              (W1.subgroupOf M) (W2.subgroupOf M) W hx⟩
  W_eq : W = (W1 ⊔ W2).subgroupOf M
  fullHypothesis :
    letI : Fintype I := instFintypeI
    letI : Fintype J := instFintypeJ
    letI : DecidableEq I := instDecidableEqI
    letI : DecidableEq J := instDecidableEqJ
    Section4Scratch.hypothesis_4_6_supported_statement M
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      W
      (Ms.subgroupOf M)
      (section8SubgroupSetPreimage M A)
      i0 j0 omega sigmaM sigma piChar xChar deltaSign tau H_A

/-- Source package for the PF `(8.15)` appeal to `(1.5.e)` and `(5.3.b)`.
For each Type `P` witness selected by the PF `(8.10)` notation, it provides
the full Section `(4.6)` package used by the formal PF5 theorem. -/
@[expose] public def section8Hypothesis52Source
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 : Set G) : Prop :=
  ∀ U W1 W2 : Subgroup G,
    notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2 →
      Nonempty (section8Hypothesis52FullData M Ms W1 W2 A)

/-- Source data for PF `(8.15)`: `M` is maximal, the PF `(8.10)` and `(8.14)`
notation is fixed, and `A` is one of `A_0(M)`, `A(M)`, or `A_1(M)`. -/
@[expose] public def theorem_8_15_source_data
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (Abook A0 A1 A D tildeA tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G) : Prop :=
  notation_8_10_source_data M MF Ms Abook A0 A1 ∧
    notation_8_14_source_data M Abook A0 A1 D tildeA tildeA0 tildeA1 R ∧
    (A = A0 ∨ A = Abook ∨ A = A1)

/-- Proof-support strengthening of PF `(8.15)`.

The extra `section8Hypothesis52Source` field is the full Section `(4.6)` /
Dade-isometry package consumed by the formal proof of the Hypothesis `(5.2)`
conclusion.  It is not part of the bare `(8.10)`/`(8.14)` notation package. -/
@[expose] public def theorem_8_15_proof_data
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (Abook A0 A1 A D tildeA tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G) : Prop :=
  theorem_8_15_source_data M MF Ms Abook A0 A1 A D tildeA tildeA0 tildeA1 R ∧
    section8Hypothesis52Source M MF Ms Abook A0 A1

public theorem theorem_8_15_proof_data.to_source_data
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {Abook A0 A1 A D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G} :
    theorem_8_15_proof_data M MF Ms Abook A0 A1 A D tildeA tildeA0 tildeA1 R →
      theorem_8_15_source_data M MF Ms Abook A0 A1 A D tildeA tildeA0 tildeA1 R :=
  And.left


public instance instCoeOutTheorem_8_15_proof_dataSource
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {Abook A0 A1 A D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G} :
    CoeOut
      (theorem_8_15_proof_data M MF Ms Abook A0 A1 A D tildeA tildeA0 tildeA1 R)
      (theorem_8_15_source_data M MF Ms Abook A0 A1 A D tildeA tildeA0 tildeA1 R) where
  coe h := h.to_source_data

/-- Source notation data for PF `(8.18)`, fixing separate `(8.10)` and `(8.14)`
notation for the two non-conjugate maximal subgroups.  The functions `RS` and
`RT` are the local `R_S` and `R_T`; they are not a single global `R`. -/
@[expose] public def theorem_8_18_source_notation_data
    {G : Type u} [Group G] [Finite G]
    (S T SF TF SS TT : Subgroup G)
    (AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G)
    (AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G)
    (RS RT : G → Subgroup G) : Prop :=
  ¬ section16ConjugateSubgroupsIn ⊤ S T ∧
    notation_8_10_source_data S SF SS AS A0S A1S ∧
    notation_8_10_source_data T TF TT AT A0T A1T ∧
    notation_8_14_source_data S AS A0S A1S DS tildeAS tildeA0S tildeA1S RS ∧
    notation_8_14_source_data T AT A0T A1T DT tildeAT tildeA0T tildeA1T RT

/-- Proof-support strengthening of PF `(8.18)`.

The two `notation_8_10_source_membership_data` fields are derivable from the
exclusive `(8.10)` source package, but are kept here for older internal proof
lemmas. -/
@[expose] public def theorem_8_18_source_data
    {G : Type u} [Group G] [Finite G]
    (S T SF TF SS TT : Subgroup G)
    (AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G)
    (AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G)
    (RS RT : G → Subgroup G) : Prop :=
  ¬ section16ConjugateSubgroupsIn ⊤ S T ∧
    notation_8_10_source_data S SF SS AS A0S A1S ∧
    notation_8_10_source_membership_data S SF AS ∧
    notation_8_10_source_data T TF TT AT A0T A1T ∧
    notation_8_10_source_membership_data T TF AT ∧
    notation_8_14_source_data S AS A0S A1S DS tildeAS tildeA0S tildeA1S RS ∧
    notation_8_14_source_data T AT A0T A1T DT tildeAT tildeA0T tildeA1T RT

public theorem theorem_8_18_source_data.to_notation_data
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G} :
    theorem_8_18_source_data S T SF TF SS TT
        AS A0S A1S DS tildeAS tildeA0S tildeA1S
        AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT →
      theorem_8_18_source_notation_data S T SF TF SS TT
        AS A0S A1S DS tildeAS tildeA0S tildeA1S
        AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT := by
  intro h
  rcases h with ⟨hnc, hS10, _hSmem, hT10, _hTmem, hS14, hT14⟩
  exact ⟨hnc, hS10, hT10, hS14, hT14⟩

public theorem theorem_8_18_source_data_of_notation_data
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G} :
    theorem_8_18_source_notation_data S T SF TF SS TT
        AS A0S A1S DS tildeAS tildeA0S tildeA1S
        AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT →
      theorem_8_18_source_data S T SF TF SS TT
        AS A0S A1S DS tildeAS tildeA0S tildeA1S
        AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT := by
  intro h
  rcases h with ⟨hnc, hS10, hT10, hS14, hT14⟩
  exact ⟨hnc, hS10, notation_8_10_source_membership_data_of_source_data hS10,
    hT10, notation_8_10_source_membership_data_of_source_data hT10, hS14, hT14⟩

public instance instCoeOutTheorem_8_18_source_dataNotation
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G} :
    CoeOut
      (theorem_8_18_source_data S T SF TF SS TT
        AS A0S A1S DS tildeAS tildeA0S tildeA1S
        AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
      (theorem_8_18_source_notation_data S T SF TF SS TT
        AS A0S A1S DS tildeAS tildeA0S tildeA1S
        AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT) where
  coe h := h.to_notation_data

/-- A book-facing package for PF `(8.15)`. -/
@[expose] public def theorem_8_15_data
    {G : Type u} [Group G] [Finite G]
    (M MF K U Ms : Subgroup G)
    (A : Set G)
    (R : G → Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  notation_8_10_data M MF K U Ms A A ∧
    (∀ x : G, x ∈ A → section16TheoremDComplement M x (R x) ∨ R x = ⊥) ∧
    S.Nonempty

/-- A representative system of maximal subgroups, for PF `(8.17)`. -/
@[expose] public def representativeSystemData
    {G : Type u} [Group G] [Finite G]
    (Ms : List (Subgroup G)) : Prop :=
  section16MaximalConjugacyRepresentatives Ms

/-- Source-facing PF `(8.17)` notation package for one representative `M_i`. -/
@[expose] public def theorem_8_17_representative_source_data
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G) : Prop :=
  notation_8_10_source_data M MF Ms A A0 A1 ∧
    notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R


end CFSG.Section8
