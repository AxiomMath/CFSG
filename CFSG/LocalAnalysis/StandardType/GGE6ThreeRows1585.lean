module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6CycX

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGE6ThreeSimultaneousCyclic1585 : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (J : Subgroup L)
    (y : MulAut L) (E : Subgroup (MulAut L)) (labL labJ : LargeEvenLabel),
    LargeEvenInLambda2 labL → LargeEvenInLambda2 labJ → GGPairE6Three 3 labL labJ →
    GGHasLabel labL (L ⧸ Subgroup.center L) → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
    y ≠ 1 → y ^ 3 = 1 → y ∈ E → IsComponentOf J (ggAutFixedSubgroup y) →
    (∀ e ∈ E, Commute e y) →
    (∀ e ∈ E, ∀ j ∈ J, e j = j) →
    LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I) → IsCyclic E

theorem ggE6ThreeI1Rank_of_simultaneousCyclic1585
    (h : GGE6ThreeSimultaneousCyclic1585) : GGE6ThreeI1Rank := by
  change GGI1PairRankOn GGPairE6Three
  intro p hp hp2 L _ _ J y E labL labJ hL hJ hpair hhL hhJ hy hyE hEelem hcomp hfix hmark
  obtain rfl : p = 3 := hpair.1
  have hcomm : ∀ e ∈ E, Commute e y := fun e he =>
    by
      rw [Commute]
      exact congrArg Subtype.val
        (hEelem.1.is_comm.comm (⟨e, he⟩ : E) (⟨y, hyE⟩ : E))
  have hcyc : IsCyclic E :=
    h L J y E labL labJ hL hJ hpair hhL hhJ hy (hEelem.2 y hyE) hyE hcomp hcomm hfix hmark
  exact le_zpowers_of_isCyclic_of_pow_eq_one Nat.prime_three hcyc hEelem.2 hyE hy

@[expose] def GGE6ThreeR1Labels1585 (labL labJ : LargeEvenLabel) : Prop :=
  let n := labL.n
  (labL.tag = .E6 ∧ 3 ∣ 2 ^ n - 1 ∧ labJ = ⟨.D, 5, n⟩) ∨
    (labL.tag = .twE6 ∧ 3 ∣ 2 ^ n + 1 ∧ labJ = ⟨.twD, 5, n⟩)

@[expose] def GGE6ThreeR3Labels1585 (labL labJ : LargeEvenLabel) : Prop :=
  let n := labL.n
  (labL.tag = .E6 ∧ 3 ∣ 2 ^ n - 1 ∧ labJ = ⟨.A, 2, 3 * n⟩) ∨
    (labL.tag = .twE6 ∧ 3 ∣ 2 ^ n + 1 ∧ labJ = ⟨.twA, 2, 3 * n⟩)

@[expose] def GGE6ThreeR4Labels1585 (labL labJ : LargeEvenLabel) : Prop :=
  let n := labL.n
  (labL.tag = .E6 ∧ 3 ∣ 2 ^ n - 1 ∧ labJ = ⟨.A, 5, n⟩) ∨
    (labL.tag = .twE6 ∧ 3 ∣ 2 ^ n + 1 ∧ labJ = ⟨.twA, 5, n⟩)

@[expose] def GGE6ThreeR16Labels1585 (labL labJ : LargeEvenLabel) : Prop :=
  let n := labL.n
  ((labL.tag = .E6 ∧ 3 ∣ 2 ^ n - 1) ∨ (labL.tag = .twE6 ∧ 3 ∣ 2 ^ n + 1)) ∧
    labJ = ⟨.triD4, 0, n⟩

@[expose] def GGE6ThreeR4OppLabels1585 (labL labJ : LargeEvenLabel) : Prop :=
  let n := labL.n
  (labL.tag = .E6 ∧ 3 ∣ 2 ^ n + 1 ∧ labJ = ⟨.A, 5, n⟩) ∨
    (labL.tag = .twE6 ∧ 3 ∣ 2 ^ n - 1 ∧ labJ = ⟨.twA, 5, n⟩)

@[expose] def GGE6ThreeR16OppLabels1585 (labL labJ : LargeEvenLabel) : Prop :=
  let n := labL.n
  ((labL.tag = .E6 ∧ 3 ∣ 2 ^ n + 1) ∨ (labL.tag = .twE6 ∧ 3 ∣ 2 ^ n - 1)) ∧
    labJ = ⟨.twD, 4, n⟩

@[expose] def GGE6ThreeCyclicOn1585 (row : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (J : Subgroup L)
    (y : MulAut L) (E : Subgroup (MulAut L)) (labL labJ : LargeEvenLabel),
    LargeEvenInLambda2 labL → LargeEvenInLambda2 labJ → GGPairE6Three 3 labL labJ →
    GGHasLabel labL (L ⧸ Subgroup.center L) → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
    y ≠ 1 → y ^ 3 = 1 → y ∈ E → IsComponentOf J (ggAutFixedSubgroup y) →
    (∀ e ∈ E, Commute e y) →
    (∀ e ∈ E, ∀ j ∈ J, e j = j) →
    LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I) →
    row labL labJ → IsCyclic E

@[expose] def GGE6ThreeRowCover1585 : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (J : Subgroup L)
    (y : MulAut L) (E : Subgroup (MulAut L)) (labL labJ : LargeEvenLabel),
    LargeEvenInLambda2 labL → LargeEvenInLambda2 labJ → GGPairE6Three 3 labL labJ →
    GGHasLabel labL (L ⧸ Subgroup.center L) → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
    y ≠ 1 → y ^ 3 = 1 → y ∈ E → IsComponentOf J (ggAutFixedSubgroup y) →
    (∀ e ∈ E, Commute e y) →
    (∀ e ∈ E, ∀ j ∈ J, e j = j) →
    LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I) →
    GGE6ThreeR1Labels1585 labL labJ ∨ GGE6ThreeR3Labels1585 labL labJ ∨
      GGE6ThreeR4Labels1585 labL labJ ∨ GGE6ThreeR16Labels1585 labL labJ ∨
      GGE6ThreeR4OppLabels1585 labL labJ ∨ GGE6ThreeR16OppLabels1585 labL labJ

theorem ggE6ThreeSimultaneousCyclic_of_rows1585
    (hcover : GGE6ThreeRowCover1585)
    (hR1 : GGE6ThreeCyclicOn1585 GGE6ThreeR1Labels1585) (hR3 : GGE6ThreeCyclicOn1585 GGE6ThreeR3Labels1585)
    (hR4 : GGE6ThreeCyclicOn1585 GGE6ThreeR4Labels1585) (hR16 : GGE6ThreeCyclicOn1585 GGE6ThreeR16Labels1585)
    (hR4opp : GGE6ThreeCyclicOn1585
        GGE6ThreeR4OppLabels1585) (hR16opp : GGE6ThreeCyclicOn1585
        GGE6ThreeR16OppLabels1585) :
    GGE6ThreeSimultaneousCyclic1585 := by
  intro L _ _ J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark
  rcases hcover L J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark with
    h1 | h3 | h4 | h16 | h4opp | h16opp
  · exact hR1 L J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark h1
  · exact hR3 L J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark h3
  · exact hR4 L J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark h4
  · exact hR16 L J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark h16
  · exact hR4opp L J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark h4opp
  · exact hR16opp L J y E labL labJ hL hJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark h16opp

theorem ggE6ThreeI1Rank_of_rows1585
    (hcover : GGE6ThreeRowCover1585)
    (hR1 : GGE6ThreeCyclicOn1585 GGE6ThreeR1Labels1585) (hR3 : GGE6ThreeCyclicOn1585 GGE6ThreeR3Labels1585)
    (hR4 : GGE6ThreeCyclicOn1585 GGE6ThreeR4Labels1585) (hR16 : GGE6ThreeCyclicOn1585 GGE6ThreeR16Labels1585)
    (hR4opp : GGE6ThreeCyclicOn1585
        GGE6ThreeR4OppLabels1585) (hR16opp : GGE6ThreeCyclicOn1585
        GGE6ThreeR16OppLabels1585) :
    GGE6ThreeI1Rank :=
  ggE6ThreeI1Rank_of_simultaneousCyclic1585
    (ggE6ThreeSimultaneousCyclic_of_rows1585 hcover hR1 hR3 hR4 hR16 hR4opp hR16opp)

end CFSG.StandardType
