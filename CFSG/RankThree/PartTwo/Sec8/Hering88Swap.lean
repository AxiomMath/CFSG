module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof88

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


@[expose] def KF88SwapCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
        (Subgroup.zpowers a : Set G)

@[expose] def KF88SwapInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∃ E ∈ partTwoE G, E ≤ A ∧ ∃ U ∈ invariantPiSubgroups Y E (piOf 2), U ≠ ⊥

theorem kF88Hyp81Y_of (hC : KF88SwapCent) (hI : KF88SwapInv) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}
    (h : Sec8Pair G A c L a b X n) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a)
    (hIJ : sec8I L a ⊔ sec8J X a ≤ Y) {x : G} (hx : x = c ∨ x = b)
    (hxY : KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) :
    Hyp81 G A a Y x := by
  obtain ⟨hbA, hb1, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hxA : x ∈ A := by rcases hx with rfl | rfl; exacts [h.mem_A, hbA]
  have hx1 : x ≠ 1 := by rcases hx with rfl | rfl; exacts [h.ne_one, hb1]
  exact
    { toPartTwoStanding := h.toPartTwoStanding
      mem_partTwoF := h.mem_partTwoF
      mem_A := h.a_mem
      ne_one := h.a_ne_one
      mem_thetaComponentsAt := hY
      sectionCentralizer_eq := hC G A c L a b X n h Y hY hIJ x hx hxY
      a_mem := hxA
      a_ne_one := hx1
      inducesStdKind := hxY
      exists_invariant_two := fun _ => hI G A c L a b X n h Y hY hIJ x hx hxY
      partTwoE_eq := fun h27 => absurd (h.card_eq.symm.trans h27) (by norm_num) }

theorem kF88Data83Y_of (h83 : Item83) (hC : KF88SwapCent) (hI : KF88SwapInv) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}
    (h : Sec8Pair G A c L a b X n) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a)
    (hIJ : sec8I L a ⊔ sec8J X a ≤ Y) {x : G} (hx : x = c ∨ x = b)
    (hxY : KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) :
    ∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), Data83 G a Y x A₀ d' n' :=
  h83 G A a Y x (kF88Hyp81Y_of hC hI h hY hIJ hx hxY) (by rw [h.card_eq]; norm_num)

@[expose] def KF88StepDData83 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      (∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), Data83 G a Y x A₀ d' n') →
      ∃ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x ∧
        IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
          aschbacherSolvableCore 3
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) ∧
        (∃ m : ℕ, 1 ≤ m ∧
          IsType418 (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
            aschbacherSolvableCore 3
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) m) ∧
        KFacts.InducesStdKind
          (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) x .field

theorem kF88StepD_of_data83 (h83 : Item83) (hC : KF88SwapCent) (hI : KF88SwapInv)
    (hS : KF88StepDData83) : KF88StepD := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY
  exact hS G A c L a b X n h Y hY hIJ x hx hxY (kF88Data83Y_of h83 hC hI h hY hIJ hx hxY)

end CFSG.RankThree.PartTwo.Sec8
