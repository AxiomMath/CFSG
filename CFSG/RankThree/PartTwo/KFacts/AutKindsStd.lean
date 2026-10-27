module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.RankThree.PartTwo.KFacts.AutSz
public import CFSG.RankThree.PartTwo.KFacts.AutTriality
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.RankThree.PartTwo.KFacts.AutLargeRee

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type*} [Group G] [Finite G]

inductive InducesStdKind (L : Subgroup G) (x : G) (k : AutKind) : Prop
  | psl2 (K : Type) [Field K] [Finite K] (h : InducesKindPSL2 K L x k)
  | psl (n : ℕ) (K : Type) [Field K] [Finite K] (hn : 3 ≤ n) (h : InducesKindPSL n K L x k)
  | sl (n : ℕ) (K : Type) [Field K] [Finite K] (hn : 3 ≤ n) (h : InducesKindSL n K L x k)
  | psu3 {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K) (hq : 2 < p ^ f)
      (h : InducesKindPSU3 hK L x k)
  | su3 {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K) (hq : 2 < p ^ f)
      (h : InducesKindSU3 hK L hq x k)
  | psp (r : ℕ) (K : Type) [Field K] [Finite K] (hr : 3 ≤ r ∨ (r = 2 ∧ ringChar K ≠ 2))
      (h : InducesKindPSp r K L x k)
  | psp4even (F : Type) [Field F] [Finite F] [CharP F 2] (h : InducesKindPSp4Even F L x k)
  | g2 (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
      (h : InducesKindG2 K L x k)
  | sz (a : ℕ) (K : Type) [Field K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
      (h : InducesKindSz a K L x k)
  | triality (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
      (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (h : InducesKindTriality σ L x k)
  | largeRee (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
      [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
      (hK : Nat.card K = 2 ^ (2 * a + 1)) (h : InducesKindLargeRee a K L x k)

variable {L : Subgroup G} {x : G} {k : AutKind}

theorem InducesStdKind.mem_normalizer (h : InducesStdKind L x k) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  cases h with
  | psl2 K h => exact h.choose_spec.choose
  | psl n K hn h => exact h.choose_spec.choose
  | sl n K hn h => exact h.choose_spec.choose
  | psu3 hK hq h => exact h.choose_spec.choose
  | su3 hK hq h => exact h.choose_spec.choose
  | psp r K hr h => exact h.choose_spec.choose
  | psp4even F h => exact h.choose_spec.choose
  | g2 K hK3 hK4 h => exact h.choose_spec.choose
  | sz a K ha hK h => exact h.choose_spec.choose
  | triality f hf K hK σ hσ h => exact h.choose_spec.choose
  | largeRee a ha K hK h => exact h.choose_spec.choose

theorem inducesKindPSL_inner_iff {n : ℕ} {K : Type} [Field K]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL n K) :
    InducesKindPSL n K L x .inner ↔
      x ∈ Subgroup.normalizer (L : Set G) ∧ ¬ InducesOuterTheta x L :=
  ⟨fun ⟨e', h⟩ => (inducesKind_inner_iff L _ e' x).mp h,
    fun h => ⟨e, (inducesKind_inner_iff L _ e x).mpr h⟩⟩

theorem inducesKindPSU3_inner_iff {p f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData p f K}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU hK 3) :
    InducesKindPSU3 hK L x .inner ↔
      x ∈ Subgroup.normalizer (L : Set G) ∧ ¬ InducesOuterTheta x L :=
  ⟨fun ⟨e', h⟩ => (inducesKind_inner_iff L _ e' x).mp h,
    fun h => ⟨e, (inducesKind_inner_iff L _ e x).mpr h⟩⟩

end CFSG.RankThree.PartTwo.KFacts
