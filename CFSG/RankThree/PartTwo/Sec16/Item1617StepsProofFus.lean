module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def KS1617Fus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L D : Subgroup G) (n : ℕ), 1 ≤ n → ¬ 3 ∣ n →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n →
    D ≤ L → CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
    ∀ y ∈ D, y ≠ 1 → ∀ z ∈ D, z ≠ 1 →
      ∃ w ∈ L ⊓ Subgroup.normalizer (D : Set G), w * y * w⁻¹ = z

namespace Proof1617

variable {G : Type} [Group G]

theorem mem_normalizer_of_mem_normalizer_inf {A L D : Subgroup G} {c : G}
    (hA : A = Subgroup.zpowers c ⊔ D) (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) {w : G}
    (hw : w ∈ L ⊓ Subgroup.normalizer (D : Set G)) :
    w ∈ Subgroup.normalizer (A : Set G) := by
  obtain ⟨hwL, hwD⟩ := Subgroup.mem_inf.mp hw
  have hwc : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hLc hwL
  rw [hA]
  have hle : Subgroup.zpowers w ≤ Subgroup.normalizer
      ((Subgroup.zpowers c ⊔ D : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp hwc,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hwD]
  exact Subgroup.zpowers_le.mp hle

end Proof1617

end CFSG.RankThree.PartTwo.Sec16
