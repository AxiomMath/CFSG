module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.GH74.Uniqueness.SU.SU13TA3Gen
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace Om8Excl

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem one_le_ncard_conjSet {A : Type*} [Group A] [Finite A] (K N : Subgroup A) :
    1 ≤ (conjSet K N).ncard :=
  (Set.ncard_pos (Set.toFinite _)).2 ⟨K, s15_T7_mem_conjSet_self K N⟩

theorem one_le_s15 (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G) :
    1 ≤ s15 M V₀ V hV L :=
  (Set.ncard_pos (Set.toFinite _)).2
    ⟨barSub V₀ V hV L, s15_T7_mem_conjSet_self (barSub V₀ V hV L) (Mbar M V₀ V hV)⟩

theorem card_eq_sq_of_ncard_two {A : Type*} [Group A] {X K N : Subgroup A}
    (h : IsDirectProdOfConj X K N) (h2 : (conjSet K N).ncard = 2) :
    Nat.card ↥X = Nat.card ↥K ^ 2 := by
  obtain ⟨Y, Z, hYZ, hS⟩ := Set.ncard_eq_two.1 h2
  have hY : Y ∈ conjSet K N := by rw [hS]; exact Set.mem_insert _ _
  have hZ : Z ∈ conjSet K N := by rw [hS]; exact Set.mem_insert_of_mem _ rfl
  have hcard : ∀ W ∈ conjSet K N, Nat.card ↥W = Nat.card ↥K := by
    rintro W ⟨n, -, rfl⟩
    exact Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hX : X = Y ⊔ Z := by
    rw [← h.2.1, hS, iSup_insert, iSup_singleton]
  have hdisj : Y ⊓ Z = ⊥ := by
    have := h.2.2.2 Y hY
    rw [hS, iSup_insert, iSup_singleton] at this
    simpa [hYZ.symm] using this
  have hcomm : ∀ y ∈ Y, ∀ z ∈ Z, Commute y z := by
    intro y hy z hz
    have h1 : ⁅y, z⁆ ∈ ⁅Y, Z⁆ := Subgroup.commutator_mem_commutator hy hz
    rw [h.2.2.1 Y hY Z hZ hYZ, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  rw [hX, CFSG.GH74.Uniqueness.SU.SU13.TA.card_sup_of_commute hcomm (disjoint_iff.2 hdisj),
    hcard Y hY, hcard Z hZ, sq]

end Om8Excl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
