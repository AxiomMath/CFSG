module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SupDecomposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_centralizerBar_of_centralizes_left {P L Q X : Subgroup G}
    (hCQ : ∀ c ∈ centralizerBar P L, ∀ q ∈ Q, c * q = q * c)
    (hZQ : ∀ q ∈ Q, (∀ q' ∈ Q, q * q' = q' * q) → q ∈ centralizerBar P L)
    (hXdecomp : X ≤ Q ⊔ centralizerBar P L)
    (hXcentQ : ∀ x ∈ X, ∀ q ∈ Q, x * q = q * x) :
    X ≤ centralizerBar P L := by
  intro x hx
  obtain ⟨q, hq, c, hc, hxqc⟩ := exists_mul_mem_sup_of_commute hCQ (hXdecomp hx)
  have hq_comm : ∀ q' ∈ Q, q * q' = q' * q := by
    intro q' hq'
    have hxq' : (q * c) * q' = q' * (q * c) := by
      rw [← hxqc]
      exact hXcentQ x hx q' hq'
    have hcq' : c * q' = q' * c := hCQ c hc q' hq'
    have h1 : (q * q') * c = (q' * q) * c := by
      calc (q * q') * c = q * (q' * c) := by rw [mul_assoc]
        _ = q * (c * q') := by rw [hcq']
        _ = (q * c) * q' := by rw [← mul_assoc]
        _ = q' * (q * c) := hxq'
        _ = (q' * q) * c := by rw [mul_assoc]
    exact mul_right_cancel h1
  rw [hxqc]
  exact (centralizerBar P L).mul_mem (hZQ q hq hq_comm) hc

theorem commutator_le_pCore_of_le_centralizerBar {P L X : Subgroup G}
    (hPNL : P ≤ Subgroup.normalizer (L : Set G))
    (hX : X ≤ centralizerBar P L) :
    ⁅X, L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (mem_centralizerBar_iff.mp (hX hx)).2 y hy

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
