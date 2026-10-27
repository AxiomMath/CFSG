module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import CFSG.Quasithin.Vol2.Ch6SL2Aut
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists

theorem l3ShapeU_basic {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = (p ^ 1) ^ 2) :
    CharP F p ∧
    (∀ A ∈ StatedSU 3 (p ^ 1) F, (A : Matrix (Fin 3) (Fin 3) F).det = 1) ∧
    negDiag3 F ∈ StatedSU 3 (p ^ 1) F ∧
    (∀ s ∈ StatedSU 3 (p ^ 1) F, s * s = 1 → s ≠ 1 →
      ∃ g ∈ StatedSU 3 (p ^ 1) F, g⁻¹ * s * g = negDiag3 F) ∧
    (∀ A ∈ StatedSU 3 (p ^ 1) F,
      (A * negDiag3 F = negDiag3 F * A ↔ ∃ B ∈ GU2Stated (p ^ 1) F, blk B = A)) ∧
    (∀ B ∈ GU2Stated (p ^ 1) F, blk B ∈ StatedSU 3 (p ^ 1) F) := by
  have hp2 : p ≠ 2 := by omega
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F :=
    ⟨hp, le_rfl, hF.trans (by ring)⟩
  have ht : ((CFSG.RankThree.Classical.unitaryInvT h : GL (Fin 3) F)) = negDiag3 F := rfl
  refine ⟨h.charP, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro A hA
    exact ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp hA).1
  ·
    rw [← ht]
    exact (CFSG.RankThree.Classical.unitaryInvT h).2
  ·
    intro s hs hss hs1
    have hs2 : (⟨s, hs⟩ : ↥(StatedSU 3 (p ^ 1) F)) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, sq]
      exact hss
    have hs1' : (⟨s, hs⟩ : ↥(StatedSU 3 (p ^ 1) F)) ≠ 1 := by
      intro e
      apply hs1
      have he := congrArg Subtype.val e
      exact he
    have hord : orderOf (⟨s, hs⟩ : ↥(StatedSU 3 (p ^ 1) F)) = 2 :=
      orderOf_eq_prime hs2 hs1'
    obtain ⟨c, hc⟩ :=
      isConj_iff.mp (CFSG.RankThree.Classical.isConj_unitaryInvT_of_orderOf h hp2 hord)
    refine ⟨(c : GL (Fin 3) F), c.2, ?_⟩
    have hsc : (c : GL (Fin 3) F) * negDiag3 F * (c : GL (Fin 3) F)⁻¹ = s := by
      have hc' := congrArg Subtype.val hc
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht] at hc'
      exact hc'
    rw [← hsc]
    group
  ·
    intro A hA
    constructor
    · intro hcomm
      have hy : (⟨A, hA⟩ : ↥(StatedSU 3 (p ^ 1) F)) *
          CFSG.RankThree.Classical.unitaryInvT h =
          CFSG.RankThree.Classical.unitaryInvT h * ⟨A, hA⟩ := by
        apply Subtype.ext
        exact hcomm
      obtain ⟨x, hx⟩ :=
        CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.mem_range_blkU_of_commute h hp2 hy
      have hx' : CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blk (x : GL (Fin 2) F) = A := by
        have hv := congrArg Subtype.val hx
        exact hv
      exact ⟨(x : GL (Fin 2) F), x.2, hx'⟩
    · rintro ⟨B, -, rfl⟩
      exact CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.blk_commute_negDiag3 B
  ·
    intro B hB
    exact (CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.blk_mem_iff h B).2 hB

end CFSG.Quasithin.H13
