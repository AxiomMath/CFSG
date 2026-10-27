module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearSides
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySides
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggResTwoNodeSideDatum_of_large_two_node_rows
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X J : Subgroup G}
    (hA : ∀ [Fact p.Prime] (r f : ℕ), 10 ≤ r → p ∣ 2 ^ f - 1 →
      GGHasLabel ⟨.A, r, f⟩ (X ⧸ Subgroup.center X) → LargeEvenInLambda2 ⟨.A, r, f⟩ →
      GGHasLabel ⟨.A, r - 2, f⟩ (J ⧸ Subgroup.center J) → GGResTwoNodeSideDatum p Bs X J)
    (hU : ∀ [Fact p.Prime] (r f : ℕ), 10 ≤ r → p ∣ 2 ^ f + 1 → p ∣ r + 1 →
      GGHasLabel ⟨.twA, r, f⟩ (X ⧸ Subgroup.center X) → LargeEvenInLambda2 ⟨.twA, r, f⟩ →
      GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J) → GGResTwoNodeSideDatum p Bs X J)
    [Fact p.Prime]
    (hrow : GGResRowAt (fun p J X => ggRowTwoNode p J X ∧ 10 ≤ X.rank) p J X) :
    GGResTwoNodeSideDatum p Bs X J := by
  obtain ⟨labJ, labX, hΛJ, hΛX, hJ, hX, hrow, hlarge⟩ := hrow
  rcases hrow with hArow | hUrow | hE | hE
  · obtain ⟨htag, hpq, -, heq⟩ := hArow
    obtain ⟨t, a, f⟩ := labJ
    dsimp only at htag hpq heq
    subst t
    rw [heq] at hΛX hX hlarge
    have hr : 10 ≤ a + 2 := hlarge
    apply hA (a + 2) f hr hpq hX hΛX
    simpa only [Nat.add_sub_cancel] using hJ
  · obtain ⟨htag, hpq, hpd, heq⟩ := hUrow
    obtain ⟨t, a, f⟩ := labJ
    dsimp only at htag hpq hpd heq
    subst t
    rw [heq] at hΛX hX hlarge
    have hr : 10 ≤ a + 2 := hlarge
    apply hU (a + 2) f hr hpq (by simpa only [Nat.add_assoc] using hpd) hX hΛX
    simpa only [Nat.add_sub_cancel] using hJ
  · rw [hE.2.2.2] at hlarge
    change 10 ≤ 0 at hlarge
    omega
  · rw [hE.2.2.2] at hlarge
    change 10 ≤ 0 at hlarge
    omega

theorem ggTBJTwoNodeLargeInput_holds
    : GGTBJTwoNodeLargeInput := by
  intro G _ _ p B Bs x L D J y K hH hp
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  constructor
  · intro _ hrow
    exact ggResTwoNodeSideDatum_of_large_two_node_rows
      (fun r f hr hpq hl hΛ hJl => ggResTwoNodeSideDatum_large_linear_L
        hRig hH (by omega : 4 ≤ r) hpq hl hΛ hJl)
      (fun r f hr hpq hpd hl hΛ hJl => ggResTwoNodeSideDatum_large_unitary_L
        hRig hH (by omega : 4 ≤ r) (by omega : r ≠ 5) hpq hpd hl hΛ hJl) hrow
  · intro _ hrow
    exact ggResTwoNodeSideDatum_of_large_two_node_rows
      (fun r f hr hpq hl hΛ hJl => ggResTwoNodeSideDatum_large_linear_K
        hRig hLB hH (by omega : 4 ≤ r) hpq hl hΛ hJl)
      (fun r f hr hpq hpd hl hΛ hJl => ggResTwoNodeSideDatum_large_unitary_K
        hRig hLB hH (by omega : 4 ≤ r) (by omega : r ≠ 5) hpq hpd hl hΛ hJl) hrow

end CFSG.StandardType

end
