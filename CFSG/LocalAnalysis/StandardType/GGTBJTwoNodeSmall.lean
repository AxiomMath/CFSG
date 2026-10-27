module

public import CFSG.LocalAnalysis.StandardType.GGTWSmallCarried
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearSides
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySides
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixOriginal
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggResTwoNodeSideDatum_of_small_two_node_rows
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs X J : Subgroup G}
    (hA : ∀ (r f : ℕ), 4 ≤ r → p ∣ 2 ^ f - 1 →
      GGHasLabel ⟨.A, r, f⟩ (X ⧸ Subgroup.center X) → LargeEvenInLambda2 ⟨.A, r, f⟩ →
      GGHasLabel ⟨.A, r - 2, f⟩ (J ⧸ Subgroup.center J) → GGResTwoNodeSideDatum p Bs X J)
    (hU : ∀ (r f : ℕ), 4 ≤ r → r ≠ 5 → p ∣ 2 ^ f + 1 → p ∣ r + 1 →
      GGHasLabel ⟨.twA, r, f⟩ (X ⧸ Subgroup.center X) → LargeEvenInLambda2 ⟨.twA, r, f⟩ →
      GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J) → GGResTwoNodeSideDatum p Bs X J)
    (hU6 : ∀ (f : ℕ), p = 3 → 3 ∣ 2 ^ f + 1 →
      GGHasLabel ⟨.twA, 5, f⟩ (X ⧸ Subgroup.center X) → LargeEvenInLambda2 ⟨.twA, 5, f⟩ →
      GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J) → GGResTwoNodeSideDatum p Bs X J)
    (hrow : GGResRowAt ggRowTwoNodeSmallJA p J X) : GGResTwoNodeSideDatum p Bs X J := by
  have hp : p.Prime := Fact.out
  obtain ⟨labJ, labX, hΛJ, hΛX, hJ, hX, hrow, htag⟩ := hrow
  rcases hrow.1 with hArow | hUrow | hE | hE
  · obtain ⟨htagA, hpq, hpd, heq⟩ := hArow
    obtain ⟨t, a, f⟩ := labJ
    dsimp only at htagA hpq hpd heq
    subst t
    have ha1 : 1 ≤ a := hΛJ.2.1
    have ha2 : 2 ≤ a := by
      by_contra ha2
      have ha : a = 1 := by omega
      have hdvd : p ∣ 2 ^ 2 := by simpa [ha] using hpd
      have hpEq : p = 2 :=
        ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)).resolve_left hp.ne_one
      exact hp2 hpEq
    rw [heq] at hΛX hX
    apply hA (a + 2) f (by omega) hpq hX hΛX
    simpa only [Nat.add_sub_cancel] using hJ
  · obtain ⟨htagU, hpq, hpd, heq⟩ := hUrow
    obtain ⟨t, a, f⟩ := labJ
    dsimp only at htagU hpq hpd heq
    subst t
    have ha : 2 ≤ a := hΛJ.2.1
    rw [heq] at hΛX hX
    by_cases h6 : a + 2 = 5
    · have ha3 : a = 3 := by omega
      subst a
      have hp3 : p = 3 := by
        have hdvd : p ∣ 2 * 3 := by simpa using hpd
        rcases hp.dvd_mul.mp hdvd with h2 | h3
        · exact (hp2 ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one)).elim
        · exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hp.ne_one
      exact hU6 f hp3 (hp3 ▸ hpq) hX hΛX hJ
    · apply hU (a + 2) f (by omega) h6 hpq (by simpa only [Nat.add_assoc] using hpd)
        hX hΛX
      simpa only [Nat.add_sub_cancel] using hJ
  · rw [hE.1] at htag
    simp at htag
  · rw [hE.1] at htag
    simp at htag

theorem ggTBJTwoNodeSmallInput_holds
    : GGTBJTwoNodeSmallInput := by
  intro G _ _ p B Bs x L D J y K hH hp
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  constructor
  · intro _ hrow
    exact ggResTwoNodeSideDatum_of_small_two_node_rows hp2
      (fun r f hr hpq hl hΛ hJl => ggResTwoNodeSideDatum_large_linear_L
        hRig hH hr hpq hl hΛ hJl)
      (fun r f hr hr5 hpq hpd hl hΛ hJl => ggResTwoNodeSideDatum_large_unitary_L
        hRig hH hr hr5 hpq hpd hl hΛ hJl)
      (fun f hp3 hpq hl hΛ hJl => by
        subst p
        exact ggResTwoNodeSideDatum_unitary_six_side_all hRig hLB hH
          (Or.inl rfl) hpq hl hΛ hJl) hrow
  · intro _ hrow
    exact ggResTwoNodeSideDatum_of_small_two_node_rows hp2
      (fun r f hr hpq hl hΛ hJl => ggResTwoNodeSideDatum_large_linear_K
        hRig hLB hH hr hpq hl hΛ hJl)
      (fun r f hr hr5 hpq hpd hl hΛ hJl => ggResTwoNodeSideDatum_large_unitary_K
        hRig hLB hH hr hr5 hpq hpd hl hΛ hJl)
      (fun f hp3 hpq hl hΛ hJl => by
        subst p
        exact ggResTwoNodeSideDatum_unitary_six_side_all hRig hLB hH
          (Or.inr rfl) hpq hl hΛ hJl) hrow

end CFSG.StandardType

end
