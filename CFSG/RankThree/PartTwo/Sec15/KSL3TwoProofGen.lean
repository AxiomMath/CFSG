module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofY0

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def KS1517CentGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → Group.IsPerfect X → ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) →
    ¬ Sec4.IsoLThreePi X 2 2 →
    ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
      sSup {T : Subgroup X | ¬ 3 ∣ Nat.card T ∧ ∃ x ∈ D, x ≠ 1 ∧
        T ≤ Subgroup.centralizer ({x} : Set X) ∧
        Subgroup.centralizer ({x} : Set X) ≤ Subgroup.normalizer (T : Set X)} = ⊤

theorem ks1517Gen_of (h : KS1517CentGen) : KS1517Gen := by
  intro X _ _ p e _ he hiso hperf h9 h4 D hD hD9
  refine eq_top_iff.mpr ((h X p e he hiso hperf h9 h4 D hD hD9).symm.le.trans
    (sSup_le_sSup ?_))
  rintro T ⟨hT3, x, hxD, -, -, hCN⟩
  refine ⟨le_top, fun q hq => ?_, fun d hd => hCN ?_⟩
  · change (q : ℕ) ≠ 3
    rintro hq3
    exact hT3 (hq3 ▸ hq)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hD.1.is_comm.comm ⟨d, hd⟩ ⟨x, hxD⟩)

end CFSG.RankThree.PartTwo.Sec15
