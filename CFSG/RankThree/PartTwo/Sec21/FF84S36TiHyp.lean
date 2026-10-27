module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb)

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

@[expose] def A9CentralizerStmt : Prop :=
  ∀ (s : P8), s ∈ A8s → s * s = 1 → s * m₁ * s⁻¹ = m₁⁻¹ → s * m₂ * s⁻¹ = m₂ →
    s.cycleType = {2, 2, 2, 2} ∧
    ∃ Q : Subgroup P8, Q ≤ A8s ∧ Q ≤ Subgroup.centralizer ({s} : Set P8) ∧
      (Q.subgroupOf (Subgroup.centralizer ({s} : Set P8) ⊓ A8s)).Normal ∧ IsPGroup 2 Q ∧
      Nat.card Q = 32 ∧ s ∈ Q ∧ Subgroup.center ↥Q = (Subgroup.zpowers s).subgroupOf Q ∧
      IsExtraspecialPGroup 2 ↥Q ∧ (∃ A : Subgroup P8, A ≤ Q ∧ IsElemAb 2 3 A) ∧
      ∀ R : Subgroup P8, R ≤ Subgroup.centralizer ({s} : Set P8) ⊓ A8s → IsPGroup 2 R →
        (R.subgroupOf (Subgroup.centralizer ({s} : Set P8) ⊓ A8s)).Normal → R ≤ Q

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
