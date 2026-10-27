module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_11

public section

namespace CFSG.RankThree.OddKernel

universe u

theorem commutator_le_of_isCyclic_quotient {P : Type*} [Group P] (C : Subgroup P) [C.Normal]
    [IsCyclic (P ⧸ C)] : commutator P ≤ C := by
  have hcomm : IsMulCommutative (P ⧸ C) := by
    let _ := IsCyclic.commGroup (α := P ⧸ C)
    infer_instance
  have h := Abelianization.commutator_subset_ker (QuotientGroup.mk' C)
  rwa [QuotientGroup.ker_mk'] at h

theorem huppert_small_prime_torsion_cyclic_normal_structure {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup p P)
    (hΩ : Nat.card (omega₁ P (p := p)) ≤ p ^ 2) :
    (∃ C : Subgroup P, ∃ _ : C.Normal, IsCyclic C ∧ IsCyclic (P ⧸ C)) ∧
      IsCyclic (commutator P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨C, hCn, hCc, hQc⟩ := CFSG.proposition_4_11 (R := P) (p := p) hp3 hΩ
  exact ⟨⟨C, hCn, hCc, hQc⟩, Subgroup.isCyclic_of_le (commutator_le_of_isCyclic_quotient C)⟩

end CFSG.RankThree.OddKernel
