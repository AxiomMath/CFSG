module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

section Helper

variable {G : Type} [Group G]

theorem uc22s217_conjClosure_eq_of_ncard_eq_one {M L : Subgroup G}
    (h : (conjSetOf M L).ncard = 1) : conjClosure M L = L := by
  obtain ⟨K, hK⟩ := Set.ncard_eq_one.mp h
  have hLmem : L ∈ conjSetOf M L := ⟨1, M.one_mem, by ext x; simp⟩
  have hKL : K = L := by
    have : L ∈ ({K} : Set (Subgroup G)) := hK ▸ hLmem
    exact (Set.mem_singleton_iff.mp this).symm
  unfold conjClosure
  rw [hK, hKL]
  simp

end Helper

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_NormalSp4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, Odd n → IsSp4 (Bar2 L) n →
    (L.subgroupOf D.M).Normal

@[expose] def S21_17R (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ (L.subgroupOf D.M).Normal →
    (∀ n : ℕ, ¬ IsSU3 (Bar2 L) n) ∧
    (∀ n : ℕ, IsPowTwo n → IsL2 (Bar2 L) n → (conjSetOf D.M L).ncard ≤ 2) ∧
    ((conjSetOf D.M L).ncard = 2 → IsL2 (Bar2 L) 2 → IsPowTwo c.n) ∧
    (∀ q : ℕ, q.Prime → 5 < q → ¬ IsL2Odd (Bar2 L) q) ∧
    (IsJ1 (Bar2 L) → CFSG.Open.evenRank G = 3)

end Statements

end CFSG.LocalAnalysis.UniquenessCase.UC22
