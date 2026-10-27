module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenFacts
public import Certificates.Certificate291401
public import Certificates.Certificate291402
public import Certificates.Certificate291403

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

open CFSG.RankThree.Native.ONTriple


theorem exists_rels_pair {j l₁ l₂ : ℕ} (hj : j < 2)
    (h₁ : l₁ < 4) (h₂ : l₂ < 4) (hl : l₁ < l₂) (m₁ m₂ : ℕ) (hm₁ : m₁ < 3) (hm₂ : m₂ < 3) :
    ∃ y : Fin 4 → GM, (∀ w ∈ l37Rels, FreeGroup.lift y (FreeGroup.mk w) = 1) ∧
      Subgroup.closure (Set.range y) = Subgroup.closure (Set.range (pairY j l₁ m₁ l₂ m₂)) :=
  Certificates.certificate291401 j l₁ l₂ hj h₁ h₂ hl m₁ m₂ hm₁ hm₂

theorem exists_rels_lY {j k : ℕ} (hj : j < 2) (hk : k < 9) :
    ∃ y : Fin 4 → GM, (∀ w ∈ l37Rels, FreeGroup.lift y (FreeGroup.mk w) = 1) ∧
      Subgroup.closure (Set.range y) = Subgroup.closure (Set.range (lY j k)) :=
  exists_rels_pair (l₁ := 0) (l₂ := 1) hj (by norm_num) (by norm_num) (by norm_num) _ _
    (rowAt_lt j hj k hk 0 (by norm_num)) (rowAt_lt j hj k hk 1 (by norm_num))

theorem mem_closure_in {j k : ℕ} (hj : j < 2) (hk : k < 9)
    (i : ℕ) (hi : i < 4) :
    xE j (2 + i / 2) (rowAt j k (2 + i / 2)) (i % 2) ∈ Subgroup.closure (Set.range (lY j k)) :=
  Certificates.certificate291402 j k hj hk i hi

theorem closure_top {j k l m : ℕ}
    (hj : j < 2) (hk : k < 9) (hl : l < 4) (hm : m < 3) (hne : m ≠ rowAt j k l) :
    Subgroup.closure (Set.range (lY j k) ∪ {xE j l m 0, xE j l m 1}) = (⊤ : Subgroup GM) :=
  Certificates.certificate291403 j k l m hj hk hl hm hne

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
