module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKGlueDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelTv
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelTvDict

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

theorem ggAutomizer_fix_of_centralizes {Bs K : Subgroup G} {y : G} (hyBs : y ∈ Bs)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) :
    ∀ φ ∈ ggAutomizer K Bs, φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := by
  intro φ hφ
  obtain ⟨g, hgK, _, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  apply Subtype.ext
  rw [hφg]
  have hyg : y * g = g * y :=
    (Subgroup.mem_centralizer_iff.mp (hKy hgK)) y (Set.mem_singleton y)
  rw [← hyg]
  group

private theorem exists_actsAs_evalWord {n : ℕ} {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6}
    {A : Subgroup (MulAut ↥Bs)} (g : Fin n → Mat6)
    (h : ∀ i : Fin n, ∃ φ ∈ A, ActsAs ι φ (g i)) :
    ∀ sw : List (Fin n), ∃ φ ∈ A, ActsAs ι φ (evalWord g sw) := by
  intro sw
  induction sw with
  | nil => exact ⟨1, A.one_mem, ActsAs.one ι⟩
  | cons i l ih =>
      obtain ⟨φ, hφA, hφ⟩ := h i
      obtain ⟨ψ, hψA, hψ⟩ := ih
      refine ⟨φ * ψ, A.mul_mem hφA hψA, ?_⟩
      change ActsAs ι (φ * ψ) (g i * evalWord g l)
      exact hφ.mul hψ

theorem realize_word {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {A : Subgroup (MulAut ↥Bs)}
    (hS : ∀ i : Fin 5, ∃ φ ∈ A, ActsAs ι φ (gS i)) (sw : List (Fin 5)) :
    ∃ φ ∈ A, ActsAs ι φ (evalWord gS sw) :=
  exists_actsAs_evalWord (A := A) gS hS sw

private theorem exists_actsAs_top_of_closureL {Bs L : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6}
    {m : Mat6} (hm : m ∈ closureL)
    (hL : ∀ m ∈ closureL, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ m) :
    ∃ φ ∈ ggAutomizer ⊤ Bs, ActsAs ι φ m := by
  obtain ⟨φ, hφA, hφ⟩ := hL m hm
  exact ⟨φ, ggAutomizer_mono Bs le_top hφA, hφ⟩

theorem ggE6Dep_noTv {Bs L K : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6}
    (hnt : GGNoTransvection 3 Bs)
    (hL : ∀ m ∈ closureL, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ m)
    {s t u w : ZMod 3} (h : s * u + t * w = 2) (hw : w ≠ 0)
    (hK : ∃ φ ∈ ggAutomizer K Bs, ActsAs ι φ (gensAll s t u w 6)) : s = 0 ∧ u = 0 := by
  by_contra hs
  obtain ⟨word, hword⟩ := exists_transvection s t u w h hw hs
  have hgen : ∀ i : Fin 7, ∃ φ ∈ ggAutomizer ⊤ Bs, ActsAs ι φ (gensAll s t u w i) := by
    intro i
    fin_cases i
    · simpa [gensAll, gensL] using
        exists_actsAs_top_of_closureL (L := L) (m := gensL 0)
          (Submonoid.subset_closure ⟨0, rfl⟩) hL
    · simpa [gensAll, gensL] using
        exists_actsAs_top_of_closureL (L := L) (m := gensL 1)
          (Submonoid.subset_closure ⟨1, rfl⟩) hL
    · simpa [gensAll, gensL] using
        exists_actsAs_top_of_closureL (L := L) (m := gensL 2)
          (Submonoid.subset_closure ⟨2, rfl⟩) hL
    · simpa [gensAll, gensL] using
        exists_actsAs_top_of_closureL (L := L) (m := gensL 3)
          (Submonoid.subset_closure ⟨3, rfl⟩) hL
    · simpa [gensAll, gensL] using
        exists_actsAs_top_of_closureL (L := L) (m := gensL 4)
          (Submonoid.subset_closure ⟨4, rfl⟩) hL
    · simpa [gensAll, gensL] using
        exists_actsAs_top_of_closureL (L := L) (m := gensL 5)
          (Submonoid.subset_closure ⟨5, rfl⟩) hL
    · obtain ⟨φ, hφA, hφ⟩ := hK
      exact ⟨φ, ggAutomizer_mono Bs le_top hφA, hφ⟩
  obtain ⟨φ, hφA, hφ⟩ :=
    exists_actsAs_evalWord (A := ggAutomizer ⊤ Bs) (gensAll s t u w) hgen word
  have ht : GGIsTransvection 3 φ := ggIsTransvection_of_isTv6 hφ hword
  have hφInd : φ ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, _, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφA
    exact ⟨g, Subgroup.mem_top g, hgN, hφg⟩
  exact hnt φ hφInd ht

end E6Dep

end CFSG.StandardType

end
