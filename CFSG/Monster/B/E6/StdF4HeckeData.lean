module

public import CFSG.Monster.B.Classical.E6FoldedData

public section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Monster.B.Classical.E6Folded

@[expose] def plen (a : ℕ) : ℕ := (tWords.getD a []).length

@[expose] def hStep (k : Fin 4) (F : List ℕ) : List ℕ :=
  (List.range 24).map fun γ =>
    if gidx k γ = γ then letterWeight k * F.getD γ 0
    else if plen (gidx k γ) = plen γ + 1 then letterWeight k * F.getD (gidx k γ) 0
    else F.getD (gidx k γ) 0 + (letterWeight k - 1) * F.getD γ 0

@[expose] def lidx (γ : ℕ) : ℕ := ([2, 1, 0, -1, -2] : List ℤ).idxOf (levList.getD γ 0)

@[expose] def hInit (j : ℕ) : List ℕ := (List.range 24).map fun γ => if lidx γ = j then 1 else 0

@[expose] def hWord (l : List (Fin 4)) (F : List ℕ) : List ℕ := l.foldr hStep F

@[expose] def hVec (j β : ℕ) : List ℕ := hWord (tWords.getD β []) (hInit j)

@[expose] def hMat : List (List (List ℕ)) := [
  [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
  [[0, 1782, 0, 0, 0], [1, 85, 672, 1024, 0], [0, 27, 27, 1728, 0], [0, 1, 42, 715, 1024],
    [0, 0, 0, 891, 891]],
  [[0, 0, 44352, 0, 0], [0, 672, 672, 43008, 0], [1, 27, 2916, 8640, 32768],
    [0, 42, 210, 22596, 21504], [0, 0, 693, 18711, 24948]],
  [[0, 0, 0, 1824768, 0], [0, 1024, 43008, 732160, 1048576], [0, 1728, 8640, 929664, 884736],
    [1, 715, 22596, 824560, 976896], [0, 891, 18711, 850014, 955152]],
  [[0, 0, 0, 0, 2097152], [0, 0, 0, 1048576, 1048576], [0, 0, 32768, 884736, 1179648],
    [0, 1024, 21504, 976896, 1097728], [1, 891, 24948, 955152, 1116160]]]

@[expose] def hSum (k j γ : ℕ) : ℕ :=
  ∑ β ∈ Finset.range 24, if lidx β = k then (hVec j β).getD γ 0 else 0

@[expose] def hSumOK (k j : ℕ) : Bool :=
  (List.range 24).all fun γ => hSum k j γ == ((hMat.getD k []).getD (lidx γ) []).getD j 0

theorem hSumOK_0 : ∀ j < 5, hSumOK 0 j = true := by decide +kernel

theorem hSumOK_1 : ∀ j < 5, hSumOK 1 j = true := by decide +kernel

theorem hSumOK_2 : ∀ j < 5, hSumOK 2 j = true := by decide +kernel

theorem hSumOK_3 : ∀ j < 5, hSumOK 3 j = true := by decide +kernel

theorem hSumOK_4 : ∀ j < 5, hSumOK 4 j = true := by decide +kernel

theorem hSum_eq {k j γ : ℕ} (hk : k < 5) (hj : j < 5) (hγ : γ < 24) :
    hSum k j γ = ((hMat.getD k []).getD (lidx γ) []).getD j 0 := by
  have h : hSumOK k j = true := by
    interval_cases k
    · exact hSumOK_0 j hj
    · exact hSumOK_1 j hj
    · exact hSumOK_2 j hj
    · exact hSumOK_3 j hj
    · exact hSumOK_4 j hj
  simp only [hSumOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h γ hγ

theorem tWords_cons : ∀ β < 24, β ≠ 23 → ∃ k : Fin 4,
    tWords.getD β [] = k :: tWords.getD (gidx k β) [] := by
  decide +kernel

theorem gidx_gidx : ∀ k : Fin 4, ∀ β < 24, gidx k (gidx k β) = β := by
  decide +kernel

theorem plen_trichotomy : ∀ k : Fin 4, ∀ γ < 24,
    gidx k γ = γ ∨ plen (gidx k γ) = plen γ + 1 ∨ plen (gidx k γ) + 1 = plen γ := by
  decide +kernel

theorem lidx_lt : ∀ γ < 24, lidx γ < 5 := by decide +kernel

theorem plen_23 : plen 23 = 0 := by decide +kernel

theorem hVec_23 (j : ℕ) : hVec j 23 = hInit j := by
  rw [hVec, tWords_theta]
  rfl

theorem hVec_cons {β : ℕ} (hβ : β < 24) (hne : β ≠ 23) : ∃ k : Fin 4,
    tWords.getD β [] = k :: tWords.getD (gidx k β) [] ∧ plen (gidx k β) + 1 = plen β ∧
      ∀ j, hVec j β = hStep k (hVec j (gidx k β)) := by
  obtain ⟨k, hk⟩ := tWords_cons β hβ hne
  refine ⟨k, hk, by rw [plen, plen, hk, List.length_cons], fun j => ?_⟩
  rw [hVec, hVec, hk]
  rfl

end CFSG.Monster.B.E6.StdF4
