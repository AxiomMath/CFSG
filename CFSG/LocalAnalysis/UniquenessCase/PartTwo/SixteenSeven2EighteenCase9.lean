module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_isPSL_of_isL3 {X : Type} [Group X] (h : IsL3 X 1) : IsPSL 3 2 1 X := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals exact absurd h0 (by norm_num)

theorem s16c167_insp18_case9 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Setting16 D ⊥ V L) {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)}
    (hC : Concl1617 D ⊥ V hV L A g Δ) (hc2 : ¬ Case168_2 D ⊥ V hV L)
    (h9 : Case168_9 D ⊥ V hV L) : Insp18 D ⊥ V hV L g Δ := by
  obtain ⟨hn, hle, hi, hs, -, -, h910⟩ := hC
  have hΔ : Δ = wConj D.M ⊥ V hV L := h910 (Or.inl h9)
  obtain ⟨-, hL3, hs15, hsum, -⟩ := h9
  have hM : D.M ≤ normalizer (V : Set G) := hS.hyp16.hyp125.normalizer_eq.ge
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hL : IsPSL 3 2 1 ↥(barSub ⊥ V hV L) := by
    show IsPSL 3 2 1 ↥(lBar ⊥ V hV L)
    exact s16c167_isPSL_of_isL3 hL3
  have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (barSub ⊥ V hV L)
      (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (barSub ⊥ V hV L)) ⊥ 3 := by
    show SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar ⊥ V hV L) (wTil ⊥ V hV L) ⊥ 3
    exact hsum
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (barSub ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  have hcj : imgTil ⊥ V hV '' Δ =
      conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (barSub ⊥ V hV L)) := by
    rw [hΔ]
    exact s16c167_imgTil_wConj hV hM L
  obtain ⟨hn2, hind, hsup⟩ := s16c167_imgTil_decomp hV hn hle hi hs
  rw [hcj] at hn2 hind hsup
  obtain ⟨h1, h2, h3, h4⟩ :=
    s16c167_cfg9_abstract (W := Vtil (⊥ : Subgroup G) V hV)
      (X := Mbar D.M ⊥ V hV) (L := barSub ⊥ V hV L) hW hL hsum' hcls hn2 hind hsup
  have hmem : ∀ I ∈ Δ,
      imgTil ⊥ V hV I ∈ conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (barSub ⊥ V hV L)) :=
    fun I hI => hcj ▸ Set.mem_image_of_mem _ hI
  have hk3 : D.k + 1 ≤ 3 := by have := s16c167_k_le_two D; omega
  refine s16c167_insp18_of_tilde D hM hle ?_ ?_ ?_ ?_ ?_ ?_
  · show D.k + 1 ≤ E3.mParam (Mbar D.M ⊥ V hV)
    exact le_trans hk3 h4
  · intro I hI
    rw [h1 _ (hmem I hI)]
    omega
  · exact s16c167_disj_of_tilde hM hle
      (fun t ht I hI => h2 t ht (imgTil ⊥ V hV I) (hmem I hI))
  · exact fun h => absurd h hc2
  · exact fun h => absurd h hc2
  · intro _ t ht ht2 I hI hIt
    rcases h3 t ht ht2 (imgTil ⊥ V hV I) (hmem I hI) hIt with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans hk3 h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
