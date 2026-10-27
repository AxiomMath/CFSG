module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5RootsOct
public import CFSG.LieType.Steinberg.CentralExt.SUBruhatExtras

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits
open scoped commutatorElement

section Octagon

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

private def octIdxB (γ : Fin 2 → ℤ) : ℤ := if γ 0 = 0 then 4 else γ 1 + 1

private theorem octIdxB_one : octIdxB (octRootB 1) = 1 := by simp [octIdxB, octRootB_one]
private theorem octIdxB_two : octIdxB (octRootB 2) = 2 := by simp [octIdxB, octRootB_two]
private theorem octIdxB_four : octIdxB (octRootB 4) = 4 := by simp [octIdxB, octRootB_four]

theorem octUnique_un5 :
    ∀ g g' : ℤ → SU (unitaryInvolution F p f) 5,
      (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k ∈ un5Oct hF k) →
      (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g' k ∈ un5Oct hF k) →
      ((intList 1 ((4 : ℕ) : ℤ)).map g).prod = ((intList 1 ((4 : ℕ) : ℤ)).map g').prod →
        ∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k = g' k := by
  have hl : intList 1 ((4 : ℕ) : ℤ) = [1, 2, 3, 4] := by decide
  intro g g' hg hg' hgg'
  rw [hl] at hg hg' hgg' ⊢
  set G : (Fin 2 → ℤ) → SU (unitaryInvolution F p f) 5 := fun γ =>
    if γ = octRootB 3 then ⁅g 2, g 4⁆ * g 3 else g (octIdxB γ) with hG
  set G' : (Fin 2 → ℤ) → SU (unitaryInvolution F p f) 5 := fun γ =>
    if γ = octRootB 3 then ⁅g' 2, g' 4⁆ * g' 3 else g' (octIdxB γ) with hG'
  have n13 : octRootB 1 ≠ octRootB 3 := by decide
  have n43 : octRootB 4 ≠ octRootB 3 := by decide
  have n23 : octRootB 2 ≠ octRootB 3 := by decide
  have hG1 : G (octRootB 1) = g 1 := by simp [hG, n13, octIdxB_one]
  have hG4 : G (octRootB 4) = g 4 := by simp [hG, n43, octIdxB_four]
  have hG2 : G (octRootB 2) = g 2 := by simp [hG, n23, octIdxB_two]
  have hG3 : G (octRootB 3) = ⁅g 2, g 4⁆ * g 3 := by simp [hG]
  have hG1' : G' (octRootB 1) = g' 1 := by simp [hG', n13, octIdxB_one]
  have hG4' : G' (octRootB 4) = g' 4 := by simp [hG', n43, octIdxB_four]
  have hG2' : G' (octRootB 2) = g' 2 := by simp [hG', n23, octIdxB_two]
  have hG3' : G' (octRootB 3) = ⁅g' 2, g' 4⁆ * g' 3 := by simp [hG']
  have hk3 : ⁅g 2, g 4⁆ ∈ un5Oct hF 3 :=
    octComm_two_four_un5 hF _ (hg 2 (by simp)) _ (hg 4 (by simp))
  have hk3' : ⁅g' 2, g' 4⁆ ∈ un5Oct hF 3 :=
    octComm_two_four_un5 hF _ (hg' 2 (by simp)) _ (hg' 4 (by simp))
  have key := prodInjective_heights_un5 hF G G'
    (by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl | rfl
      · rw [hG1]; exact hg 1 (by simp)
      · rw [hG4]; exact hg 4 (by simp)
      · rw [hG2]; exact hg 2 (by simp)
      · rw [hG3]; exact mul_mem hk3 (hg 3 (by simp)))
    (by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl | rfl
      · rw [hG1']; exact hg' 1 (by simp)
      · rw [hG4']; exact hg' 4 (by simp)
      · rw [hG2']; exact hg' 2 (by simp)
      · rw [hG3']; exact mul_mem hk3' (hg' 3 (by simp)))
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hG1, hG2,
        hG3, hG4, hG1', hG2', hG3', hG4']
      rw [← octReorder_un5 hF g hg, ← octReorder_un5 hF g' hg']
      simpa using hgg')
  have e1 := key (octRootB 1) (by simp)
  have e4 := key (octRootB 4) (by simp)
  have e2 := key (octRootB 2) (by simp)
  have e3 := key (octRootB 3) (by simp)
  rw [hG1, hG1'] at e1
  rw [hG4, hG4'] at e4
  rw [hG2, hG2'] at e2
  rw [hG3, hG3', e2, e4] at e3
  have e3' : g 3 = g' 3 := mul_left_cancel e3
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  exacts [e1, e2, e3', e4]

theorem un5Octagon : Un5Octagon hF where
  ne_bot i hi := by
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
    exact (steinbergExtras hF 5 (by norm_num) ζ hζ).ne_bot _ (octRootB_mem_roots' hi)
  invariant i hi h hh x hx := by
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
    have hct := isCTGroupDatum hF 5 (by norm_num) ζ hζ
    exact (Subgroup.mem_normalizer_iff.1
      (iSup_le_normalizer_rootGroup (D := rootDatum hF 5) hct (octRootB_mem_roots' hi) hh) x).1 hx
  carrier_eq := by
    have h := (octComm_un5 hF).carrier_eq (i := 1) (j := ((4 : ℕ) : ℤ)) le_rfl le_rfl
    rw [← un5U_eq_iSup hF] at h
    exact h
  unique := octUnique_un5 hF
  reverse_eq i j hi _ hj := (octComm_un5 hF).reverse_eq hi hj
  subgroup i j hi _ hj := (octComm_un5 hF).exists_subgroup (U := unU hF 5)
    (fun k h1 h4 => octGroup_le_un5U hF h1 (by omega)) hi hj
  meet_one x hxB hx := by
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
    have hU : x ∈ unUneg hF 5 := by
      refine chainProd_subset (un5Oct hF) (unUneg hF 5) _ (fun k hk => ?_) hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
      obtain ⟨h1, h4⟩ := mem_intList_iff.1 hj
      exact octGroup_neg_le_un5Uneg hF h1 (by omega)
    have hmem : x ∈ borel (rootDatum hF 5) (levelTorus (unitaryInvolution F p f)) ⊓
        negUnipotent (rootDatum hF 5) := ⟨hxB, hU⟩
    rw [(CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ hζ).borel_inf_negUnipotent] at hmem
    exact Subgroup.mem_bot.1 hmem

end Octagon

end CFSG.Quasithin.H13.F431.Un
