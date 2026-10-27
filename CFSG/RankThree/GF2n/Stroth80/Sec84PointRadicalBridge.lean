module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs
public import CFSG.ClassicalGroups.Alternating.PointRadicalCount

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating
open scoped Matrix

theorem card_le_of_no_nonA2 {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 2 ≤ m)
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) (P : Subgroup (GL (Fin m ⊕ Fin m) K))
    (hP : P ≤ LspGL m K u) (hno : ∀ A ∈ P, ¬ SpNonA2 A) :
    Nat.card ↥P ≤ Nat.card K ^ (m - 1) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨y0, hy0⟩ : ∃ y0 : Fin m ⊕ Fin m → K, spForm m K y0 u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu ((spForm_nondegenerate (m := m) (K := K)).2 u hcon)
  obtain ⟨P', hP'def⟩ : ∃ P' : Subgroup (LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)),
      P' = P.map (Matrix.GeneralLinearGroup.toLin :
        GL (Fin m ⊕ Fin m) K ≃*
          LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)).toMonoidHom := ⟨_, rfl⟩
  have hcardEq : Nat.card ↥P' = Nat.card ↥P := by
    rw [hP'def]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  have hP'le : P' ≤ pointRadical (spForm m K) spForm_isAlt u := by
    rw [hP'def]
    rintro _ ⟨A, hAP, rfl⟩
    obtain ⟨hA, hmem⟩ := mem_LspGL_iff.mp (hP hAP)
    rw [mem_Lsp] at hmem
    have hEq : ((spEquiv (m := m) (K := K) ⟨A, hA⟩ : Gsp (spForm m K)) :
        LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) =
          Matrix.GeneralLinearGroup.toLin A := by
      refine Units.ext (LinearMap.ext fun v => ?_)
      rw [Matrix.GeneralLinearGroup.toLin_apply]
      exact spEquiv_app (m := m) (K := K) ⟨A, hA⟩ v
    show Matrix.GeneralLinearGroup.toLin A ∈ pointRadical (spForm m K) spForm_isAlt u
    rw [← hEq]
    exact hmem
  have hno' : ∀ (w : Fin m ⊕ Fin m → K) (c : K), spForm m K u w = 0 →
      siegel (spForm m K) spForm_isAlt u w c ∈ P' → c = 0 ∨ ∃ s : K, w = s • u := by
    intro w c hw hmem
    left
    rw [hP'def] at hmem
    obtain ⟨A, hAP, hAe⟩ := Subgroup.mem_map.mp hmem
    have hAe' : Matrix.GeneralLinearGroup.toLin A =
        siegel (spForm m K) spForm_isAlt u w c := hAe
    have hnA : ∀ y : Fin m ⊕ Fin m → K,
        spForm m K y ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = 0 := by
      intro y
      by_contra hne
      exact hno A hAP ⟨y, hne⟩
    have hzero : ∀ y : Fin m ⊕ Fin m → K, c * spForm m K y u ^ 2 = 0 := by
      intro y
      have hsA : (siegel (spForm m K) spForm_isAlt u w c :
          (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) y =
            (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y := by
        rw [← hAe']
        exact Matrix.GeneralLinearGroup.toLin_apply A y
      rw [← siegel_form_apply_self h2 spForm_isAlt hw c y, hsA]
      exact hnA y
    rcases mul_eq_zero.mp (hzero y0) with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 hy0)
  have hcard := card_le_of_no_c2 spForm_isAlt spForm_nondegenerate hu hm finrank_spSpace P' hP'le
    hno'
  rw [hcardEq] at hcard
  exact hcard

end CFSG.RankThree.GF2n.Stroth80
