module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8Minus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem t3P0H_map_conj_isParabolicTwo (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h : ↥(T3H K b c)) :
    IsParabolicTwo ↥(T3H K b c) ((t3P0H K b c).map (MulAut.conj h).toMonoidHom) := by
  have h1 : IsParabolicTwo ↥(T3H K b c) (t3P0H K b c) := by
    simpa only [t3P0H] using
      (t3P0_isParabolic hirr).map (t3e K b c).toMonoidHom
        (by simpa using (t3e K b c).surjective)
  exact h1.map (MulAut.conj h).toMonoidHom (MulAut.conj h).surjective

theorem map_conj_t3UH_le_map_conj_t3P0H (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h : ↥(T3H K b c)) :
    (t3UH K b c).map (MulAut.conj h).toMonoidHom ≤
      (t3P0H K b c).map (MulAut.conj h).toMonoidHom := by
  have h1 : t3UH K b c ≤ t3P0H K b c := by
    simpa only [t3UH, t3P0H] using
      Subgroup.map_mono (f := (t3e K b c).toMonoidHom) (t3U_le_t3P0 hirr)
  exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) h1

theorem t3P0H_map_conj_not_le_t3PℓH (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h : ↥(T3H K b c)) :
    ¬ (t3P0H K b c).map (MulAut.conj h).toMonoidHom ≤ t3PℓH K b c h := by
  intro hle
  exact t3P0H_not_le_t3Pℓ0H hirr
    ((Subgroup.map_le_map_iff_of_injective (MulAut.conj h).injective).mp hle)

theorem t3P0H_map_conj_ne_top (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h : ↥(T3H K b c)) :
    (t3P0H K b c).map (MulAut.conj h).toMonoidHom ≠ ⊤ := by
  intro htop
  apply t3P0_ne_top hirr
  have hH : t3P0H K b c = ⊤ := by
    rw [← Subgroup.map_equiv_top (MulAut.conj h)] at htop
    exact Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective htop
  rw [t3P0H] at hH
  rw [← Subgroup.map_equiv_top (t3e K b c)] at hH
  exact Subgroup.map_injective (f := (t3e K b c).toMonoidHom) (t3e K b c).injective hH

theorem t3P0H_map_conj_le_of_parabolic (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (S : Sylow 2 ↥(T3H K b c)) (h : ↥(T3H K b c))
    (hS : (S : Subgroup ↥(T3H K b c)) = (t3UH K b c).map (MulAut.conj h).toMonoidHom)
    {P : Subgroup ↥(T3H K b c)} (hP : IsParabolicTwo ↥(T3H K b c) P)
    (hSP : (S : Subgroup ↥(T3H K b c)) ≤ P) (hnot : ¬ P ≤ t3PℓH K b c h) :
    (t3P0H K b c).map (MulAut.conj h).toMonoidHom ≤ P := by
  have hnorm : Subgroup.normalizer (S : Set ↥(T3H K b c)) ≤ P :=
    IsParabolicTwo.normalizer_le hP S hSP
  have hB : (t3BH K b c).map (MulAut.conj h).toMonoidHom =
      Subgroup.normalizer (S : Set ↥(T3H K b c)) := by
    rw [t3BH_eq_normalizer hirr, Subgroup.map_equiv_normalizer_eq, ← hS]
    rfl
  exact t3P0H_map_conj_le_of_borel_le_of_not_le_point hirr h (by rw [hB]; exact hnorm) hnot

end CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi
