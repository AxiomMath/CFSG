module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208KCommon
import CFSG.RankThree.PartTwo.Sec19.Census194.RankOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagSz
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {X : Type} [Group X]

theorem s208k_false_of_solvable_overgroups
    (h1 : ∀ T : Sylow 2 X, ∀ J : Subgroup X, normalizer ((T : Subgroup X) : Set X) ≤ J →
      J ≠ ⊤ → Group.IsSolvable ↥J)
    {P : Subgroup X} (hP : IsParabolicTwo X P) (hPX : P ≠ ⊤) {n : ℕ} (hQ : S208kQ P n) :
    False := by
  obtain ⟨T, hTP⟩ := hP
  exact s208k_not_isSolvable hQ (h1 T P hTP hPX)

variable [Finite X]

private theorem s208k_isSolvable_of_eq {T : Sylow 2 X} {J : Subgroup X}
    (h : J = normalizer ((T : Subgroup X) : Set X) ∨ J = ⊤) (hJ : J ≠ ⊤) :
    Group.IsSolvable ↥J := by
  rcases h with rfl | rfl
  · exact CFSG.ComponentClassification.AS76b.isSolvable_normalizer_sylow_two T
  · exact absurd rfl hJ

theorem s208k_solvable_overgroups_of_isL2 {m : ℕ} (hX : IsL2 X m) (T : Sylow 2 X)
    (J : Subgroup X) (hTJ : normalizer ((T : Subgroup X) : Set X) ≤ J) (hJ : J ≠ ⊤) :
    Group.IsSolvable ↥J :=
  s208k_isSolvable_of_eq (CFSG.RankThree.PartTwo.Sec19.eq_normalizer_or_top_psl_two
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)) T J hTJ) hJ

theorem s208k_solvable_overgroups_of_isU3 {m : ℕ} (hX : IsU3 X m) (T : Sylow 2 X)
    (J : Subgroup X) (hTJ : normalizer ((T : Subgroup X) : Set X) ≤ J) (hJ : J ≠ ⊤) :
    Group.IsSolvable ↥J :=
  s208k_isSolvable_of_eq (CFSG.RankThree.PartTwo.Sec19.eq_normalizer_or_top_psu_three
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)) T J hTJ) hJ

theorem s208k_solvable_overgroups_of_isSz {m : ℕ} (hX : IsSz X m) (T : Sylow 2 X)
    (J : Subgroup X) (hTJ : normalizer ((T : Subgroup X) : Set X) ≤ J) (hJ : J ≠ ⊤) :
    Group.IsSolvable ↥J := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := (CFSG.Blueprint.LieModel.suzukiModel hX).2
  have hco := isCoatom_normalizer_sylow_of_mulEquiv e
    (isCoatom_normalizer_sylow_suzukiGroup ha hcard) T
  refine s208k_isSolvable_of_eq (T := T) ?_ hJ
  rcases eq_or_lt_of_le hTJ with h | h
  · exact Or.inl h.symm
  · exact Or.inr (hco.2 J h)

theorem s208k_solvable_overgroups_of_isSU3 {m : ℕ} (hX : IsSU3 X m) (T : Sylow 2 X)
    (J : Subgroup X) (hTJ : normalizer ((T : Subgroup X) : Set X) ≤ J) (hJ : J ≠ ⊤) :
    Group.IsSolvable ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective (QuotientGroup.mk' (center X)) := QuotientGroup.mk'_surjective _
  have : Finite (X ⧸ center X) := Finite.of_surjective _ hπ
  have hker : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  have hkJ : (QuotientGroup.mk' (center X)).ker ≤ J := by
    rw [hker]
    exact (center_le_normalizer _).trans hTJ
  have hle : normalizer (((T.mapSurjective hπ : Sylow 2 (X ⧸ center X)) :
      Subgroup (X ⧸ center X)) : Set (X ⧸ center X)) ≤ J.map (QuotientGroup.mk' (center X)) := by
    rw [Sylow.coe_mapSurjective]
    exact (CFSG.AGLEmbedding.ParabPrime.normalizer_map_le T hπ hker.le).trans (map_mono hTJ)
  rcases CFSG.RankThree.PartTwo.Sec19.eq_normalizer_or_top_psu_three
      (CFSG.Blueprint.LieModel.statedClassicalModel hX.2 (by decide)) _ _ hle with h | h
  · have : Group.IsSolvable ↥(J.map (QuotientGroup.mk' (center X))) := by
      rw [h]
      exact CFSG.ComponentClassification.AS76b.isSolvable_normalizer_sylow_two _
    have : Group.IsSolvable ↥(QuotientGroup.mk' (center X)).ker := by
      rw [hker]
      exact Group.isSolvable_of_comm fun a b => Subtype.ext ((mem_center_iff.mp b.2) a)
    exact CFSG.Quasithin.B6.isSolvable_of_map _ J hkJ
  · exact absurd (show J = ⊤ by rw [← comap_map_eq_self hkJ, h, comap_top]) hJ

theorem s208k_false_of_rankOne {m : ℕ} (hX : IsSz X m ∨ IsL2 X m ∨ IsU3 X m ∨ IsSU3 X m)
    {P : Subgroup X} (hP : IsParabolicTwo X P) (hPX : P ≠ ⊤) {n : ℕ} (hQ : S208kQ P n) :
    False := by
  refine s208k_false_of_solvable_overgroups (fun T J hTJ hJ => ?_) hP hPX hQ
  rcases hX with h | h | h | h
  · exact s208k_solvable_overgroups_of_isSz h T J hTJ hJ
  · exact s208k_solvable_overgroups_of_isL2 h T J hTJ hJ
  · exact s208k_solvable_overgroups_of_isU3 h T J hTJ hJ
  · exact s208k_solvable_overgroups_of_isSU3 h T J hTJ hJ

end CFSG.LocalAnalysis.UniquenessCase.UC22
