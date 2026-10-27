module

public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem delta_eq_sup_sup_of {A L : Subgroup G} {c : G} (hbal : Step143Balance)
    (h : Sec14Std G A c L) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) {X : Subgroup G}
    (hXΔ : X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)))
    (hLD : ∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
      lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) :
    delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X := by
  have hA := h.isE27'
  have hAmax := h.maximal_isElemAbelian
  apply le_antisymm
  · refine sSup_le fun P hP => ?_
    obtain ⟨hPq, hPa⟩ := hP
    have hP3 : ¬ 3 ∣ Nat.card P := (isPiSubgroup_piCompl_iff Nat.prime_three P).mp hPq.1.2.1
    refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA.1
      (by rw [hA.2]; norm_num) hPq.1.2.2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3) fun H hHA hH9 => ?_
    have hH : IsHyperplane A H := ⟨hHA, by rw [hA.2, hH9]; norm_num⟩
    by_cases haH : a ∈ H
    · have hK := pPrimeCoreOf_centralizer_le_sup hA hAmax hH.1
        (commutator_pPrimeCoreOf_le hbal h ha ha1 hΩ hH haH)
      refine (hPq.2 H hH).trans ?_
      rw [qBound]
      exact sup_le (sup_le (hK.trans le_sup_left) (le_sup_right.trans le_sup_left))
        ((hLD H hH haH).trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
    · have hAle := le_sup_zpowers_of_not_mem hA hH ha haH
      have hCA : P ⊓ Subgroup.centralizer (H : Set G) ≤
          P ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
        ⟨hx.1, mem_centralizer_of_le_sup hAle hx.2 (hPa hx.1)⟩
      exact hCA.trans ((inf_centralizer_le_xA hAmax hP3).trans (le_sup_right.trans le_sup_left))
  · have hmem := sup_pPrimeCoreOf_mem_scriptQ (LB := lB A) hA hAmax ha
    exact sup_le (le_delta hmem.1 hmem.2) hXΔ

end CFSG.RankThree.PartTwo.Sec14
