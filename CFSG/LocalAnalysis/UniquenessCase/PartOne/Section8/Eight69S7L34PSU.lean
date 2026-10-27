module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34Basic
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

private theorem isSolvable_outer_psu_three {X : Type} [Group X] {p m : ℕ}
    (h : LieModel X .PSU 3 p m) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
  (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier
    (H := X) (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))).2

private theorem card_frattini_le_eight_of_sylow_psu_three {X : Type} [Group X] [Finite X]
    {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : LieModel X .PSU 3 p m) (S : Sylow 2 X)
    {R : Subgroup X} (hRS : R ≤ S) : Nat.card (↥R ⧸ frattini ↥R) ≤ 8 := by
  have hm : m ≠ 0 := by
    have := h.admissible.2.1
    omega
  have hp2 : p ≠ 2 := by
    have := hp.two_le
    omega
  have hLn : CFSG.GH74.GLS.IVK.IsLnEps 3 X (-1) (p ^ m) := by
    obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
    exact Or.inr ⟨rfl, K, hfield, hfinite, hK, ⟨e⟩⟩
  have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
  have hmod : p ^ m % 4 = 1 ∨ p ^ m % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hmod with hmod | hmod
  · obtain ⟨n, hn, ⟨e⟩⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_sd hp hp2 hLn hmod
        (Nat.one_lt_pow hm hp.one_lt) S
    have hR2 : IsPGroup 2 ↥R :=
      S.isPGroup'.of_injective (Subgroup.inclusion hRS) (Subgroup.inclusion_injective hRS)
    have hTG : CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups ↥(S : Subgroup X) :=
      CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv e
        (CFSG.GF2Type.Aschbacher1976Common.twoGen_semidihedral n hn)
    exact (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_frattini_le_four_of_twoGen
      hTG hRS hR2).trans (by norm_num)
  · obtain ⟨n, hn, ⟨e⟩⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_wr hp hp2 hLn hmod S
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType.card_le_eight
      (S := (S : Subgroup X)) S.isPGroup' (by omega) e hRS

theorem not_hasL34Section_mulAut_of_lieModel_psu_three {X : Type} [Group X] [Finite X] {p m : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h : LieModel X .PSU 3 p m) :
    ¬ HasL34Section (⊤ : Subgroup (MulAut X)) := by
  refine not_hasL34Section_mulAut_of_isSolvable_outer (isSolvable_outer_psu_three h) ?_
  refine not_hasL34Section_of_card_frattini_le_eight
    (Classical.choice (Sylow.nonempty (p := 2) (G := X))) ?_
  intro R hR
  exact card_frattini_le_eight_of_sylow_psu_three hp hp5 h _ hR

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
