module

public import CFSG.Open.PGLModelStated
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.GH74.Filter.Orthogonal.SymplecticSix
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
public import CFSG.CGT.PushingUpLit.A78.NoSU4
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem e16Lie_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ E : Subgroup B, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16) :
    ∃ E : Subgroup A, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨E, hE, hcard⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, CFSG.Open.IsElemAbelian.map hE e.symm.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hcard]

theorem e16Lie_exists_of_four_le_pRank {G : Type*} [Group G] [Finite G]
    (h : 4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G)) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two h
  exact ⟨E, hE, by norm_num [hcard]⟩

theorem exists_E16_projSU_four_two : ∃ E : Subgroup (projSU 4 2 1),
    CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec21.U4Lines.nonempty_projSU_mulEquiv_SU 1 one_pos
  obtain ⟨E, hE, hcard⟩ := CFSG.CGT.PushingUpLit.A78.su4_exists_elemAbelian (f := 1) le_rfl
  exact e16Lie_of_mulEquiv e ⟨E, hE, by norm_num [hcard]⟩

theorem exists_E16_projSL_two_thirtytwo : ∃ E : Subgroup (projSL 2 (GaloisField 2 5)),
    CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := 2) (a := 1) (b := 1)
    (K := GaloisField 2 5) le_rfl (by norm_num) (GaloisField.card 2 5 (by norm_num))
  exact e16Lie_of_mulEquiv (CFSG.PGLModel.projSLEquivStatedProj 2 (GaloisField 2 5))
    (e16Lie_exists_of_four_le_pRank (le_trans (by norm_num) h))

theorem exists_E16_projSL_three_four : ∃ E : Subgroup (projSL 3 (GaloisField 2 2)),
    CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := 3) (a := 1) (b := 2)
    (K := GaloisField 2 2) le_rfl (by norm_num) (GaloisField.card 2 2 (by norm_num))
  exact e16Lie_of_mulEquiv (CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField 2 2))
    (e16Lie_exists_of_four_le_pRank (le_trans (by norm_num) h))

theorem exists_E16_statedSL_three_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ E : Subgroup (CFSG.Assembly.LowTwoRank.StatedSL 3 K),
      CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  have hK2 : Nat.card K = 2 ^ 2 := hK.trans (by norm_num)
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK2
  have hφ : Function.Injective (CFSG.SectionRank.ClassicalOdd.linHom (K := K) 3 1 2) :=
    CFSG.SectionRank.ClassicalOdd.linHom_injective (by norm_num)
  have hle : (⊤ : Subgroup (Multiplicative (Fin 1 × Fin 2 → K))).map
      (CFSG.SectionRank.ClassicalOdd.linHom (K := K) 3 1 2) ≤
        CFSG.Assembly.LowTwoRank.StatedSL 3 K := by
    rintro _ ⟨s, -, rfl⟩
    exact Subgroup.subset_closure (CFSG.SectionRank.ClassicalOdd.det_eq_one_of_hom
      (p := 2) (CFSG.SectionRank.ClassicalOdd.linHom (K := K) 3 1 2) s)
  have hTop : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup (Multiplicative (Fin 1 × Fin 2 → K))) :=
    ⟨inferInstance, fun x _ => CFSG.SectionRank.ClassicalOdd.pow_char_eq_one (K := K) x⟩
  refine ⟨((⊤ : Subgroup (Multiplicative (Fin 1 × Fin 2 → K))).map
      (CFSG.SectionRank.ClassicalOdd.linHom (K := K) 3 1 2)).subgroupOf _, ?_, ?_⟩
  · exact CFSG.Open.IsElemAbelian.subgroupOf
      (CFSG.Open.IsElemAbelian.map hTop (CFSG.SectionRank.ClassicalOdd.linHom (K := K) 3 1 2)) _
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective hφ, Subgroup.card_top,
      CFSG.SectionRank.ClassicalOdd.card_multiplicative_fun (P := Fin 1 × Fin 2) hK2]
    norm_num [Fintype.card_prod]

theorem exists_E16_projSp_three_two : ∃ E : Subgroup (projSp 3 (GaloisField 2 1)),
    CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  have h := CFSG.GH74.Filter.le_pRank_Sp_sym (n := 3) (K := GaloisField 2 1) (by norm_num)
    (GaloisField.card 2 1 (by norm_num))
  exact e16Lie_of_mulEquiv (CFSG.PGLModel.projSpEquivStatedProj 3 (GaloisField 2 1))
    (e16Lie_exists_of_four_le_pRank (le_trans (by norm_num [Nat.choose]) h))

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
