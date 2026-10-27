module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSmallCore
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSmallLat
public import CFSG.CGT.PushingUpLit.BHS6.Basic
public import CFSG.GH74.KGroups.L3EpsOrder
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartTwo.Sec19 (IsProperParabolic)

theorem ksm_nine_ext {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hext : Sec4.IsExtOf P (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))) :
    ¬ 9 ∣ Nat.card P := by
  have hext' : ∃ K : Subgroup ↥P, ∃ _ : K.Normal,
      Nonempty (K ≃* Multiplicative (Fin 4 → ZMod 2)) ∧
        Nonempty (↥P ⧸ K ≃* Equiv.Perm (Fin 5)) := hext
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eQ⟩⟩ := hext'
  have hK : Nat.card K = 16 := by
    rw [Nat.card_congr eK.toEquiv]
    show Nat.card (Fin 4 → ZMod 2) = 16
    simp [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card]
  have hQ' : Nat.card (↥P ⧸ K) = 120 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have hPcard : Nat.card P = 1920 := by
    have h1 := Subgroup.card_mul_index (H := K)
    have h2 : K.index = 120 := hQ'
    rw [hK, h2] at h1
    omega
  rw [hPcard]
  norm_num

theorem ksm_nine_A10 {X : Type} [Group X] [Finite X]
    (hXA : Nonempty (X ≃* alternatingGroup (Fin 10))) : KSmNoNine X := by
  intro P hP
  unfold ParabolicShape at hP
  rcases hP with ⟨hempty, -⟩ | ⟨-, hext⟩
  · obtain ⟨e⟩ := hXA
    exact (hempty.false e).elim
  · exact ksm_nine_ext hext

theorem ksm_nine_of_nineFree {X : Type} [Group X] [Finite X]
    (hNF : CFSG.AGLEmbedding.ParabHub.NineFreeOver X) : KSmNoNine X := by
  intro P hP h9
  unfold ParabolicShape at hP
  rcases hP with ⟨-, hprop⟩ | ⟨-, hext⟩
  · unfold IsProperParabolic at hprop
    obtain ⟨hPtop, T, hTN⟩ := hprop
    have hTP : (T : Subgroup X) ≤ P := le_trans Subgroup.le_normalizer hTN
    have hT' : CFSG.RankThree.PartOne.IsSylowOf 2 (T : Subgroup X) ⊤ :=
      CFSG.ABGLocalTools.isSylowOf_iff.1 (ksm_isSylow_top_of_sylow T)
    have hT := CFSG.CGT.PushingUpLit.BHS6.isSylowTwoOf_of_isSylowOf hT'
    exact hPtop (hNF _ P hT hTP h9)
  · exact ksm_nine_ext hext h9

theorem ksm_nine_of_card {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Nat.card X = n)
    (hn : ¬ 9 ∣ n) : KSmNoNine X := by
  intro P _ h9
  apply hn
  rw [← hX]
  exact dvd_trans h9 (Subgroup.card_subgroup_dvd_card P)

theorem ksm_card_sl_three_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1)) =
    168 := by
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  rw [CFSG.GH74.KGroups.L3Eps.card_specialLinear_three, hF]
  norm_num

theorem ksm_false_sp_four_two {X : Type} [Group X] (hX : CFSG.IsQuasisimple X)
    (h : Nonempty (X ≃* projSp 2 (GaloisField 2 1))) : False := by
  obtain ⟨e⟩ := h
  exact CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.SpFour.false_of_isQuasisimple_projSp_two_one hX e

theorem ksm_false_g_two_two
    {X : Type} [Group X]
    (hX : CFSG.IsQuasisimple X)
    (h : Sec8.IsoGTwoEven X 1) : False := by
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by
    rw [hcard]
    norm_num
  obtain ⟨φ⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK2
  exact CFSG.Quasithin.R3c2.not_isQuasisimple_quasithinG2_two hK2 (e.trans φ) hX

theorem ksm_nineFree_a_six {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 6)) : CFSG.AGLEmbedding.ParabHub.NineFreeOver X :=
  CFSG.AGLEmbedding.ParabHub.NineFreeOver.of_mulEquiv e.symm
    CFSG.AGLEmbedding.ParabHub.nineFreeOver_alt_six

theorem ksm_nineFree_u_three_three
    {X : Type} [Group X]
    (e : X ≃* projSU 3 3 1) : CFSG.AGLEmbedding.ParabHub.NineFreeOver X := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 3 1 := by
    unfold CFSG.Open.StatedLieAdmissible
    norm_num
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hm : CFSG.Open.StatedClassicalModel X .PSU 3 3 1 :=
    ⟨hadm, GaloisField 3 (2 * 1), inferInstance, inferInstance, hF,
      ⟨e.trans (CFSG.PGLModel.projSUEquivStatedProj 3 3 1)⟩⟩
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, hm⟩)
  exact CFSG.AGLEmbedding.ParabHub.NineFreeOver.of_mulEquiv e'.symm
    CFSG.AGLEmbedding.ParabHub.nineFreeOver_u33

end CFSG.RankThree.PartTwo.Late
