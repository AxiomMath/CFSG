module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofPGroup
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.Models.PGLSimple
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankBridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsYKO3

open CFSG
open CFSG.Assembly.RankThreeEven (projSL)

private theorem seven_dvd_card_projSL_three_two :
    7 ∣ Nat.card (projSL 3 (GaloisField 2 1)) := by
  rw [Nat.card_congr (CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField 2 1)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
    GaloisField.card 2 1 (by norm_num)]
  decide

theorem eq_one_of_not_seven_dvd {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hK : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 1)))
    {H : Type*} [Group H] [Finite H] (h7 : ¬ 7 ∣ Nat.card H) (f : K →* H) : f = 1 := by
  obtain ⟨e⟩ := hK
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, f k ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext h)
  have hNsolv : Group.IsSolvable (CFSG.pCore 2 K) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := K)).isNilpotent
    infer_instance
  have hsimple : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) := by
    have : IsSimpleGroup (projSL 3 (GaloisField 2 1)) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num))
        (Or.inl (by norm_num))
    exact e.isSimpleGroup
  have hker : f.ker ≤ CFSG.pCore 2 K :=
    Sec11.LSSolvableProof.ker_le_of_perfect hNsolv hsimple f ⟨k, hk⟩
  have h7K : 7 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
    rw [Nat.card_congr e.toEquiv]
    exact seven_dvd_card_projSL_three_two
  have h7ker : 7 ∣ f.ker.index :=
    h7K.trans (by rw [← Subgroup.index_eq_card]; exact Subgroup.index_dvd_of_le hker)
  rw [Subgroup.index_ker] at h7ker
  exact h7 (h7ker.trans (Subgroup.card_subgroup_dvd_card f.range))

theorem eq_one_of_pRank_le_two_five {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hK : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 1)))
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 5 P) (hrank : CFSG.pRank 5 P ≤ 2)
    (ρ : K →* MulAut P) : ρ = 1 := by
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases hnt : Nontrivial P
  swap
  ·
    rw [not_nontrivial_iff_subsingleton] at hnt
    ext k x
    exact Subsingleton.elim _ _
  obtain ⟨D, hDc, -, hDexp, hDcomm, -, hker⟩ :=
    SectionRank.Ccomm.supercritical_witness (p := 5) (by norm_num) hP
  have hDp : IsPGroup 5 D := hP.to_subgroup D
  have hDexp' : ∀ x : D, x ^ 5 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDclass : commutator D ≤ Subgroup.center D :=
    Res11.commutator_le_center_of_le_centralizer hDcomm
  have hDrank : CFSG.pRank 5 D ≤ 2 :=
    (RankThree.PartOne.FixedRank36.pRank_le_of_injective D.subtype D.subtype_injective).trans hrank
  have hQrank : CFSG.pRank 5 (D ⧸ commutator D) ≤ 2 :=
    (class_two_small_rank_order_bounds hDp hDexp' hDclass).1 hDrank
  have hΦ : frattini D = commutator D := frattini_eq_commutator hDp hDexp'
  have : Fact (IsPGroup 5 D) := ⟨hDp⟩
  have hWel : IsElementaryAbelian 5 (D ⧸ frattini D) :=
    CFSG.isElementaryAbelian_quotient_frattini (R := D) (p := 5)
  have hWrank : CFSG.pRank 5 (D ⧸ frattini D) ≤ 2 :=
    (RankThree.PartOne.FixedRank36.pRank_le_of_injective
      (QuotientGroup.quotientMulEquivOfEq hΦ).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hΦ).injective).trans hQrank
  have hWexp : ∀ x : D ⧸ frattini D, x ^ 5 = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hWel.exponent_dvd_p x
  obtain ⟨n, hn⟩ := (hDp.to_quotient (frattini D)).exists_card_eq
  have hn2 : n ≤ 2 := by
    rw [← pRank_eq_of_isMulCommutative hp.out hWexp hWel.toIsMulCommutative hn]
    exact hWrank
  obtain ⟨eW⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (fun a b => hWel.toIsMulCommutative.is_comm.comm a b) hWexp hn
  have h7 : ¬ 7 ∣ Nat.card (MulAut (D ⧸ frattini D)) := by
    rw [SectionRank.Ccomm.card_mulAut_eq_card_GL eW, SectionRank.Ccomm.card_GL_zmod]
    interval_cases n <;> decide
  have hσ1 : (SectionRank.Ccomm.frattiniAction D).comp ρ = 1 :=
    eq_one_of_not_seven_dvd hK h7 _
  apply Res11.eq_one_of_isPGroup_range ρ (p := 5)
  refine hker.to_le ?_
  rintro _ ⟨k, rfl⟩
  rw [MonoidHom.mem_ker]
  exact DFunLike.congr_fun hσ1 k

end CFSG.RankThree.PartTwo.Sec20.SimsYKO3
