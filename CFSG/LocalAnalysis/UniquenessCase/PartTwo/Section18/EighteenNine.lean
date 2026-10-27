module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenNineB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenPiCV
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MbarSigmaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaMinusThreeNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

section Certified


@[expose] def Gap_18_9_WC (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  V₀ = ⊥ →
    IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 2 →
    SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 2)
      (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 3 →
    ∃ i ≤ 1, normalizer (CFSG.Quasithin.E3.wClos V i D.T : Set G) ≤ D.M ∧
      centralizer (CFSG.Quasithin.E3.cClos V (D.k + i) D.T : Set G) ≤ D.M

theorem s18_9_false_of_omegaMinus_four {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G}
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h127 : R127 D)
    (h1742 : S17.R17_42At D V₀ V) (h641 : S17.R17_64_1At D V₀ V)
    (h642 : S17.R17_64_2At D V₀ V) (h643 : S17.R17_64_3At D V₀ V)
    (hK4m : Inputs1719.K_O4m4_ThreeNat) (h : Hyp18 D V₀ V p L)
    (hO : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 2)
    (hS : SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 2)
      (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 3) : False := by
  have hL2 := isL2_of_isOmegaMinus_four (by norm_num) hO
  have hcong := cong_of_isL2_barSub D h h1742 h641 h642 h643 hL2
  have hp := D.sig_prime p h.hp
  have hp17 : p = 17 := by
    have h17 : (p : ℤ) ∣ 17 := by
      have := Int.ModEq.dvd hcong.symm
      norm_num at this
      exact this
    have : p ∣ 17 := by exact_mod_cast h17
    exact (Nat.prime_dvd_prime_iff_eq hp.1 (by norm_num)).1 this
  subst hp17
  have hcard : Nat.card V₀ ≤ 4 := by
    have := (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
    omega
  have h2 := S17.two_le_pRank_mbar_of_mem_sig h.hyp125 hx h61 h127 hcard h.hp
  have hLM : L ≤ D.M := (S17.calLp_subset_calC D 17 h.hL).1.le
  have hXM : conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le hLM
  have hXY := barSub_mono V₀ V h.hyp125.isElemAbelian hXM
  have hnorm := barSub_subgroupOf_mbar_normal (V₀ := V₀) (V := V) h.hyp125.isElemAbelian hXM
    (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have h1 := hK4m (Vtil V₀ V h.hyp125.isElemAbelian)
    (s15_Infra_vtil_sq_eq_one V₀ V h.hyp125.isElemAbelian)
    (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))
    (Mbar D.M V₀ V h.hyp125.isElemAbelian) hXY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hnorm) hO hS
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h2
  omega

theorem s18_9_false_of_omegaMinus_six_of_bot {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) (hK6m : Inputs1719.K_O6m4_ThreeNatM)
    (h : Hyp18 D V₀ V p L) (hgap : Gap_18_9_WC D V₀ V p L h) (hV₀ : V₀ = ⊥)
    (hO : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 2)
    (hS : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 2)
      (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 3) : False := by
  obtain ⟨i, hi, hN, hC⟩ := hgap hV₀ hO hS
  have hm : MBarGT D.M V₀ V (D.k + i) := by
    have hpair := h.hyp125.pairFacts
    have hLM : L ≤ D.M := (S17.calLp_subset_calC D p h.hL).1.le
    have hXM : conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le hLM
    have hXY := barSub_mono V₀ V h.hyp125.isElemAbelian hXM
    have hnorm := barSub_subgroupOf_mbar_normal (V₀ := V₀) (V := V) h.hyp125.isElemAbelian hXM
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
    have h6 := hK6m (Vtil V₀ V h.hyp125.isElemAbelian)
      (s15_Infra_vtil_sq_eq_one V₀ V h.hyp125.isElemAbelian)
      (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))
      (Mbar D.M V₀ V h.hyp125.isElemAbelian) hXY
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hnorm) hO hS
    rw [mBarGT_iff_lt_mBar D.M V₀ V h.hyp125.isElemAbelian hpair.le hpair.le_normalizer
      hpair.le_normalizer₀]
    have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
    unfold mBar
    omega
  rcases twelve_ten_two D hx h61 h126 h111 h.hyp125 hV₀ hm with h1 | h1
  · exact h1 hN
  · exact h1 hC

theorem eighteen_nine {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h127 : R127 D)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (h1742 : S17.R17_42At D V₀ V) (h641 : S17.R17_64_1At D V₀ V)
    (h642 : S17.R17_64_2At D V₀ V) (h643 : S17.R17_64_3At D V₀ V)
    (h171 : ∀ hV : Hyp125 D V₀ V, S17.R17_1At D V₀ V hV) (hKU : Inputs1719.KU4U5CartanQuotient)
    (h8103 : F08.R8103 D) (h8106 : F08.R8106 D)
    (hK4m : Inputs1719.K_O4m4_ThreeNat) (hK6m : Inputs1719.K_O6m4_ThreeNatM)
    (h : Hyp18 D V₀ V p L) (hgap : Gap_18_9_WC D V₀ V p L h) :
    R18_9At D V₀ V p L h := by
  rintro (⟨hO, hS⟩ | ⟨hO, hS⟩)
  · by_cases hV₀ : V₀ = ⊥
    · exact s18_9_false_of_omegaMinus_six_of_bot hx h61 h126 h111 hK6m h hgap hV₀ hO hS
    · exact false_of_isU4_two_of_ne_bot h171 h1742 hKU h8103 h8106 h hV₀
        (isU4_of_isOmegaMinus hO)
  · exact s18_9_false_of_omegaMinus_four hx h61 h127 h1742 h641 h642 h643 hK4m h hO hS

theorem eighteen_thirteen_d {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hm : MBarGT D.M V₀ V 3)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h8 : R18_8At D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h) (h11 : R18_11At D V₀ V p L h)
    (h12 : R18_12At D V₀ V p L h)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h117 : C117 D V₀ V) (hH1 : K_18_13_H1)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D)
    (h1742 : S17.R17_42At D V₀ V)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (h171 : ∀ hV : Hyp125 D V₀ V, S17.R17_1At D V₀ V hV)
    (hKU : Inputs1719.KU4U5CartanQuotient) (h8103 : F08.R8103 D) (h8106 : F08.R8106 D)
    (hK : Inputs1719.K_SU44_TwoNat)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V)
    (hK4m : Inputs1719.K_O4m4_ThreeNat) (hK6m : Inputs1719.K_O6m4_ThreeNatM)
    (hgap : Gap_18_9_WC D V₀ V p L h) :
    R18_13At D V₀ V p L h :=
  eighteen_thirteen_c h hm h6b h7b h8
    (eighteen_nine hx h61 h127 h126 h111 h1742 h641 h642 h643 h171 hKU h8103 h8106 hK4m hK6m h
      hgap)
    h10 h11 h12 h17_66_1 h18_4 h117 hH1 hx h61 h127 h1214 h1742 h126 h111 h171 hKU h8103 h8106
    hK

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
