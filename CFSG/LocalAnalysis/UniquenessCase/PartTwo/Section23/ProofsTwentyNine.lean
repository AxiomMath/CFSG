module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsUniqueN
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847Fields
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFortyOneFrame
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineNormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNinePush
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim
import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem one_le_of_card_eq_two_pow_sub_one {A : Subgroup G} {m : ℕ}
    (h : Nat.card A = 2 ^ m - 1) : 1 ≤ m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  rw [hm0] at h
  simp at h
  have hpos : 0 < Nat.card A := Nat.card_pos
  omega

private theorem le_N_of_le_inf_normalizer (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hPush : Push2329 D Ch) {K A : Subgroup G} (hK : K ∈ calC D.M)
    (hA : A ≤ K ⊓ Subgroup.normalizer (D.T : Set G)) : A ≤ c.N := by
  have hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c (CFSG.Open.IsSubnormal.le hK.1) hK.2.1
  have hJleT : InS3.thompsonJ D.T ≤ D.T := by
    rw [InS3.thompsonJ_eq_quasithin]
    exact CFSG.Quasithin.B6.thompsonJ_le D.T
  refine hPush h1930 c h3 D.T le_rfl (Subgroup.le_normalizer)
    ⟨1, D.T.one_mem, le_sup_left⟩ (c.V_le_T h4 h1930) hJleT A (hA.trans inf_le_right) ?_
  exact (hA.trans inf_le_left).trans
    (hKCZ.trans (Subgroup.centralizer_le_normalizer (D.Z : Set G)))

private theorem alternative_one_of_le (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hPush : Push2329 D Ch) {K A : Subgroup G} (hK : K ∈ calC D.M) (hthin : F08.Thin8 K)
    {m : ℕ} (hm1 : 1 ≤ m)
    (hshape : IsSz (Bar2 K) m ∨
      ∃ e : ℕ, (2 ≤ m ∨ e ≤ 1) ∧ IsL2 (Bar2 K) (2 ^ e * m))
    (hA : A ≤ K ⊓ Subgroup.normalizer (D.T : Set G)) (hcard : Nat.card A = 2 ^ m - 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ∣ CFSG.Open.pRank 2 D.Z ∧
      (IsSz (Bar2 K) m ∨
        ∃ e : ℕ, (2 ≤ m ∨ e ≤ 1) ∧ IsL2 (Bar2 K) (2 ^ e * m)) ∧
      ∃ A : Subgroup G, IsInnerCartanOnL A K c.L D.T m := by
  have hAcN : A ≤ c.N := le_N_of_le_inf_normalizer D Ch c h1930 h4 h3 hPush hK hA
  have hoddA : Odd (Nat.card A) := by
    rw [hcard]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  obtain ⟨hcyc, hdvd⟩ :=
    Ctx23L.isCyclic_and_card_dvd_of_le D Ch c h1930 h4 h23 h847 hLN hK hthin
      (le_inf (hA.trans inf_le_left) hAcN) hoddA
  have hmdvd : m ∣ CFSG.Open.pRank 2 D.Z :=
    CFSG.Quasithin.Vol2.Ch11.SecA.dvd_of_two_pow_sub_one_dvd (by rwa [hcard] at hdvd)
  have hNL : c.N ≤ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_left.trans (Ctx23L.sup_le_N D Ch c))).mp hLN
  refine ⟨m, hm1, hmdvd, hshape, A, hA, hcyc, hcard, hAcN.trans hNL, ?_, ?_⟩
  · intro a ha
    exact Ctx23L.exists_inducedBar_conj_of_mem D Ch c h1930 h4 h23 hLN hK
      ⟨(hA.trans inf_le_left) ha, hAcN ha⟩
  · intro a ha h1
    exact Ctx23L.eq_one_of_inducedBar_one c h1930 h4 h847 hK hthin ((hA.trans inf_le_left) ha)
      (hoddA.of_dvd_nat (Subgroup.orderOf_dvd_natCard A ha)) (hNL (hAcN ha)) h1

private theorem alternative_one_of_isSz (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hPush : Push2329 D Ch) (hAut : KSzTwoAut) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : (K.subgroupOf D.M).Normal) {a : ℕ} (hSz : IsSz (Bar2 K) a) (haOdd : Odd a) :
    ∃ m : ℕ, 1 ≤ m ∧ m ∣ CFSG.Open.pRank 2 D.Z ∧
      (IsSz (Bar2 K) m ∨
        ∃ e : ℕ, (2 ≤ m ∨ e ≤ 1) ∧ IsL2 (Bar2 K) (2 ^ e * m)) ∧
      ∃ A : Subgroup G, IsInnerCartanOnL A K c.L D.T m := by
  obtain ⟨A, hA, hcard⟩ := exists_borelLift_of_isSz hAut D hK hKn hSz
  have hthin : F08.Thin8 K := thin8_of_isL2_or_isSz (Or.inr hSz)
  have ha1 : 1 ≤ a := by
    have := haOdd.pos
    omega
  exact alternative_one_of_le D Ch c h1930 h4 h23 h847 hLN h3 hPush hK hthin ha1
    (Or.inl hSz) hA hcard

private theorem alternative_one_of_isL2_odd (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hPush : Push2329 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : (K.subgroupOf D.M).Normal) {a : ℕ} (hL2 : IsL2 (Bar2 K) a) (haOdd : Odd a) :
    ∃ m : ℕ, 1 ≤ m ∧ m ∣ CFSG.Open.pRank 2 D.Z ∧
      (IsSz (Bar2 K) m ∨
        ∃ e : ℕ, (2 ≤ m ∨ e ≤ 1) ∧ IsL2 (Bar2 K) (2 ^ e * m)) ∧
      ∃ A : Subgroup G, IsInnerCartanOnL A K c.L D.T m := by
  obtain ⟨e, m, hk, A, hA, -, hcard, -⟩ := exists_borelLift_of_isL2 D hK hKn hL2
  have hthin : F08.Thin8 K := thin8_of_isL2_or_isSz (Or.inl hL2)
  have hm1 : 1 ≤ m := one_le_of_card_eq_two_pow_sub_one hcard
  have he : e ≤ 1 := by
    by_contra he
    have he1 : 1 ≤ e := by omega
    have h2e : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega : e ≠ 0)
    have h2a : 2 ∣ a := by
      rw [hk]
      exact h2e.mul_right m
    exact haOdd.not_two_dvd_nat h2a
  exact alternative_one_of_le D Ch c h1930 h4 h23 h847 hLN h3 hPush hK hthin hm1
    (Or.inr ⟨e, Or.inr he, by rw [← hk]; exact hL2⟩) hA hcard

private theorem alternative_one_of_isL2_two_mul (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hPush : Push2329 D Ch) (hField : FieldGen2329 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : (K.subgroupOf D.M).Normal) {a : ℕ} (hL2 : IsL2 (Bar2 K) (2 * a)) :
    ∃ m : ℕ, 1 ≤ m ∧ m ∣ CFSG.Open.pRank 2 D.Z ∧
      (IsSz (Bar2 K) m ∨
        ∃ e : ℕ, (2 ≤ m ∨ e ≤ 1) ∧ IsL2 (Bar2 K) (2 ^ e * m)) ∧
      ∃ A : Subgroup G, IsInnerCartanOnL A K c.L D.T m := by
  obtain ⟨e, m, hk, A, hA, -, hcard, hnot⟩ := exists_borelLift_of_isL2 D hK hKn hL2
  have hthin : F08.Thin8 K := thin8_of_isL2_or_isSz (Or.inl hL2)
  have hm1 : 1 ≤ m := one_le_of_card_eq_two_pow_sub_one hcard
  have hguard : 2 ≤ m ∨ e ≤ 1 := by
    by_cases hm2 : 2 ≤ m
    · exact Or.inl hm2
    · right
      by_contra he
      have he2 : 2 ≤ e := by omega
      have hmEq : m = 1 := by omega
      have hk2 : 2 ≤ 2 * a := s13_two_le_of_isL2 hL2
      obtain ⟨t, htK, htT, hnotx⟩ := hnot hmEq hk2
      have hL2e : IsL2 (Bar2 K) (2 ^ e) := by
        have h := hL2
        rw [hk, hmEq, mul_one] at h
        exact h
      obtain ⟨x, hx⟩ := hField h1930 c h3 K hK hKn e he2 hL2e t htK htT
      have h2a : 2 * a = 2 ^ e := by rw [hk, hmEq, mul_one]
      have haeq : a = 2 ^ (e - 1) := by
        have he' : e = (e - 1) + 1 := by omega
        rw [he', Nat.pow_succ'] at h2a
        exact Nat.mul_left_cancel (by norm_num) h2a
      have hexp : (2 * a) / 2 = 2 ^ (e - 1) := by
        rw [haeq]
        exact Nat.mul_div_right (2 ^ (e - 1)) (by norm_num)
      rw [hexp] at hnotx
      exact hnotx x hx
  exact alternative_one_of_le D Ch c h1930 h4 h23 h847 hLN h3 hPush hK hthin hm1
    (Or.inr ⟨e, hguard, by rw [← hk]; exact hL2⟩) hA hcard

private theorem false_of_isJ1 (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hLN : (c.L.subgroupOf c.N).Normal) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hPush : Push2329 D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : (K.subgroupOf D.M).Normal) (hJ1 : IsJ1 (Bar2 K)) : False := by
  obtain ⟨A, hA, hoddA, hnoncomm⟩ := exists_borelLift_of_isJ1 D hK hKn hJ1
  have hAcN : A ≤ c.N := le_N_of_le_inf_normalizer D Ch c h1930 h4 h3 hPush hK hA
  have hthin : F08.Thin8 K := thin8_of_isJ1_bar2 hJ1
  exact hnoncomm (Ctx23L.isMulCommutative_of_le D Ch c h1930 h4 h23 h847 hLN hK hthin
    (le_inf (hA.trans inf_le_left) hAcN) hoddA)

private theorem alternative_two_of_isL2Odd (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch)
    (h1930 : H1930 D) {K : Subgroup G} (hK : K ∈ calC D.M) (h2112 : S21_12 D Ch)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hL2q : IsL2Odd (Bar2 K) q) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd (Bar2 K) q ∧
      ⁅CFSG.Quasithin.opResidual 3 c.B, K⁆ ≤ CFSG.Open.pCoreOf 2 K := by
  haveI : IsSimpleGroup (Bar2 K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hL2q
  have hcenter : Subgroup.center (Bar2 K) = ⊥ := uc22p21k_center_eq_bot hK.2.2
  obtain ⟨e⟩ : Nonempty (BarInf K ≃* Bar2 K) :=
    uc22p21k_barInf_equiv_of_center_bot hK.2.2 hcenter
  have hChev : IsChev (BarInf K) q :=
    ⟨.PSL, 2, 1, hL2q.admissible, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2q⟩
  exact ⟨q, hq, hq2, hL2q, (h2112 h1930 c.toCtx23.toCtx21 K hK q hq hq2 hChev).2⟩

theorem s23_29_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h52 : S23_5_2 D Ch) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D)
    (h847 : R847ThinCZ D) (h8 : S23_8 D Ch) (h2112 : S21_12 D Ch)
    (hAut : KSzTwoAut) (hPush : Push2329 D Ch) (hField : FieldGen2329 D Ch) : S23_29 D Ch := by
  intro h1930 c K hK
  have h3 : 3 ≤ CFSG.Open.pRank 2 D.Z :=
    Ctx23L.three_le_pRank_Z D Ch hE h207 h52 h23 h1930 c
  obtain ⟨hKn, hcase⟩ := h8 h1930 c K hK
  have hLN : (c.L.subgroupOf c.N).Normal := Ctx23L.normal_L_N D Ch h4 h23 h208 h1930 c
  rcases hcase with ⟨a, haOdd, hshape⟩ | ⟨hcase2, -⟩
  · rcases hshape with hL2 | hSz
    · exact Or.inl (alternative_one_of_isL2_odd D Ch c h1930 h4 h23 h847 hLN h3 hPush
        hK hKn hL2 haOdd)
    · exact Or.inl (alternative_one_of_isSz D Ch c h1930 h4 h23 h847 hLN h3 hPush hAut
        hK hKn hSz haOdd)
  · rcases hcase2 with ⟨q, hq, hq2, hL2q⟩ | hJ1 | ⟨a, hL2⟩
    · exact Or.inr (alternative_two_of_isL2Odd D Ch c h1930 hK h2112 hq hq2 hL2q)
    · exact (false_of_isJ1 D Ch c h1930 h4 h23 h847 hLN h3 hPush hK hKn hJ1).elim
    · exact Or.inl (alternative_one_of_isL2_two_mul D Ch c h1930 h4 h23 h847 hLN h3 hPush
        hField hK hKn hL2)

end CFSG.LocalAnalysis.UniquenessCase.UC22
