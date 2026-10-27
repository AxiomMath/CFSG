module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S219Sig3
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Ta
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08Use
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Ug
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_su3_oddN (D : Data G) (Ch : Choice2011 G)
    (h869N : F08.R869N D) (hV : S22_V D Ch) (h846 : F08.R846 D) (h1930 : H1930 D)
    (c : Ctx22b D Ch) (hn3 : 3 ≤ c.n) (hm6 : c.n ≠ 6) {K : Subgroup G} (hKC : K ∈ calC D.M)
    (hN : (K.subgroupOf D.M).Normal) {n : ℕ} (hsu : IsSU3 ↥(mbarImage D.M c.V K) n)
    (hodd : Odd n) : c.n ≤ n := by
  by_contra hlt
  push Not at hlt
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  haveI := uc22p22a_qs_nontrivial hsu.1
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun hle =>
    ((Subgroup.nontrivial_iff_ne_bot _).1 inferInstance)
      ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 hle)
  have hshape : Shape2214 (↥(mbarImage D.M c.V K) ⧸ center ↥(mbarImage D.M c.V K)) n :=
    Or.inr (Or.inr (Or.inr hsu.2))
  have hthin : ¬ F08.Thin8 (conjClosure D.M K) := by
    rw [uc22p2214_conjClosure_eq_of_normal hKM hN]
    exact uc22p2214_not_thin_single D.M c.V hKM (Or.inr ⟨hsu, hodd⟩)
  have hn1 : 1 ≤ n := uc22p2214_one_le_of_shape hshape
  obtain ⟨a, ha, r, hao, hpp, hmr⟩ := uc22p22i_exists_prim_prime_elt (by omega : 2 ≤ c.n) hm6 c.hpi
  have hr : r.Prime := hpp.1
  have hr5 : 5 ≤ r := by
    by_contra h5
    have h4 : r = 4 := by omega
    rw [h4] at hr
    exact absurd hr (by decide)
  have hprim : ¬ r ∣ 2 ^ n - 1 := hpp.2.2 n (by omega) hlt
  have hfix := uc22p2214_fix D c hKM (Or.inl hN)
  obtain ⟨Y, _, _, ⟨e⟩, S, hS, hrN⟩ := uc22p2214_borel_of_elt_faith D Ch hV h1930 c hKC hKV
    hshape hfix (fun _ hb hb1 => uc22p2214_faith_of_R869N D Ch h869N hV h1930 c hKC hKV hthin hfix
      hb hb1) ha hr hao (by omega) hr5
  rcases uc22p2214_borel_prime_U3 (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hsu.2) hS hr
    (by omega) hrN with h1 | h1
  · exact hprim h1
  · exact uc22p2214_false_of_sp D Ch h1930 c hr
      (h846 K hKC n (uc22p22a_shape_su3 D c hKC hsu) r hr (by omega) h1) ha hao

theorem uc22p2215_false_of_su3N (D : Data G) (Ch : Choice2011 G)
    (hK147 : K147) (h869N : F08.R869N D) (hV : S22_V D Ch) (h846 : F08.R846 D) (h8 : S22_8 D Ch)
    (hSg : UC6S846.SigmaStd D) (h229 : S22_9 D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch)
    (hn3 : 3 ≤ c.n) (h3 : 3 ∈ D.sig) {K : Subgroup G} (hKC : K ∈ calC D.M)
    (hN : (K.subgroupOf D.M).Normal) {n : ℕ} (hsu : IsSU3 ↥(mbarImage D.M c.V K) n)
    (hodd : Odd n) : False := by
  have hm6 : c.n ≠ 6 := by
    intro hc6
    apply uc22p2214_not_mem_piSet D Ch h8 hSg h1930 c h3
    rw [c.hpi, hc6]
    exact ⟨Nat.prime_three, by norm_num⟩
  have hle := uc22p2214_su3_oddN D Ch h869N hV h846 h1930 c hn3 hm6 hKC hN hsu hodd
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hel : CFSG.Open.IsElemAbelian 2 c.V := (hV h1930 c).1.1.1.2.2.2
  haveI := uc22p22a_qs_nontrivial hsu.1
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun hKV =>
    ((Subgroup.nontrivial_iff_ne_bot _).1 inferInstance)
      ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 hKV)
  have hlg := uc22p22d_lgConj_of_normal c.V hKM hN
  have hL2 : IsL2 ↥(mbarImage D.M c.V K) n := by
    refine uc22p22d_isL2_of_case147 hK147 D c hred hel hKC hKV (uc22p22a_two_le_of_isU3 hsu.2)
      (Or.inr (Or.inl ?_)) (h229 h1930 c) hle
    rw [hlg]
    exact hsu
  exact uc22p21k_not_isL2 hsu.1 (Or.inr ⟨n, hsu.2⟩) n hL2

theorem uc22p2213t_false_of_su3N (D : Data G) (Ch : Choice2011 G)
    (hK147 : K147) (h117 : R117W D) (h869N : F08.R869N D) (hV : S22_V D Ch) (h846 : F08.R846 D)
    (h8 : S22_8 D Ch) (hSg : UC6S846.SigmaStd D) (h229 : S22_9 D Ch) (h9 : S21_9Sig3 D Ch)
    (he : CFSG.Open.evenRank G = 3) (h1930 : H1930 D) (c : Ctx22b D Ch) (hn3 : 3 ≤ c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal) {n : ℕ}
    (hodd : Odd n) (hsu : IsSU3 (Bar2 L) n) : False := by
  have h2 := uc22p22a_two_le_of_isU3 hsu.2
  have h3 : 3 ∈ D.sig :=
    (h9 h1930 c.toCtx21 L hL hN n hsu (uc22p22a_not_isPowTwo_of_odd hodd (by omega)) he).2
  have hLV :=
    uc22p2213t_not_le_centralizer D Ch h117 hV h1930 c hL (not_thin8_of_isSU3 hsu hodd)
  have hO2 : CFSG.pCore 2 (MBar D.M c.V) = ⊥ :=
    (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 (hV h1930 c).1.2.2
  have hq := (uc22br4_isComponentOf_mbarImage D.M c.V L c.hVM hO2 hL hLV).2.2
  obtain ⟨⟨ε⟩, -⟩ := uc22p22a_data D c hL hq
  exact uc22p2215_false_of_su3N D Ch hK147 h869N hV h846 h8 hSg h229 h1930 c hn3 h3 hL hN
    ⟨hq, CFSG.Blueprint.LieModel.of_mulEquiv ε hsu.2⟩ hodd

end CFSG.LocalAnalysis.UniquenessCase.UC22
