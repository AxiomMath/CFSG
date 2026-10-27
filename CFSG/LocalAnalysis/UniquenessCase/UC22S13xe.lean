module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xa
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xb
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xd
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xe_odd_card_B {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) :
    Odd (Nat.card c.B) := by
  by_contra h
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B) 2 h
  have h1 := uc22p21d_odd_orderOf_of_mem_calB1 c.hB x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact (by decide : ¬ Odd 2) h1

theorem uc22s13xe_case136b (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D)
    (hTU : ∀ L ∈ calC D.M, F13.Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n)
    (hN : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal) (hsig : D.sig = D.sig1)
    (h1930 : H1930 D) (c : Ctx21 D Ch) (hB : c.B ≠ ⊥) (hH : Hyp2120 D c) {p : ℕ}
    (hp : p ∈ D.sig) : F13.Case136b D p c.B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hperm, _⟩ := c.hB
  exact ⟨hB, c.hle.trans c.hBM, uc22s13xe_odd_card_B c, hperm, s21_2 D Ch h1930 c c.B le_rfl,
    uc22s13xd_sylow hThin hCyc hSig hTU hN hsig c hH p hp⟩

theorem uc22s13xe_hyp131_of_isPowTwo
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h847 : R847Four D)
    (h211 : S21_1 D Ch) (h216 : S21_16 D Ch) (h218 : S21_18 D Ch)
    (hpow : ∀ L ∈ calC D.M, ∀ n, IsSU3 (Bar2 L) n → IsPowTwo n) (h19 : S21_19 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) (hH : Hyp2120 D c) (hsig : D.sig = D.sig1) :
    F13.Hyp131 D where
  thinOrU3 := uc22s13xc_thinOrU3_of_isPowTwo h1930 c hH h216 hpow
  normal := uc22s13xc_normal hH
  layer := uc22s13xc_layer h1930 c hH h218
  uniq := uc22s13a_hyp131_uniq h847 h211 h1930 c hSig.nonempty (uc22s13xc_normal hH)
  smallS := uc22s13xd_smallS hThin hCyc hSig (uc22s13xc_thinOrU3_of_isPowTwo h1930 c hH h216 hpow)
    (uc22s13xc_normal hH) hsig h61 c hH
  notAmong := uc22s13xc_notAmong_of_isPowTwo h1930 c hH h216 hpow h19

theorem uc22s13xe_hyp131
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h847 : R847Four D)
    (h211 : S21_1 D Ch) (h216 : S21_16 D Ch) (h218 : S21_18 D Ch) (h219 : S21_9N D Ch)
    (h19 : S21_19 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) (hH : Hyp2120 D c)
    (he : CFSG.Open.evenRank G ≠ 3) (hsig : D.sig = D.sig1) : F13.Hyp131 D :=
  uc22s13xe_hyp131_of_isPowTwo hThin hCyc hSig h61 h847 h211 h216 h218
    (uc22p2121e_isPowTwo_of_s21_9N h1930 c hH h219 he) h19 h1930 c hH hsig

theorem uc22s13xe_not_solvable_of_two_le {D : Data G} {Ch : Choice2011 G} (h61 : UC6.R6_1 D)
    (c : Ctx21 D Ch) (hH : Hyp2120 D c) {p : ℕ} (hp : p ∈ D.sig)
    (h2 : 2 ≤ CFSG.Open.pRank p D.M) : ¬ Group.IsSolvable ↥D.M := by
  intro hsol
  have hnc : ∀ C : Subgroup (Bar2 D.M), ¬ CFSG.IsComponent C := fun C hC => by
    obtain ⟨L, hL, -⟩ := uc22p21c_exists_calC_of_component D.M hC
    exact UC6S846.not_solvable_of_mem_calC hL hsol
  have h1 := uc22p2121b_pRank_le_one_add_sum h61 c hH hp ∅
    (fun C => iff_of_false (by simp) (hnc C))
  rw [Finset.sum_empty] at h1
  omega

theorem uc22s13xe_sig_eq_sig1 {D : Data G} {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (c : Ctx21 D Ch) (hH : Hyp2120 D c) : D.sig = D.sig1 := by
  obtain ⟨p, hp⟩ := hSig.nonempty
  have hns := uc22s13xe_not_solvable_of_two_le h61 c hH hp
    ((by norm_num : 2 ≤ 3).trans (hSig.three_le p hp))
  refine Set.Subset.antisymm (UC6S846.sig_subset_sig1 hSig hns) fun q hq => ?_
  rw [D.sig_sub, Set.mem_union, Set.mem_union]
  exact Or.inl (Or.inl hq)

theorem uc22s13xe_s21_21EB
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    {Ch : Choice2011 G} (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h136 : R136bFour D) (h847 : R847Four D)
    (h211 : S21_1 D Ch) (h216 : S21_16 D Ch) (h218 : S21_18 D Ch) (h219 : S21_9N D Ch)
    (h19 : S21_19 D Ch) : S21_21EB D Ch := by
  intro h1930 c hB hH
  by_contra he
  obtain ⟨p, hp⟩ := hSig.nonempty
  have hsig := uc22s13xe_sig_eq_sig1 hSig h61 c hH
  have hH131 :=
    uc22s13xe_hyp131 hThin hCyc hSig h61 h847 h211 h216 h218 h219 h19 h1930 c hH he hsig
  have h3 := h136 hsig hH131 p hp c.B
    (uc22s13xe_case136b hThin hCyc hSig hH131.thinOrU3 hH131.normal hsig h1930 c hB hH hp)
  have h4p := h4 p hp
  omega

theorem uc22s13xe_s21_21EB_setup4
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) {Ch : Choice2011 G}
    (h136 : R136bFour (UC6.dataOfSetup4 hS hU S)) (h847 : F08.R847 (UC6.dataOfSetup4 hS hU S))
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) (h216 : S21_16 (UC6.dataOfSetup4 hS hU S) Ch)
    (h218 : S21_18 (UC6.dataOfSetup4 hS hU S) Ch) (h219 : S21_9N (UC6.dataOfSetup4 hS hU S) Ch)
    (h19 : S21_19 (UC6.dataOfSetup4 hS hU S) Ch) : S21_21EB (UC6.dataOfSetup4 hS hU S) Ch :=
  uc22s13xe_s21_21EB hThin hCyc (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (UC6.r6_1_dataOfSetup4 hS hU S) (fun _ hp => UC6.four_le_pRank_of_sigma hp) h136
    (r847Four_of_r847 _ h847 (by have := hS.rank; omega)) h211 h216 h218 h219 h19

end CFSG.LocalAnalysis.UniquenessCase.UC22
