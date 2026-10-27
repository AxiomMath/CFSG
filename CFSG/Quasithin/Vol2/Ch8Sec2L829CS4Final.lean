module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4L3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4Sz
public import CFSG.Quasithin.Vol2.Ch8Sec2L822A
public import CFSG.Quasithin.Vol2.Ch8Sec2L829Coc

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G]

theorem step2_reduced_829 (hE22 : E2.E22StatementC) (hS825 : Stmt8_2_5)
    (hLU : HLU82) (hcard : Mathieu.StmtH13Card) (h827 : Step827) (h828 : Stmt8_2_8)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I)
    (hcoc : Row711M24Cocode T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H) (hC : Concl822 T L I H h k) :
    ∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧
      E22Surv2a H T (H ⊓ fsuM T L) K ∧
      ∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥(E2.star (H ⊓ fsuM T L) H K) ∨
        (IsPSU 3 2 n ↥(E2.star (H ⊓ fsuM T L) H K) ∧ Even n)) := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  obtain ⟨hmin, hsq, -, -⟩ := setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH
  have hC5 : Concl825 T L I h k := hS825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hT : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hVH : fsuV T I ≤ H := (fsuV_le_T hyp.fsu hV hN).trans hT.1
  have hrank : CFSG.Open.pRank 3 H ≤ 1 :=
    (pRank_three_le_one_cocode_829 hLU hcard h827 h37 h38 h39 (stmtFSUModule_of_eight h3228)
      h711n hyp h731 h821 hrow hcoc hH hh hC hC5 (h828 G T L I hyp h731 h821 hc hrow H h k hH hh hC)).2
  have hk : k = 2 := k_eq_two_cocode_829 hC5 hcoc
  have hns : ¬ Group.IsSolvable ↥H := not_isSolvable_H_cocode_829 hVH hh hC hk
  have hIH : ch82I (fsuV T I) h ≤ H := ch82I_le_829 hVH hh
  have hI := (concl822_cocode_829 hC hk).1
  have h60 := sixty_dvd_starQuot_H_cocode_829 (M := fsuM T L) hIH hI
  have h3 : 3 ∣ Nat.card (E2.StarQuot (H ⊓ fsuM T L) H) := (by norm_num : (3 : ℕ) ∣ 60).trans h60
  have h5 : 5 ∣ Nat.card (E2.StarQuot (H ⊓ fsuM T L) H) := (by norm_num : (5 : ℕ) ∣ 60).trans h60
  have hTp : IsPGroup 2 ↥T := hmin.isSylow.2.1
  obtain ⟨K, hKc, hHK, hq, hcase⟩ := step2_entry_cocode_829 hE22 hVH hh hmin hsq hC5 hcoc hC
  have hKH : K ≤ H := le_of_mem_cComp hKc
  rcases hcase with h1a | h2a | h2b
  ·
    obtain ⟨hJ, ⟨t, ht, hne, -⟩, n, hn2, hty, -⟩ := h1a
    have htH : t ∈ H := hmin.isSylow.1 ht
    rcases hty with hL | hSz
    · exact (not_surv1a_L2_of_pRank hKc htH hJ hne (by omega) hL hrank).elim
    · exact (not_surv1a_sz hmin hns hKc hJ h3 hSz).elim
  ·
    obtain ⟨n, hn2, hX⟩ := surv2a_cocode_829 hHK hTp h3 h5 h2a
    exact ⟨K, hKc, hHK, hq, h2a, n, hn2, hX⟩
  ·
    have hJ2 := h2b.2.1
    obtain ⟨n, hn1, hX⟩ := surv2b_cocode_829 hHK hTp h5 h2b
    exact (not_surv2b_of_pRank hKH hJ2 ⟨n, hn1, hX⟩ hrank).elim

end CFSG.Quasithin.H13
