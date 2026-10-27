module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217VMain
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S217L2Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217L2Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem uc22s217v_sp_three (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (hSg : UC6S846.SigmaStd D) (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h8107 : F08.R8107 D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal)
    (hJ1 : IsJ1 (Bar2 L)) : IsStronglyPEmbedded 3 D.M := by
  by_contra hnsp
  have h3 := uc22s217v_ncard_le_three D hSg hL hJ1 Nat.prime_three (by norm_num) (by norm_num)
    hnsp
  obtain ⟨K, hK, hKL⟩ := uc22s217v_exists_ne hL hnN
  have h2 : 1 < (conjSetOf D.M L).ncard := (Set.one_lt_ncard_iff (Set.toFinite _)).2
    ⟨K, L, hK, ⟨1, D.M.one_mem, by ext x; simp⟩, hKL⟩
  rcases (by omega : (conjSetOf D.M L).ncard = 2 ∨ (conjSetOf D.M L).ncard = 3) with hc | hc
  · exact uc22s217v_false_of_ncard_two D hSg h4 h614 h76 hL hc hJ1 Nat.prime_three
      (by norm_num) (by norm_num) hnsp
  · exact uc22s217v_false_of_ncard_three D Ch h211 h8107 hH c hL hc hJ1

theorem uc22s217v_false_of_not_dvdK3 (D : Data G) (Ch : Choice2011 G) (h5 : S21_5 D Ch)
    (hK3 : StronglyEmbeddedThree) (hSE : IsStronglyPEmbedded 3 D.M) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal)
    (hJ1 : IsJ1 (Bar2 L)) {b : G} (hb : b ∈ c.B0) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbr : orderOf b = r) (hrJ : ¬ r ∣ 175560) : False := by
  classical
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hbM : b ∈ D.M := c.hBM hb
  have hbr1 : b ^ r = 1 := by rw [← hbr]; exact pow_orderOf_eq_one b
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have h3 : 2 ≤ CFSG.Open.pRank 3 (conjClosure D.M L) := by
    obtain ⟨K, hK, hKL⟩ := uc22s217v_exists_ne hL hnN
    have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
    have hKX := uc22s217u3a_le_conjClosure hK
    have hLX : L ≤ conjClosure D.M L :=
      uc22s217u3a_le_conjClosure ⟨1, D.M.one_mem, by ext x; simp⟩
    obtain ⟨g, -, rfl⟩ := hK
    have hconj : L.map (MulAut.conj g).toMonoidHom = uniqueFourConj g⁻¹ L := by
      simp [uniqueFourConj]
    haveI := (kJ1_holds _ hJ1).2.1
    refine P2214R.two_le_pRank_of_conj hL hKC hKL ⟨g⁻¹, hconj⟩ hLX hKX hXM Nat.prime_three
      (by norm_num) ?_
    rw [uc22p21k_center_eq_bot hL.2.2, Subgroup.index_bot, (kJ1_holds _ hJ1).1]
    norm_num
  have hcb : ∀ K ∈ conjSetOf D.M L, CentralizesBar b K := fun K hK =>
    uc22s217v_centralizesBar_of_isJ1 (uc22s217v_isJ1_of_mem hJ1 hK) hr hrJ
      (h5 hH c₀ K (uc22p2214_calC_of_mem_conjSetOf hL hK) hb) hbr1
  have hbX : CentralizesBar b (conjClosure D.M L) := by
    refine uc22p2214_centralizesBar_conjClosure (hMX hbM) fun K hK k hk => ?_
    have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
    have h1 : b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 D.M :=
      uc22p22r_pCoreOf_le_of_isSubnormal hKC.1 ((hcb K hK).2 k hk)
    have hkX : k ∈ conjClosure D.M L := uc22s217u3a_le_conjClosure hK hk
    have h2 : b * k * b⁻¹ * k⁻¹ ∈ conjClosure D.M L :=
      (conjClosure D.M L).mul_mem ((mem_normalizer_iff.1 (hMX hbM) k).1 hkX)
        ((conjClosure D.M L).inv_mem hkX)
    exact uc22p2214_pCoreOf_inf_le hXM ⟨h1, h2⟩
  have hbc : Nat.card (zpowers b) = r := by rw [Nat.card_zpowers, hbr]
  have hXQ := uc22p21d_sup_pCore_eq hr hr2 hbc fun g hg =>
    uc22p21d_centralizesBar_of_mem_zpowers hbX hg
  have hAB : zpowers b ≤ c.B0 := Subgroup.zpowers_le.2 hb
  exact s21_2 D Ch hH c₀ (zpowers b) hAB
    (uc22s217l2t_normalizer_le_of_strongThree D.standing.simple D.standing.kProper hK3 hSE hXM
      (UC6.R869S.perfect_of_isProdOfCalC hprod) h3 hr (hAB.trans c.hBM) hbc hXQ)

theorem s21_17RV_of_fourK3 (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (h5 : S21_5 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hSg : UC6S846.SigmaStd D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h8107 : F08.R8107 D) (hK3 : StronglyEmbeddedThree) : S21_17RV D Ch := by
  intro hH c L hL hnN hJ1
  exfalso
  obtain ⟨b, hb, r, hr, hr2, -, hbr⟩ := Ctx21.exists_mem_B0_orderOf_ne_three c (hn3 hH c)
  by_cases hrJ : r ∣ 175560
  · have hnsp := uc22s217v_not_sp D Ch hH c hb hr hbr
    have h3 := uc22s217v_ncard_le_three D hSg hL hJ1 hr hr2 hrJ hnsp
    obtain ⟨K, hK, hKL⟩ := uc22s217v_exists_ne hL hnN
    have h2 : 1 < (conjSetOf D.M L).ncard := (Set.one_lt_ncard_iff (Set.toFinite _)).2
      ⟨K, L, hK, ⟨1, D.M.one_mem, by ext x; simp⟩, hKL⟩
    rcases (by omega : (conjSetOf D.M L).ncard = 2 ∨ (conjSetOf D.M L).ncard = 3) with hc | hc
    · exact uc22s217v_false_of_ncard_two D hSg h4 h614 h76 hL hc hJ1 hr hr2 hrJ hnsp
    · exact uc22s217v_false_of_ncard_three D Ch h211 h8107 hH c hL hc hJ1
  · exact uc22s217v_false_of_not_dvdK3 D Ch h5 hK3
      (uc22s217v_sp_three D Ch h211 hSg h4 h614 h76 h8107 hH c hL hnN hJ1) hH c hL hnN hJ1 hb
      hr hr2 hbr hrJ

end CFSG.LocalAnalysis.UniquenessCase.UC22
