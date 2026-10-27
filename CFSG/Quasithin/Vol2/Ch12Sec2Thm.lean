module

public import CFSG.Quasithin.Vol2.Ch12Sec2Cases
public import CFSG.Quasithin.Vol2.Ch12Sec2Indec
public import CFSG.Quasithin.Vol2.Ch12Sec2NatA5
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueExt
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueHatA6
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueIrr
public import CFSG.Quasithin.Vol2.Ch12Sec2GlueL52
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch12Sec1Setup
public import CFSG.Quasithin.Background.B1MoreNineD
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3084
public import Certificates.Certificate3086
public import Certificates.Certificate3119
public import Certificates.Certificate3120
public import Certificates.Certificate3139
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3172
public import Certificates.Certificate7022
public import Certificates.Certificate8010
public import Certificates.Certificate8011
public import Certificates.Certificate8012
public import Certificates.Certificate8013
public import Certificates.Certificate8014
public import Certificates.Certificate8015
public import Certificates.Certificate8016
public import Certificates.Certificate8017
public import Certificates.Certificate8018
public import Certificates.Certificate8019
public import Certificates.Certificate8020
public import Certificates.Certificate8021
public import Certificates.Certificate8022
public import Certificates.Certificate8024
public import Certificates.Certificate8025
public import Certificates.Certificate8026
public import Certificates.Certificate8027
public import Certificates.Certificate8028
public import Certificates.Certificate8029
public import Certificates.Certificate8030
public import Certificates.Certificate8031
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate4103
public import Certificates.Certificate7067
public import Certificates.Certificate17000
public import Certificates.Certificate17022
public import Certificates.Certificate17026
public import Certificates.Certificate17001
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Walter.Defs
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

section Transport

variable {G : Type} [Group G] [Finite G]

theorem isFFModule_of_eq {W V L L' : Subgroup G} (hW : W = V) (hL : L' = L)
    [IsMulCommutative ↥W]
    (h : ∃ A : Subgroup (MulAut ↥W), IsFFStarOffender (V := ↥W)
      (Subgroup.normalizer (autOn L' W : Set (MulAut ↥W))) A) :
    ∃ _ : IsMulCommutative ↥V, IsFFModule (V := ↥V)
      (Subgroup.normalizer (autOn L V : Set (MulAut ↥V))) := by
  subst hW
  subst hL
  obtain ⟨A, hA⟩ := h
  exact ⟨inferInstance, isFFModule_of_offender hA⟩

omit [Finite G] in
theorem binaryOrthogonalFour_of_eq {W V L L' : Subgroup G} (hW : W = V) (hL : L' = L)
    [IsMulCommutative ↥W] {n : ℕ} (h : BinaryOrthogonalFour (V := ↥W) (autOn L' W) ⊤ ⊥ n) :
    ∃ _ : IsMulCommutative ↥V, BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ n := by
  subst hW
  subst hL
  exact ⟨inferInstance, h⟩

end Transport

theorem stmt12_2_2_of_inputs
    (h1001 : Stmt10_0_1) (h323 : Stmt3_2_3) (h325 : Stmt3_2_5)
    (h328 : Stmt3_2_8) (h6220 : Stmt6_2_20) (h701 : Stmt7_0_1) (h1101 : Stmt11_0_1)
    (h12111 : Stmt12_1_11) (hG2 : G2ZornQuotientModel) : Stmt12_2_2 := by
  intro G _ _ T hs hnab hQ hT
  by_cases hA : Alt12_2_2 G
  · exact Or.inl hA
  right
  intro L hmax hf hq
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h1001 G T L hs hnab hQ hT hmax hf hq
  have hL0 : conjClosure L T = L := conjClosure_eq_self_of_normalizes hTL
  obtain ⟨⟨hM, -⟩, -, hex⟩ := h323 G T L hs hnab hQ hT hmax hf hq
  rw [hL0] at hM hex
  refine ⟨hTL, ?_, fun V hV => ?_⟩
  · obtain ⟨I, hI⟩ := irrPlusBaseNonempty_of_a36 VolI.a36ForSQTK_holds G T L hs hnab hQ hT hmax hf
      hq hTL
    obtain ⟨V₀, hV₀, -, -⟩ := hex I hI
    exact ⟨V₀, hV₀⟩
  have hH : Hyp1223 G T L V := ⟨hs, hnab, hQ, hT, hA, hmax, hf, hq, hTL, hV⟩
  have hfsu : FSU G T L V := hH.fsu
  have hLV := le_normalizer_of_hyp1223 hH
  have hVLT := le_sup_of_hyp1223 hH
  have hVT : V ≤ T := (hV.1.trans (reducedAggregate_le_pCoreOf _)).trans
    (pCoreOf_le_of_le_normalizer hT (le_sup_right.trans Subgroup.le_normalizer))
  obtain ⟨-, -, hcases⟩ := h325 G T L V hfsu hL0.symm
  have key : V = conjClosure V T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧
      (∀ m ∈ Subgroup.normalizer (L : Set G),
        CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
      (Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) ∨
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥) := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, -, hTV, hC, hTI⟩ | ⟨hC, -, ⟨t, ht, htN⟩, hall⟩
    · have hTV : T ≤ Subgroup.normalizer (V : Set G) := by
        rw [h1]
        exact le_normalizer_conjClosure V T
      have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
        have := le_normalizer_conjClosure (conjClosure V T) (Subgroup.normalizer (L : Set G))
        rwa [← h2, ← h1] at this
      exact ⟨h1, hTV, fun m hm => Or.inl (conjugate_eq_self_of_mem_normalizer (hMV hm)),
        Or.inl hMV⟩
    · refine ⟨h1, hTV, fun m hm => ?_, Or.inr hC⟩
      by_cases hmV : m ∈ Subgroup.normalizer (V : Set G)
      · exact Or.inl (conjugate_eq_self_of_mem_normalizer hmV)
      · exact Or.inr (hTI m hm hmV)
    · exfalso
      obtain ⟨hVM, hVsum, hVinf, hniso⟩ := hall t ht htN
      have hVN : conjClosure V T ≤ Subgroup.normalizer (L : Set G) :=
        (conjClosure_le fun x hx v hv => (L ⊔ T).mul_mem ((L ⊔ T).mul_mem
          ((le_sup_right : T ≤ L ⊔ T) hx) (hVLT hv))
          ((L ⊔ T).inv_mem ((le_sup_right : T ≤ L ⊔ T) hx))).trans
          (sup_le Subgroup.le_normalizer hTL)
      rcases stmt12_1_setup_of h323 h325 h701 G T L V hfsu hL0.symm hC t ht htN hVM hVsum hVinf
          hniso with
        hJ4 | ⟨n, hn, ⟨e⟩, hred', ⟨eM⟩, hLVt, hnat1, hnat2⟩
      · exact hA (Or.inr (Or.inr (Or.inr (Or.inr hJ4))))
      · exact h12111 G T L hs hnab hQ hT hmax hf n hn ⟨e⟩ (conjClosure V T) V
          (CFSG.conjugate V t) hVN hred' ⟨eM⟩ hVinf hVsum.symm hLV hLVt hnat1 hnat2 hniso
  obtain ⟨hVeq, hTV, hTI, hMC⟩ := key
  have hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) := by
    have := (stmt3_2_2_eight_proved G T L V hfsu).2.1
    rwa [hL0, ← hVeq] at this
  refine ⟨⟨hVT, hTV, hred, hfsu⟩, hTI, hMC, ?_⟩
  obtain ⟨hab, -, -, h7⟩ := h701 G T L V hfsu
  rcases h7 with hFF | hJ4 | ⟨n, hn, hOrth⟩ | hFour
  ·
    obtain ⟨hab', hc⟩ := h328 G T L V hfsu hL0.symm hVeq (isFFModule_of_eq hVeq.symm hL0 hFF)
    refine ⟨hab', ?_⟩
    rcases hc with h1 | (h2a | h2b) | h3 | h4 | (⟨⟨e⟩, halt⟩ | ⟨⟨e⟩, halt⟩) | ⟨⟨e⟩, halt⟩ |
        ⟨⟨e⟩, hcard⟩ | ⟨hperf, hZ3, ⟨e⟩, hcard⟩ | ⟨n, hn, ⟨e⟩, hnat⟩ | ⟨⟨e⟩, hext⟩ |
        ⟨⟨e⟩, hcard⟩
    · exact (false_of_concl328_one h6220 naturalSL24NotA5Sum hH hred hM h1).elim
    · exact modules_of_concl328_two_a h1101 hH hred h2a
    · exact modules_of_concl328_two_b l32FourIndecomposable hH hred h2b
    · exact (false_of_concl328_three h1101 hH hred h3).elim
    · exact modules_of_concl328_four h1101 hG2 hH hred h4
    · exact modules_of_alternatingNatural_odd hH (Or.inl rfl) e halt
    · exact modules_of_alternatingNatural_odd hH (Or.inr rfl) e halt
    · exact modules_of_concl328_six hH e halt
    · exact modules_of_concl328_seven hH hTV e hcard
    · exact modules_of_concl328_eight hatA6SixIrreducible hH hred hperf hZ3 e hcard
    · exact modules_of_concl328_nine hH hred hTV hn e hnat
    · exact modules_of_concl328_ten extSqFourAltEight hH hred e hext
    · exact modules_of_concl328_eleven l52TenFixedPointFree hH hred hTV e hcard
  ·
    exact (hA (Or.inr (Or.inr (Or.inr (Or.inr hJ4.2.2.2.2.2))))).elim
  ·
    obtain ⟨hab', hO⟩ := binaryOrthogonalFour_of_eq hVeq.symm hL0 hOrth
    exact (false_of_concl701_orth h6220 hH hred hM hn hO).elim
  ·
    have h1 := hFour.1
    rw [show fsuL0 T L = L from hL0] at h1
    exact (lt_irrefl L h1).elim

end CFSG.Quasithin.H13
