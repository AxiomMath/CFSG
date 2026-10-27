module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213CovSylow
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicLocal17
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22S216Spor
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_inf_centralizerBar_eq_bot {P Q L : Subgroup G} (hQL : Q ≤ L)
    (hQ3 : IsPGroup 3 Q) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L))) :
    Q ⊓ PartOne.Section8.centralizerBar P L = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hQ3 (UC6S846.isPGroup_pCoreOf L)).eq_bot
  rw [eq_bot_iff]
  rintro z ⟨hzQ, hzC⟩
  have hcen : (QuotientGroup.mk (⟨z, hQL hzQ⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) :=
    CFSG.SectionRank.Ccomm.mk_mem_center_iff.mpr fun y =>
      (CFSG.mem_openPCoreOf_iff _).mp (hzC.2 y y.2)
  obtain ⟨k, hk⟩ := hQ3 ⟨z, hzQ⟩
  have hdvd3 : orderOf (QuotientGroup.mk (⟨z, hQL hzQ⟩ : ↥L) : Bar2 L) ∣ 3 ^ k := by
    refine (orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) _).trans ?_
    have h := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at h ⊢
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (center (Bar2 L))) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hZ).pow_left k
  have h1 : orderOf (QuotientGroup.mk (⟨z, hQL hzQ⟩ : ↥L) : Bar2 L) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd3 (Subgroup.orderOf_dvd_natCard _ hcen)
  have hzO : z ∈ CFSG.Open.pCoreOf 2 L :=
    (CFSG.mem_openPCoreOf_iff (⟨z, hQL hzQ⟩ : ↥L)).mpr
      ((QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1))
  have hmem : z ∈ Q ⊓ CFSG.Open.pCoreOf 2 L := ⟨hzQ, hzO⟩
  rwa [hQO2] at hmem

theorem uc22s213_center_bar2_eq_bot_of_isSpor_rest
    (hSC : PartTwo.Inputs1719.K_SporadicCoverCenterOdd) {M L : Subgroup G} (hL : L ∈ calC M)
    {s : TauCeti.SporadicName} (hs : s = .M12 ∨ s = .M24 ∨ s = .Ru ∨ s = .J4)
    (hX : IsSpor (BarInf L) s) : center (Bar2 L) = ⊥ := by
  obtain ⟨φ⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨f⟩ := hX
  have hs' : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .HS ∨
      s = .He ∨ s = .Ru ∨ s = .J4 := by
    rcases hs with rfl | rfl | rfl | rfl <;> simp
  rcases hSC (Bar2 L) s hL.2.2 (uc22p20p_odd_center_bar2 ↥L) ⟨φ.symm.trans f⟩ hs' with
    h | ⟨rfl, -⟩
  · exact h
  · rcases hs with h | h | h | h <;> cases h

theorem uc22s213_strong_of_center (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    (hinn : ∀ σ : MulAut (BarInf L), Odd (orderOf σ) →
      σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (h2 : CFSG.Open.pRank 3 L = 2) (hm3 : CFSG.Open.pRank 3 S.M ≤ 2)
    (hp : CFSG.Open.pRank S.p L ≤ 1) : IsStronglyPEmbedded 3 S.M := by
  by_contra hnot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hMN : S.M ≤ normalizer (L : Set G) := by
    by_contra hMN
    exact hZ (PartOne.Section8.three_dvd_center_bar2_of_calC_of_not_normal hS hU S hσ hnot hL
      h2 hMN)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 S.M
  have hPN : P ≤ normalizer (L : Set G) := hP.le.trans hMN
  have hQ : IsSylowOf 3 (P ⊓ L) L := hP.inf_of_le_normalizer hLM hMN
  have hQr : 2 ≤ CFSG.Open.pRank 3 (P ⊓ L) := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf Nat.prime_three hQ, h2]
  obtain ⟨E, hEQ, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hQr
  have hPQ : P ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_normalizer hPN).trans inf_normalizer_le_normalizer_inf
  have hdec : P ≤ P ⊓ L ⊔ PartOne.Section8.centralizerBar P L :=
    PartOne.Section8.le_sup_centralizerBar_of_inner inf_le_left inf_le_right rfl
      (normal_subgroupOf_of_le_normalizer hPQ) hQ hP.isPGroup hPN le_rfl fun y hy => by
        obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP.isPGroup ⟨y, hy⟩
        rw [Subgroup.orderOf_mk] at hk
        exact uc22s213_exists_inner_of_odd hL.2.2 hinn (hPN hy) (hk ▸ Odd.pow (by decide))
  have hQO2 : P ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hQ.isPGroup
      (UC6S846.isPGroup_pCoreOf L)).eq_bot
  have hcomm : ∀ q ∈ P ⊓ L, ∀ c ∈ PartOne.Section8.centralizerBar P L, q * c = c * q := by
    intro q hq c hc
    have h := commutator_mem_commutator hq hc
    rwa [PartOne.Section8.commutator_eq_bot_centralizerBar inf_le_right hQO2 hPQ, mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h
  have hmeet := uc22s213_inf_centralizerBar_eq_bot (P := P) inf_le_right hQ.isPGroup hZ
  have hC1 : PartOne.Section8.centralizerBar P L = ⊥ := by
    by_contra hne
    have hCP : PartOne.Section8.centralizerBar P L ≤ P := PartOne.Section8.centralizerBar_le P L
    have h3C : 3 ∣ Nat.card (PartOne.Section8.centralizerBar P L) :=
      (hP.isPGroup.to_le hCP).card_eq_or_dvd.resolve_left fun h => hne (card_eq_one.mp h)
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(PartOne.Section8.centralizerBar P L))
      3 h3C
    have hco : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe, hc]
    have hcQ : (c : G) ∉ P ⊓ L := fun h => by
      have hc1 : (c : G) ∈ P ⊓ L ⊓ PartOne.Section8.centralizerBar P L := ⟨h, c.2⟩
      rw [hmeet, mem_bot] at hc1
      rw [hc1, orderOf_one] at hco
      omega
    have hcE : (c : G) ∈ centralizer (E : Set G) := by
      rw [mem_centralizer_iff]
      exact fun e he => hcomm e (hEQ he) c c.2
    have h3 := CFSG.AGLEmbedding.three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer
      Nat.prime_three hEel hEc hco (fun h => hcQ (hEQ h)) hcE
      (hEQ.trans (inf_le_left.trans hP.le)) (hP.le (hCP c.2))
    omega
  have hPL : P ⊓ L = P :=
    le_antisymm inf_le_left (by simpa only [hC1, sup_bot_eq] using hdec)
  have h3β : 3 ∉ uniqueFourBeta G := fun h =>
    hnot (isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h)
  have hpp : S.p.Prime := S.hp.1.1
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  haveI : Fact S.p.Prime := ⟨hpp⟩
  have hsp := PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  have h76 : Conclusion76 S.M S.p := UC6.conclusion76_dataOfSetup4 hSE hS hU S h3β S.hp hsp
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (UC6.four_le_pRank_of_sigma S.hp)
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hLM
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hpp hp2
    (UC6.R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hL.2.2 hpp hp2 hp)
    hBM (hBM.trans hMN) hBel hBc Nat.prime_three (by norm_num) inf_le_right hQ.isPGroup
  have hΓ : CFSG.Open.rankThreeGamma 1 3 (P ⊓ L) ≤ S.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76
      (inf_le_right.trans hLM) hQ.isPGroup hQr hF
  rw [hPL] at hΓ hQr
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    have hE1 : E = ⊥ := le_bot_iff.mp (hEQ.trans inf_le_left)
    rw [hE1, card_bot] at hEc
    omega
  exact hnot (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le
    (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hP hP1
    ((CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore le_rfl
      (le_trans (by norm_num) hQr)).trans hΓ)
    fun y hy hyo => CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le hΓ hy hyo)

theorem uc22s213_not_centralizesBar_of_spor (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hSC : PartTwo.Inputs1719.K_SporadicCoverCenterOdd) {L : Subgroup G} (hL : L ∈ calC S.M)
    (hs : IsSpor (BarInf L) .M12 ∨ IsSpor (BarInf L) .M24 ∨ IsSpor (BarInf L) .Ru ∨
      IsSpor (BarInf L) .J4)
    (hm3 : CFSG.Open.pRank 3 S.M ≤ 2) (h3 : CFSG.Open.pRank 3 L ≤ 2)
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  haveI := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  obtain ⟨s, hs, hX⟩ : ∃ s : TauCeti.SporadicName, (s = .M12 ∨ s = .M24 ∨ s = .Ru ∨ s = .J4) ∧
      IsSpor (BarInf L) s := by
    rcases hs with h | h | h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr (Or.inl rfl), h⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), h⟩
  have hsJ : s ≠ .J1 := by rcases hs with rfl | rfl | rfl | rfl <;> decide
  have hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    rw [uc22s213_center_bar2_eq_bot_of_isSpor_rest hSC hL hs hX, card_bot]
    norm_num
  have h2 : 2 ≤ CFSG.Open.pRank 3 L :=
    uc22s213_pRank_three_barInf hL.2.2 hZ ▸ hrank (BarInf L) s hsJ hX
  have hp := uc22s213_pRank_le_one_of_centralizesBar (CFSG.Quasithin.A3.subnormal_le hL.1) hodd
    hpr haL S.hp.1.1 S.hp.1.2.1 hN
  have h1 := hk1 (uc22s213_strong_of_center hS hU S hσ hSE hOut hL hZ
    (fun σ hσ' => uc22s216_mem_range_conj_of_isSpor hout hL hX hσ') (by omega) hm3 hp)
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
