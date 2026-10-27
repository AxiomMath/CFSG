module

public import CFSG.LocalAnalysis.UniquenessCase.UCKQSDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporM5
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporM7
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicBMData
public import CFSG.RankThree.Native.BFiveLocalRel
public import CFSG.RankThree.Native.LyFiveSpec
public import CFSG.RankThree.PartOne.KS.Co1ScalCheck
public import CFSG.RankThree.PartOne.Q1327S.HN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint

section HN

open CFSG.RankThree.PartOne.KS.HNFive CFSG.RankThree.PartOne.Q1327S

theorem pcaSpor_HN5 :
    PCASporAt .HN 5 := by
  intro K _ _ ⟨e⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨q, z, x, r, hR⟩ := exists_hn_rel
  haveI hfin : Finite (NativeSporadic.Carrier .HN) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.HN ≠ 0
      rw [CFSG.Sporadic.HN.card_HN]; norm_num)
  refine PCentralAbelianAt.of_mulEquiv e ?_
  have hcardQ : Nat.card (QG q) = 5 ^ 5 := hR.card_Q
  exact PCentralAbelianAt.of_exponent (U := QG q) (IsPGroup.of_card hcardQ)
    (fun u hu => hR.pow_five_of_mem hu) hcardQ.symm.le

end HN

section Ly

open CFSG.RankThree.Native

theorem qsLy_pca :
    PCentralAbelianAt CFSG.Sporadic.Ly.J 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ := lyFiveMRelJ.q
  have hcardQ : Nat.card (fiveQ lyFiveXJ lyFiveVJ) = 5 ^ 5 := hQ.card_fiveQ
  exact PCentralAbelianAt.of_exponent (U := fiveQ lyFiveXJ lyFiveVJ) (IsPGroup.of_card hcardQ)
    (fun u hu => hQ.pow_five_of_mem hu) hcardQ.symm.le

theorem pcaSpor_Ly5 :
    PCASporAt .Ly 5 := by
  intro K _ _ ⟨e⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have e' : K ≃* NativeSporadic.Ly := e
  have φ : K ≃* CFSG.Sporadic.Ly.J := e'.trans CFSG.Sporadic.Ly.lyEquivJ
  exact @PCentralAbelianAt.of_mulEquiv K CFSG.Sporadic.Ly.J _ _ (inferInstance) (inferInstance) 5 _ φ qsLy_pca

end Ly

section B

open CFSG.Monster.B.Pinned CFSG.RankThree.Native

theorem pcaSpor_B5 :
    PCASporAt .B 5 := by
  intro K _ _ ⟨e⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hfin : Finite (NativeSporadic.Carrier .B) := finite_B
  refine PCentralAbelianAt.of_mulEquiv e ?_
  have hR := bFiveRel
  have hcardQ : Nat.card (FiveLocal.Q qFive) = 5 ^ 5 := hR.card_Q
  exact PCentralAbelianAt.of_exponent (U := FiveLocal.Q qFive) (IsPGroup.of_card hcardQ)
    (fun u hu => hR.pow_five_of_mem hu) hcardQ.symm.le

end B

section Co1

open CFSG.RankThree.PartOne.KS.ScalFive CFSG.RankThree.PartOne.KS.Co1Scal CFSG.Monster.B.Pinned

theorem qsCo1_pca_of_scalRel {G : Type} [Group G] [Finite G] {q : Fin 2 → G} {z s t : G}
    {M Sm : Matrix (Fin 2) (Fin 2) (ZMod 5)} {cs ct : Fin 2 → ℕ} {r : ZMod 5}
    (hR : ScalRel q z s t M Sm 0 1 cs r ct) : PCentralAbelianAt G 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQP : IsPGroup 5 (QG q) := IsPGroup.of_card hR.card_Q
  refine PCentralAbelianAt.of_noncomm hQP (q_mem 1) (q_mem 0) (hR.pow_five_of_mem (q_mem 1)) ?_
  intro hc
  have hz1 : z ≠ 1 := by
    intro h
    have := hR.orderOf_z
    rw [h, orderOf_one] at this
    omega
  apply hz1
  rw [← hR.z_eq]
  unfold bcomm
  calc (q 0)⁻¹ * (q 1)⁻¹ * q 0 * q 1 = (q 0)⁻¹ * (q 1)⁻¹ * (q 0 * q 1) := by group
    _ = (q 0)⁻¹ * (q 1)⁻¹ * (q 1 * q 0) := by rw [← hc]
    _ = 1 := by group

theorem pcaSpor_Co1_5 : PCASporAt .Co1 5 := by
  intro K _ _ ⟨e⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hfin : Finite (NativeSporadic.Carrier .Co1) := (inferInstance : Finite NativeSporadic.Co1)
  exact PCentralAbelianAt.of_mulEquiv e (qsCo1_pca_of_scalRel co1Scal_rel)

end Co1

section M5Gmat

open _root_.Timmesfeld.PcFive _root_.Timmesfeld.PcReg
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.SporM5

theorem qsM5_exists_exponent [Finite Gmat] :
    ∃ U : Subgroup Gmat, IsPGroup 5 U ∧ (∀ u ∈ U, u ^ 5 = 1) ∧ 5 ^ 5 ≤ Nat.card U :=
  rSub_Gmat

end M5Gmat

section M5

theorem pcaSpor_M5 : PCASporAt .M 5 := by
  intro K _ _ ⟨e⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : IsSimpleGroup (NativeSporadic.Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  obtain ⟨e'⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := NativeSporadic.Carrier .M) (MulEquiv.refl _)
  haveI : Finite CFSG.Monster.Generated.Gmat := Finite.of_equiv K (e.trans e').toEquiv
  obtain ⟨U, hU, hexp, hcard⟩ := qsM5_exists_exponent
  exact PCentralAbelianAt.of_mulEquiv (e.trans e') (PCentralAbelianAt.of_exponent hU hexp hcard)

end M5

section M7

theorem pcaSpor_M7 : PCASporAt .M 7 := by
  intro K _ _ ⟨e⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsSimpleGroup (NativeSporadic.Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := NativeSporadic.Carrier .M) (MulEquiv.refl _)
  have φ : K ≃* CFSG.Monster.Generated.Gmat := e.trans ε
  haveI : Finite CFSG.Monster.Generated.Gmat := Finite.of_equiv K φ.toEquiv
  have hexp := CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.M7Spor.pcSub_pow_seven
  refine PCentralAbelianAt.of_mulEquiv φ (PCentralAbelianAt.of_exponent ?_ hexp
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.M7Spor.seven_pow_five_le_card)
  intro u
  exact ⟨1, Subtype.ext (by simpa using hexp u.1 u.2)⟩

end M7

section Spor

theorem pcaSpor_holds : PCASpor :=
  pcaSpor_of_pairs CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds
    pcaSpor_HN5 pcaSpor_Ly5 pcaSpor_Co1_5 pcaSpor_B5 pcaSpor_M5 pcaSpor_M7

end Spor

end CFSG.LocalAnalysis.UniquenessCase.UCK
