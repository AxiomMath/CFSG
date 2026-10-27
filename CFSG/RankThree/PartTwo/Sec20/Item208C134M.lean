module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res3ProofCaseOne
public import CFSG.RankThree.PartTwo.Sec3.Sims321
public import CFSG.Quasithin.MS93.C134CorrM
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N
open CFSG.RankThree.PartTwo.Sec20.Res2
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem false_of_c134Case4Min_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.C134Case4Min (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False := by
  obtain ⟨⟨n', F, _, _, α, hF, ⟨hαs, hαk⟩, hZdec, -, hU, hTop, -⟩, hcore⟩ := hi
  obtain ⟨hKU, -, β, -, hβk, hβ⟩ := hU
  obtain ⟨A₃, A₄, hA₃, hA₄, hVC⟩ := hTop
  have hKQ : kTwenty M c ≤ Subgroup.normalizer
      ((CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c) : Subgroup G) : Set G) := hVC.1
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  have hβinj := injective_of_ker_eq β hβk
  refine false_of_module_core hT hTN h207 hKN hLQ (toSL α) (toSL_surjective hαs)
    (toSL_eq_one_iff_mem hαk) (inf_le_left.trans c134Q_le) (le_normalizer_centerOf hKQ)
    comm_of_mem_centerOf (fun z hz k hk => commutator_mem_centerOf_c134Q_core hT hKQ hz hk)
    (fun g hg m hm hmP k hk => ?_) hcore
  have hZc := comm_of_mem_centerOf (Q := CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c))
  have hCZ := (le_sup_left (a := CFSG.Quasithin.c134CQ (kTwenty M c ⊔ T) (kTwenty M c))).trans_eq
    hZdec.symm
  have hUZ := (le_sup_right (b := ⁅CFSG.Quasithin.centerOf
    (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)), kTwenty M c⁆)).trans_eq hZdec.symm
  have hLE : CFSG.Quasithin.c134CQ (kTwenty M c ⊔ T) (kTwenty M c) ≤
      Subgroup.normalizer ((⁅CFSG.Quasithin.centerOf
        (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)), kTwenty M c⁆ :
          Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [show x * u * x⁻¹ = u by rw [hZc x (hCZ hx) u (hUZ hu)]; group]
      exact hu
    · intro hu
      have h := hZc x (hCZ hx) _ (hUZ hu)
      have h2 : x * (x * u * x⁻¹) = x * u := by rw [h]; group
      have h3 : x * u * x⁻¹ = u := mul_left_cancel h2
      rw [← h3]
      exact hu
  have hm' : m ∈ ((CFSG.Quasithin.c134CQ (kTwenty M c ⊔ T) (kTwenty M c) : Set G) *
      ((⁅CFSG.Quasithin.centerOf (CFSG.Quasithin.c134Q (kTwenty M c ⊔ T) (kTwenty M c)),
        kTwenty M c⁆ : Subgroup G) : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE, ← hZdec]
    exact hm
  obtain ⟨a, ha, u, hu, rfl⟩ := hm'
  have hapc : ∀ p ∈ kTwenty M c, p * a * p⁻¹ = a := fun p hp => by
    rw [Subgroup.mem_centralizer_iff.mp ha.2 p hp]
    group
  have huP : ∀ p ∈ T ⊓ kTwenty M c, p * u * p⁻¹ = u := by
    intro p hp
    have h1 := hmP p hp
    have h2 := hapc p hp.2
    calc p * u * p⁻¹ = (p * a * p⁻¹)⁻¹ * (p * (a * u) * p⁻¹) := by group
      _ = u := by rw [h1, h2]; group
  have hku := fix_of_natural (toSL α) β hβinj (equivariance_toSL hβ) hKU hg hu huP k hk
  calc (k : G) * (a * u) * (k : G)⁻¹ = ((k : G) * a * (k : G)⁻¹) * ((k : G) * u * (k : G)⁻¹) :=
        by group
    _ = a * u := by rw [hapc k k.2, hku]

theorem false_of_c134Case4Min {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20One G A M L N c T) (hTN : T ≤ N)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N)
    (hKN : ¬ kTwenty M c ≤ N)
    (hLQ : kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T)
    (hi : CFSG.Quasithin.C134Case4Min (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c)) :
    False :=
  false_of_c134Case4Min_core hT.toCtx20 hTN h207 hKN hLQ hi

section Certificates


theorem item208One_of_AS_corrM_ctx (hAS : CFSG.Quasithin.MS93.AS_C_1_34_corrM)
    (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053) (h207 : Item207One)
    (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) (h1812 : Sec18.Item181_2)
    (h184_1 : Sec18.Item184_1) (hC : Step208CasesCtx) : Item208One := by
  intro G _ _ A M L N c T hT hTN
  have h1 := h2051 G A M L N c T hT
  have h2 := rank3II_20_5_2_of h204 hT h1
  have h3 := h2053 G A M L N c T hT h2
  have hMS := step208MSPair_of_bridge CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge h189 h204
    h321 (step208X_of h1812 h184_1 (step208XActs_of h189 h321 h204 h2051 h2053))
  obtain ⟨hpair, hcomp, hmul, hα⟩ := hMS G A M L N c T hT hTN h2 h3
  obtain ⟨i, hi⟩ := hAS G (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) hpair hcomp hmul hα
  obtain ⟨-, hKN, hpar⟩ := item189_case_one h189 hT h3
  have hLQ := sup_pCoreOf_eq h321 h189 hT h2 h3
  have h207' := h207 G A M L N c T hT hTN
  have h204' := h204 G A M L N c T hT
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi.elim
  · exact hC G A M L N c T hT hTN h204' h207' h3 hKN hpar hLQ 1 hi
  · exact hC G A M L N c T hT hTN h204' h207' h3 hKN hpar hLQ 2 hi
  · exact hC G A M L N c T hT hTN h204' h207' h3 hKN hpar hLQ 3 hi
  · exact (false_of_c134Case4Min hT hTN h207' hKN hLQ hi).elim
  · exact hC G A M L N c T hT hTN h204' h207' h3 hKN hpar hLQ 5 hi
  · exact hi.elim

theorem item208One_of_AS_corrM_S322 (hAS : CFSG.Quasithin.MS93.AS_C_1_34_corrM)
    (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053) (h207 : Item207One)
    (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) (h1812 : Sec18.Item181_2)
    (h184_1 : Sec18.Item184_1) : Item208One :=
  item208One_of_AS_corrM_ctx hAS h204 h2051 h2053 h207 h189 h321 h1812 h184_1
    (step208CasesCtx_of_four (step208CasesCtxFour_of (Res3.step208CaseOneL32_proof h184_1)))

theorem item208One_of_sec18M (hAS : CFSG.Quasithin.MS93.AS_C_1_34_corrM)
    (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) (h189 : Sec18.Item189)
    (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053) (h207 : Item207One) :
    Item208One :=
  item208One_of_AS_corrM_S322 hAS h204 h2051 h2053 h207 h189 Sec3.Sims321.item321Split_holds
    h1812 h184

theorem item208One_core (hAS : CFSG.Quasithin.MS93.AS_C_1_34_corrM) (h321 : Sec3.Item321Split)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20 G A M L N c T)
    (hN : N = Subgroup.normalizer (L : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Assembly.RankThreeEven.projSL 3
      (GaloisField 2 2)))
    (hLp : ⁅L, L⁆ = L) (hLM : ¬ L ≤ M) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M)
    (h280 : (L ⊓ M).relIndex L = 280) (hKC : kTwenty M c ∈ oTwoComponentsIn M)
    (hKN : ¬ kTwenty M c ≤ N) (hK : KType20 M N c) (hTN : T ≤ N)
    (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h2 : ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G))
    (h3 : KIsL3 M c)
    (h207 : kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N) :
    IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n := by
  have hpar := hK.isMaxParabolic h3
  obtain ⟨x, -, hxM, -, hxS⟩ :=
    step208X_core hT hN hAL hO2L h280 hTN (step208S_core h321 hT hN hAL hKC hpar h2 h3 hTN)
  obtain ⟨hpair, hcomp, hmul, hα⟩ :=
    step208MSPair_core CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge kFactL3OddThreeRank h321
      hT hKC hKN h204 hTN h2 h3 ⟨x, hxM, hxS⟩
  obtain ⟨i, hi⟩ := hAS G (kTwenty M c ⊔ T) (sTwenty M N c T) (kTwenty M c) hpair hcomp hmul hα
  have hLQ := sup_pCoreOf_eq_core h321 hT hKC h2 h3
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi.elim
  · exact conclusion_of_isC134Case_one_core
      (fun e hi1 => (Res3.false_of_caseOne_L32_core hT hN hAL hLq hLp hLM hO2L hTN h204 h207 e
        hKN hi1).elim) hT hTN h204 h207 h3 hKN hpar hLQ hi
  · exact (false_of_isC134Case_two_core hT hTN h207 hKN hLQ hi).elim
  · exact (false_of_isC134Case_three_core hT hTN h207 hKN hLQ hi).elim
  · exact (false_of_c134Case4Min_core hT hTN h207 hKN hLQ hi).elim
  · exact (not_isC134Case_five_core hT hTN h207 hKN hi).elim
  · exact hi.elim

section CertificatesWeak


theorem item208One_of_sec18W
    (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    (h189 : Sec18.Item189) (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053)
    (h207 : Item207One) : Item208One :=
  item208One_of_sec18M CFSG.Quasithin.MS93.c134Weak_holds.toM h1812 h184 h189 h204 h2051 h2053
    h207

end CertificatesWeak

end Certificates

end CFSG.RankThree.PartTwo.Sec20

