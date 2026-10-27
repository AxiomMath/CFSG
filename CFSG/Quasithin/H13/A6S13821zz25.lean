module

public import CFSG.Quasithin.H13.A6S13821zz22
public import CFSG.Quasithin.H13.A6S13821zz24
public import CFSG.Quasithin.H13.A6S13821za
public import CFSG.Quasithin.H13.A6S1372L76A
public import CFSG.Quasithin.H13.A6S13821zz21

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.RankThree.PartTwo.Sec4

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_simple_13820b
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45)
    {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n)
    (hL : IsPSL 3 2 2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsPSU 3 2 3 (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, hH, hK, hKn, hHK, -, -⟩ := hC
  obtain ⟨-, -, hF⟩ := S.hypF918_K0 h36c h37 h38 h139 h1334 h13 hS hH hK
  have e : (K ⊔ T) ⊔ S.L1 = H := by
    rw [hHK, sup_assoc, sup_comm T S.L1]
  rw [e] at hF
  have hSQ := S.sqtkGroup_of_mem_Hz hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) k).mp hk) (le_conjClosure K T)
  have hsimp : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hL with h | h
    · exact A5.isSimpleGroup_of_isPSL34 h
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 3 h).2
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirr := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFe := factElem hF hIU
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirr
  have hD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hMp : autIH (fsuV1 T V) I H (conjClosure K T) = autIH (fsuV1 T V) I H K := by
    rw [hK₀]
  have hqM := hA.qhat_M hD.sylow.1
  have hne : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  obtain ⟨eI⟩ := nonempty_mulEquiv_quotient_autI hF hIU hsimp hne
  have hD3 : D3Std (autIH (fsuV1 T V) I H H) (autIH (fsuV1 T V) I H (conjClosure K T))
      (autIH (fsuV1 T V) I H T) (autIH (fsuV1 T V) I H K)
      (subM (fsuV1 T V) (conjClosure I H) I) :=
    ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  rcases hL with h | h
  · exact A5.false_of_insp4_L34 hA21 hG2 h42 h45 hD310 hD3 hMp hqM (hA.qOf_VT hD.exp)
      (IsPSL.of_mulEquiv eI h)
  · exact A6S20.false_of_insp4_u38 hA21 h42 h45 hD310 hD3 hMp hqM (hA.qOf_VT hD.exp)
      (IsPSU.of_mulEquiv eI h)

theorem claim_13820b
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hA21 : AsA21SQTKSection) (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45)
    {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n) (hb : S.Case13820bHyp H K)
    (h24 : ¬ IsPSL 2 2 2 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) :
    S.L1 ≤ K ∧ ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H ∧
      ∃ (π : Bool) (f : ℕ) (F : Type) (_ : Field F), PiField π 2 f F ∧ ModThree π (2 ^ f) ∧
        ((π = true ∧ f = 2) ∨ (π = false ∧ f = 3)) ∧
        Nonempty (↥(S.KSt H K) ≃* slPi π 3 (2 ^ f) F) := by
  obtain ⟨hS, hH, hK, hKN, hHK, hn, hLie⟩ := hC
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hq := S.isQuasisimple_modO2 h36c h139 h1334 h13 hS hH hK
  obtain ⟨e₀⟩ := S.kst_equiv hS hH hK
  have hLU : IsPSL 3 2 2 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
      IsPSU 3 2 3 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) := by
    rcases hb.1 with h | h | h
    · exact absurd h h24
    · exact Or.inl h
    · exact Or.inr h
  let e₁ : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃*
      (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  have hc : Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
        20160 ∨
      Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
        5515776 := by
    rw [Nat.card_congr e₁.toEquiv]
    rcases hLU with h | h
    · exact Or.inl (A5.card_of_isPSL34 h)
    · exact Or.inr (A6S20.card_of_isPSU38 h)
  rcases S.center_modO2_cases h36 hH hK hKN hq with hZ | hZ
  ·
    exfalso
    let e₂ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
        ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    refine S.false_of_simple_13820b h36c h37 h38 h139 h1334 h13 hD310 hA21 hG2 h42 h45
      ⟨hS, hH, hK, hKN, hHK, hn, hLie⟩ ?_
    rcases hLU with h | h
    · exact Or.inl (IsPSL.of_mulEquiv (e₂.trans e₁).symm h)
    · exact Or.inr (IsPSU.of_mulEquiv (e₂.trans e₁).symm h)
  · obtain ⟨π, f, F, _, hF, hq3, hq2, hπf, ⟨φ⟩⟩ := S.exists_slPi_13820 h36 hS hH hK hKN hq hZ hc
    have hLieQ : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n := lieF2n_congr e₀.symm hLie
    have hL1K := S.L1_le_of_slPi h1334 hS hH hK hKN hn hLieQ hq hF hq3 hq2 φ
    exact ⟨hL1K, commutator_UH_eq_of_L1_le hKH hKN hL1K, π, f, F, inferInstance, hF, hq3, hπf,
      ⟨φ⟩⟩

end Setting4

end CFSG.Quasithin.H13.A6
