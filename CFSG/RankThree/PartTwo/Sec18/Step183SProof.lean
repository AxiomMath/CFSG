module

public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofStatements
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofTools
import CFSG.RankThree.PartTwo.Sec18.Item181b
public import CFSG.RankThree.PartTwo.Sec18.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step183SNoSharedCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M N : Subgroup G), Sec18Std G A M →
    IsMaximalTwoLocal N → A ≤ N → N ≠ M →
    inSubgroup (CFSG.pPrimeCore 3) M ≠ inSubgroup (CFSG.pPrimeCore 3) (M ⊓ N)

namespace Step183SProof

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_inf_eq_of_pPrimeCore_eq {M N : Subgroup G}
    (hO : inSubgroup (CFSG.pPrimeCore 3) M = inSubgroup (CFSG.pPrimeCore 3) (M ⊓ N)) :
    CFSG.Open.pCoreOf 2 (M ⊓ N) = CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (pCoreOf_inf_le_of_pPrimeCore_eq hO) ?_
  set R := CFSG.Open.pCoreOf 2 M with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hRY : R ≤ inSubgroup (CFSG.pPrimeCore 3) M :=
    le_inSubgroup_pPrimeCore_of hcop (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hYMN : inSubgroup (CFSG.pPrimeCore 3) M ≤ M ⊓ N := by
    rw [hO]
    exact Subgroup.map_subtype_le _
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRY.trans hYMN)
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hR2

theorem false_of_step183S (h1811 : Item181_1) (h1813 : Item181_3) (hS : Step183S)
    {A M N : Subgroup G} (h : Sec18Std G A M) (hN : IsMaximalTwoLocal N) (hAN : A ≤ N)
    (hNM : N ≠ M)
    (hOM : inSubgroup (CFSG.pPrimeCore 3) M = inSubgroup (CFSG.pPrimeCore 3) (M ⊓ N)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.isSimpleGroup
  have hMN : CFSG.Open.pCoreOf 2 (M ⊓ N) = CFSG.Open.pCoreOf 2 M :=
    pCoreOf_inf_eq_of_pPrimeCore_eq hOM
  have hNM' : N ⊓ M = M ⊓ N := inf_comm N M
  have hle := pCoreOf_le_pCoreOf_inf h hAN
  have hne : CFSG.Open.pCoreOf 2 (N ⊓ M) ≠ CFSG.Open.pCoreOf 2 N := by
    intro heq
    apply hNM
    have hO : CFSG.Open.pCoreOf 2 N = CFSG.Open.pCoreOf 2 M := by
      rw [← heq, hNM', hMN]
    rw [← normalizer_pCoreOf_of_isMaximalTwoLocal hN, hO,
      normalizer_pCoreOf_of_isMaximalTwoLocal h.mem_scriptM.1]
  have hO : inSubgroup (CFSG.pPrimeCore 3) N ≠ inSubgroup (CFSG.pPrimeCore 3) (N ⊓ M) :=
    fun heq => hne (le_antisymm (pCoreOf_inf_le_of_pPrimeCore_eq heq) hle)
  have hNtop : N ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot h.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hN)
  obtain ⟨L, hL, S₀, hS₀, hH⟩ := h1811 G A M h N hAN hNtop hO
  set H := L ⊔ A ⊔ S₀ with hHdef
  have hHN : H ≤ N := sup_le (sup_le (le_of_mem_oTwoComponentsIn hL) hAN)
    (hS₀.le.trans ((Subgroup.map_subtype_le _).trans inf_le_left))
  set T := CFSG.Open.pCoreOf 2 (M ⊓ N) with hTdef
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hNMT : N ⊓ M ≤ Subgroup.normalizer (T : Set G) := by
    rw [hNM']
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hTNM : T ≤ N ⊓ M := by
    rw [hNM']
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hTY : T ≤ inSubgroup (CFSG.pPrimeCore 3) (N ⊓ M) :=
    le_inSubgroup_pPrimeCore_of hcop hTNM hNMT
  have hTS : T ≤ S₀ :=
    le_of_isSylowOf_of_normal hT2 hTY (Subgroup.map_subtype_le _) hNMT hS₀
  have hTH : T ≤ H := hTS.trans le_sup_right
  have hTM : T ≤ M := hTNM.trans inf_le_right
  have hTO : T ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hTH hTM)
      ((inf_le_inf_right M hHN).trans hNMT) hT2
  have hSeq : CFSG.Open.pCoreOf 2 (H ⊓ M) = CFSG.Open.pCoreOf 2 M :=
    le_antisymm ((hS G A M N L S₀ h hN hAN hNM hOM hMN hL hS₀ hH).trans hMN.le) (hMN ▸ hTO)
  have hON : CFSG.Open.pCoreOf 2 N ≤ H := hle.trans (by rw [hNM']; exact hTH)
  obtain ⟨P, hP1, hP2, hNP⟩ := hN.1
  have hF : CFSG.generalizedFitting H = CFSG.pCore 2 H :=
    Item183NMProof.generalizedFitting_eq_of_pCoreOf_le h.charTwoType ⟨P, hP1, hP2, hNP⟩ hHN
      hON
  obtain ⟨⟨C, hCchar, hC1, hHC⟩, -⟩ := h1813 G A M h H hH hF
  set C' := C.map (CFSG.Open.pCoreOf 2 (H ⊓ M)).subtype with hC'
  have hMC : M ≤ Subgroup.normalizer (C' : Set G) := by
    have : C.Characteristic := hCchar
    have hMO : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) := by
      rw [hSeq]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
    exact hMO.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic C)
  have hC'1 : C' ≠ ⊥ := fun hb =>
    hC1 ((Subgroup.map_eq_bot_iff_of_injective C (Subgroup.subtype_injective _)).mp hb)
  have hC'2 : IsPGroup 2 C' :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)).to_le (Subgroup.map_subtype_le C)
  have hloc : IsPLocal 2 (Subgroup.normalizer (C' : Set G)) := ⟨C', hC'1, hC'2, rfl⟩
  have hMeq : Subgroup.normalizer (C' : Set G) = M := by
    by_contra hne'
    exact h.mem_scriptM.1.2 _ (lt_of_le_of_ne hMC (Ne.symm hne')) hloc
  exact perfectResidual_not_le_of_mem_scriptH h hH
    ((Subgroup.map_subtype_le _).trans (hHC.trans hMeq.le))

end Step183SProof

open Step183SProof

theorem noSharedCore_of_step183S (h1811 : Item181_1) (h1813 : Item181_3) (hS : Step183S) :
    Step183SNoSharedCore := by
  intro G _ _ A M N hst hN hAN hNM hO
  exact false_of_step183S h1811 h1813 hS hst hN hAN hNM hO

end CFSG.RankThree.PartTwo.Sec18
