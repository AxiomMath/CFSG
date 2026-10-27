module

public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofTools
import CFSG.RankThree.PartTwo.Sec18.Item183KT
import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofStatements
import CFSG.RankThree.PartTwo.Sec18.Item183KDiag

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item183NMProof

variable {G : Type} [Group G] [Finite G] {A M K E : Subgroup G} {c : G}

theorem normalizer_E_le (h45 : Sec4.Item4_5) (hD : Diag183 G A M c K E) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  obtain ⟨e⟩ := hD.quotient_iso
  have hSL := isSLThreePi_of_SL34 e
  exact Sec12.normalizer_le_of_sec12StdBar h45 hD.sec12StdBar
    (Sec12.card_center_eq_three_of_isSLThreePi hSL)
    (fun T hT hT9 hZT => KFacts.exists_normalizer_moves_of_isSLThreePi hSL T hT hT9 hZT)

theorem false_of_pPrimeCore_ne
    (h45 : Sec4.Item4_5)
    (h1811 : Item181_1) (h1812 : Item181_2) (hCb : Step183Cb) (hD : Diag183 G A M c K E)
    {N : Subgroup G} (hN : N ∈ scriptM (gamma 2 E : Set G))
    (hO : inSubgroup (CFSG.pPrimeCore 3) M ≠ inSubgroup (CFSG.pPrimeCore 3) (M ⊓ N)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Sec18Std G A M := hD.toSec18Std
  have hEN : Sec18Std G E N := ⟨hD.toPartTwoStanding, hD.partTwoS_eq, hD.E_mem_partTwoE, hN⟩
  have : IsSimpleGroup G := h.isSimpleGroup
  have hE : IsE27 E := isE27_of_mem_partTwoE hD.E_mem_partTwoE
  have hEM : E ≤ M := hD.E_le.trans (inf_le_right.trans
    ((normalizer_le_gamma le_rfl (by rw [hD.toHyp183.isE27.pRank_eq]; norm_num)).trans
      fun x hx => h.mem_scriptM.2 hx))
  have hMtop : M ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot h.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM.1)
  obtain ⟨L, -, S₀, -, hH⟩ := h1811 G E N hEN M hEM hMtop hO
  set H := L ⊔ E ⊔ S₀ with hHdef
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hEH : E ≤ H := le_of_mem_scriptH₀ hH₀
  set L₁ := inSubgroup perfectResidual H with hL₁
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  obtain ⟨s, hs, -, -⟩ := h1812 G E N hEN H hH
  have hcE : c ∈ E := hD.sec12StdBar.mem_A
  have hc3 : orderOf c = 3 := Item183K.orderOf_c hD.toHyp183
  have hcC : c ∈ sectionCentralizer E L₁ (CFSG.Open.pCoreOf 2 L₁) :=
    hCb G E N H s hEN hH hs _ (Subgroup.zpowers_le.mpr hcE) (by rw [Nat.card_zpowers, hc3])
      (inf_le_right.trans (normalizer_E_le h45 hD)) (Subgroup.mem_zpowers c)
  obtain ⟨d, hdEK, hdC⟩ :
      ∃ d ∈ E ⊓ K, d ∉ sectionCentralizer E L₁ (CFSG.Open.pCoreOf 2 L₁) := by
    by_contra hall
    push Not at hall
    have hEK9 : Nat.card (E ⊓ K : Subgroup G) = 9 :=
      Item183K.card_eq_nine_of_le hE inf_le_left
        (nine_le_card_of_not_subset_zpowers (fun x hx => hE.1.2 x hx.1) hD.inf_noncyclic)
        (fun heq => hD.toHyp183.false_of_isE27_le hE (inf_eq_left.mp heq))
    have hLO : CFSG.Open.pCoreOf 2 L₁ ≤ CFSG.Open.pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₁).trans (Subgroup.map_subtype_le _))
        ((le_normalizer_inSubgroup_perfectResidual H).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
    refine perfectResidual_not_le_of_mem_scriptH hEN hH
      (perfectResidual_le_of_commutator_le hEN hEH inf_le_left hEK9 fun l hl b hb => ?_)
    have h1 := hLO ((hall b hb).2 l hl)
    have e : (b * l * b⁻¹ * l⁻¹)⁻¹ = l * b * l⁻¹ * b⁻¹ := by group
    rw [← e]
    exact (CFSG.Open.pCoreOf 2 H).inv_mem h1
  have hcH : c ∈ H := hEH hcE
  have hdH : d ∈ H := hEH hdEK.1
  have hcL := (forall_mem_pCoreOf_iff hcH).mp hcC.2
  have hdL : π ⟨d, hdH⟩ ∉ Subgroup.centralizer
      (((perfectResidual H).map π : Subgroup _) : Set _) :=
    fun hd => hdC ⟨hdEK.1, (forall_mem_pCoreOf_iff hdH).mpr hd⟩
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set Y := inSubgroup perfectResidual (H ⊓ C) with hYdef
  have hYimg := Claim184LcProof.map_perfectResidual_inf_centralizer hcH
    (hD.toHyp183.pow_three hD.mem_A) hcL
  have hYHC : Y ≤ H ⊓ C := Subgroup.map_subtype_le _
  have hYH : Y ≤ H := hYHC.trans inf_le_left
  have hYC : Y ≤ C := hYHC.trans inf_le_right
  have hYp : ⁅Y, Y⁆ = Y := commutator_inSubgroup_perfectResidual _
  have hEC : E ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩))
  have hENY : E ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf hEH hEC).trans (le_normalizer_inSubgroup_perfectResidual _)
  have hq := isQuasisimple_map_perfectResidual hH₀.2.1
  obtain ⟨K', hK', hKK'⟩ := hD.mem_thetaComponentsAt
  replace hKK' : K'.map C.subtype = K := hKK'
  have hYK : Y ≤ K := by
    rw [← hKK']
    refine le_map_of_isSubnormal hK'.2.1 hYC (D := E ⊓ K) (by rw [hKK']; exact inf_le_right)
      (fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hENY hx.1) y).mp hy) ?_
    intro W hWY hWn hWd
    exact le_of_forall_commutator_mem hYH hYp hYimg hq hdH hdL hWY hWn
      (fun y hy => hWd y hy d hdEK)
  have hKN : K ≤ N := hD.le_of_mem_scriptM hN
  have hRN : CFSG.Open.pCoreOf 2 H ≤ N :=
    le_of_le_normalizer_of_isPGroup_two hEN (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (hEH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hLY : L₁ ≤ Y ⊔ CFSG.Open.pCoreOf 2 H := by
    rintro _ ⟨l, hl, rfl⟩
    have hlb : π l ∈ (Y.subgroupOf H).map π := by
      rw [hYimg]
      exact ⟨l, hl, rfl⟩
    obtain ⟨y, hy, hyl⟩ := hlb
    have h1 : π (y⁻¹ * l) = 1 := by rw [map_mul, map_inv, hyl, inv_mul_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
    have heq : (l : G) = (y : G) * ((y⁻¹ * l : H) : G) := by simp
    change (l : G) ∈ Y ⊔ CFSG.Open.pCoreOf 2 H
    rw [heq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hy) h1
  exact perfectResidual_not_le_of_mem_scriptH hEN hH (hLY.trans (sup_le (hYK.trans hKN) hRN))

end Item183NMProof

end CFSG.RankThree.PartTwo.Sec18
