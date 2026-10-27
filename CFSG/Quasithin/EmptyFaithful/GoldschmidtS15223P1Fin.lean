module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Z2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223KcLocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem false_of_quasithinV2_ne_bot {T Mc L : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hloc : quasithinIsLocal T L) (hV2 : quasithinV2 L ≠ ⊥) : False := by
  obtain ⟨S₂, hS₂⟩ := hq.exists_sylow
  have hH : InH T (L ⊔ T) := ⟨le_sup_right, hloc.2.2.2⟩
  have hchar : CharTwo (L ⊔ T) := by
    subst hS₂
    exact charTwo_of_inH hq.qtke.2.1 S₂ hH
  have hcomp : L ∈ cComp (L ⊔ T) := hloc.2.1
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hsub : IsSubnormal L (L ⊔ T) := subnormal_of_mem_cComp hcomp
  refine hq.faithful_empty L ⟨hloc, ?_, ?_, hV2⟩
  · exact (eq_oTwoUpper_iff_forall_normal L).mp (eq_oTwoUpper_of_perfect hperf)
  · exact (quasithinGenFitting_eq_pCoreOf_iff L 2).mpr (A4.charTwo_of_subnormal hsub hchar)

theorem false_of_z2Of_commutator_ne_bot {T Mc Kc : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hKcMc : Kc ≤ Mc) (hKn : Mc ≤ Subgroup.normalizer (Kc : Set G)) (hTMc : T ≤ Mc)
    (hchar : CharTwo Kc)
    (hcases : Case15212ii T Mc Kc ∨ Case15212iii T Mc Kc ∨ Case15212He T Mc Kc)
    (hne : ⁅z2Of Kc, Kc⁆ ≠ ⊥) : False := by
  rcases hcases with ⟨hmax, -⟩ | ⟨L, t, hmax, hL, htT, -, hKc, hcomm, -⟩ | ⟨hmax, -⟩
  · exact false_of_quasithinV2_ne_bot hq hmax.1 hne
  · have htMc : t ∈ Mc := hTMc htT
    have hLK : L ≤ Kc := le_sup_left.trans hKc.ge
    have hconjZ : conjSub t (z2Of Kc) = z2Of Kc :=
      conjSub_eq_self152 (normalizer_le_normalizer_z2Of Kc (hKn htMc))
    have hL0 : ⁅z2Of Kc, L⁆ ≠ ⊥ := by
      intro h0
      apply hne
      have h1 : ⁅z2Of Kc, conjSub t L⁆ = ⊥ := by
        have := congrArg (conjSub t) h0
        rw [← conjSub_commutator, hconjZ] at this
        exact this.trans (Subgroup.map_bot _)
      have hLZ : L ≤ Subgroup.centralizer (z2Of Kc : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h0
      have hLtZ : conjSub t L ≤ Subgroup.centralizer (z2Of Kc : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h1
      have hKZ : Kc ≤ Subgroup.centralizer (z2Of Kc : Set G) := hKc.le.trans (sup_le hLZ hLtZ)
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hKZ
    have hQMc : pCoreOf 2 Kc ≤ pCoreOf 2 Mc :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Kc).trans hKcMc)
        (hKn.trans (normalizer_le_normalizer_pCoreOf 2 Kc)) (pCoreOf_isPGroup 2 Kc)
    have hLMc : L ≤ Mc := le_of_mem_cComp hL
    have hQL : pCoreOf 2 Kc ≤ Subgroup.normalizer (L : Set G) := by
      intro q hq'
      have hqMc : q ∈ Mc := hKcMc (pCoreOf_le 2 Kc hq')
      refine mem_normalizer_of_case_iii hL htMc hKc hKn hcomm hqMc fun l hl => ?_
      have hlP : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 Mc :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mc (hLMc hl)) q⁻¹).mp
          ((pCoreOf 2 Mc).inv_mem (hQMc hq'))
      have e : q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 Mc).mul_mem (hQMc hq') hlP
    have hV2 : quasithinV2 L ≠ ⊥ :=
      quasithinV2_ne_bot_of_commutator_ne_bot hchar hLK
        (subnormal_of_mem_cComp (cComp_mem_of_le hL hLK hKcMc)) (perfect_of_mem_cComp hL)
        ((z2Of_le_pCoreOf Kc).trans (pCoreOf_le 2 Kc)) (isElemAbelian_z2Of Kc)
        (pCoreOf_le_centralizer_z2Of Kc) hQL hL0
    exact false_of_quasithinV2_ne_bot hq hmax.1 hV2
  · exact false_of_quasithinV2_ne_bot hq hmax.1 hne

end S15223

end CFSG.Quasithin
