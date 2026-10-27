module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Two
public import CFSG.Quasithin.EmptyFaithful.S1421L11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

omit [Finite G] in
theorem isMulCommutative_uOfL22_of_hypF98
    (h : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T)) :
    IsMulCommutative ↥(uOfL22 T M) :=
  h.F911_3.1

theorem hypF98_of_isHz (st : Setting1427 T M H K1) (hU : IsMulCommutative ↥(uOfL22 T M)) :
    HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H := by
  have h1281 := lemma_14_2_4 st.hyp st.facts
  have hHz : IsHz T M (yOfL22 T M) H :=
    (lemma_14_2_5 st.hyp st.facts).mpr ⟨st.hStar.1, st.hStar.2.1⟩
  have h81 : HypF81 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) H :=
    h1281.hypF81_of_commutator (fun _ hg => h1281.commutator_eq_bot_of_abelian hU hg) hHz
  exact h81.toHypF98 st.hyp.card_omegaOneCenter

theorem le_normalizer_oTwoUpper_of_setting (st : Setting1427 T M H K1) :
    T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  st.hStar.1.1.trans (le_normalizer_oTwoUpper H)

theorem sqtkGroup_of_inH (st : Setting1427 T M H K1) : SQTKGroup ↥H := by
  obtain ⟨hk, hq⟩ := isSQTKSub_of_inH st.hyp.qtke st.hyp.simple st.hyp.nonabelian st.hStar.1
  exact ⟨hq, hk⟩

theorem hypF918_of_cfg (st : Setting1427 T M H K1) (hU : IsMulCommutative ↥(uOfL22 T M))
    (hK : oTwoUpper H ∈ cComp (mcOf T))
    (hq : CFSG.IsQuasisimple (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H))) :
    HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H (oTwoUpper H) := by
  have hTK := le_normalizer_oTwoUpper_of_setting st
  have hcc : conjClosure (oTwoUpper H) T = oTwoUpper H := H13.L1295B.conjClosure_eq hTK
  have hHM : H ≤ mcOf T := (st.hyp.isUniqueM_centralizer st.hStar.1 st.hStar.2.1).1.2
  refine
    { toHypF98 := hypF98_of_isHz st hU
      K_cComp := cComp_mem_of_le hK (oTwoUpper_le H) hHM
      K_quasisimple := ?_
      H_eq := ?_
      K₀_normal := ?_ }
  · have e : (pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H) = CFSG.pCore 2 ↥(oTwoUpper H) := by
      rw [pCoreOf, map_subtype_subgroupOf']
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq e.symm) hq
  · rw [hcc]
    refine le_antisymm ?_ (sup_le (oTwoUpper_le H) inf_le_right)
    exact (sup_oTwoUpper_eq st).ge.trans (sup_le_sup_left (le_inf le_sup_right st.hStar.1.1) _)
  · rw [hcc]
    exact le_normalizer_oTwoUpper H

end S1421

end CFSG.Quasithin
