module

public import CFSG.Quasithin.EmptyFaithful.S1421Q9D
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Q16

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

omit [Finite G] in
theorem omegaOneCenter_le_T (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1.1

theorem isPGroup_omegaOneCenter (st : Setting1427 T M H K1) :
    IsPGroup 2 (quasithinOmegaOneCenter T) :=
  st.hyp.sylow.1.to_le (omegaOneCenter_le_T T)

theorem omegaOneCenter_le_mcOf (st : Setting1427 T M H K1) : quasithinOmegaOneCenter T ≤ mcOf T :=
  (omegaOneCenter_le_T T).trans st.hyp.toQTFE14.t_le_mc

theorem omegaOneCenter_le_pCoreOf_mcOf (st : Setting1427 T M H K1) :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 (mcOf T) :=
  le_pCoreOf_of_le_normalizer 2 (omegaOneCenter_le_mcOf st)
    (Subgroup.centralizer_le_normalizer _) (isPGroup_omegaOneCenter st)

theorem pCoreOf_mcOf_le_pCoreOf_H (st : Setting1427 T M H K1) :
    pCoreOf 2 (mcOf T) ≤ pCoreOf 2 H :=
  pCoreOf_le_pCoreOf_of_sylow (Q9.H_le_mcOf st) (Q9.isSylowTwoOf_mcOf st).2.1 st.hStar.1.1
    (Q9.isSylowTwoOf_mcOf st).2.2

theorem pCoreOf_mcOf_le_T (st : Setting1427 T M H K1) : pCoreOf 2 (mcOf T) ≤ T :=
  (pCoreOf_le_pCoreOf_of_sylow st.hyp.toQTFE14.t_le_mc (Q9.isSylowTwoOf_mcOf st).2.1 le_rfl
    (Q9.isSylowTwoOf_mcOf st).2.2).trans (pCoreOf_le 2 T)

theorem pCoreOf_mcOf_le_sOf (st : Setting1427 T M H K1) :
    pCoreOf 2 (mcOf T) ≤ S1421.sOf T K1 :=
  le_inf (pCoreOf_mcOf_le_T st) ((pCoreOf_mcOf_le_pCoreOf_H st).trans st.notation_.pCore_le)

theorem sup_sOf_le_mcOf (st : Setting1427 T M H K1) : K1 ⊔ S1421.sOf T K1 ≤ mcOf T :=
  sup_le (Q9.k1_le_mcOf st) (inf_le_left.trans st.hyp.toQTFE14.t_le_mc)

theorem pCoreOf_mcOf_le_pCoreOf_sup (st : Setting1427 T M H K1) :
    pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (K1 ⊔ S1421.sOf T K1) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_mcOf_le_sOf st).trans le_sup_right)
    ((sup_sOf_le_mcOf st).trans (le_normalizer_pCoreOf 2 (mcOf T)))
    (pCoreOf_isPGroup 2 (mcOf T))

theorem charTwo_mcOf (st : Setting1427 T M H K1) : CharTwo (mcOf T) :=
  charTwo_of_inH' st.hyp.qtke st.hyp.sylow
    ⟨st.hyp.toQTFE14.t_le_mc, pCoreOf_ne_bot_of_isTwoLocal st.hyp.mc_max.1⟩

end Q16

end CFSG.Quasithin
