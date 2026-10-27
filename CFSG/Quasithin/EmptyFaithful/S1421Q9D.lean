module

public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.EmptyFaithful.S1421Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Q9

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem k1_le_H (st : Setting1427 T M H K1) : K1 ≤ H :=
  st.notation_.le_K.trans (oTwoUpper_le H)

theorem sup_eq_hStar (st : Setting1427 T M H K1) : K1 ⊔ T = H := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo st.hyp.sylow
  have hTH : (S : Subgroup G) ≤ H := st.hStar.1.1
  have hYH : K1 ⊔ (S : Subgroup G) ≤ H := sup_le (k1_le_H st) hTH
  have hY : InH (S : Subgroup G) (K1 ⊔ (S : Subgroup G)) :=
    inH_of_le S le_sup_right hYH st.hStar.1
  exact st.hStar.2.2 _ hY hYH fun hle => st.notation_.not_le (le_sup_left.trans hle)

theorem H_le_mcOf (st : Setting1427 T M H K1) : H ≤ mcOf T :=
  (st.hyp.isUniqueM_centralizer st.hStar.1 st.hStar.2.1).1.2

theorem k1_le_mcOf (st : Setting1427 T M H K1) : K1 ≤ mcOf T :=
  (k1_le_H st).trans (H_le_mcOf st)

theorem isSylowTwoOf_mcOf (st : Setting1427 T M H K1) : IsSylowTwoOf T (mcOf T) :=
  isSylowTwoOf_of_quasithinIsSylowTwo st.hyp.sylow st.hyp.toQTFE14.t_le_mc

theorem isSylowTwoOf_H (st : Setting1427 T M H K1) : IsSylowTwoOf T H :=
  isSylowTwoOf_of_quasithinIsSylowTwo st.hyp.sylow st.hStar.1.1

theorem pCoreOf_mcOf_ne_bot (st : Setting1427 T M H K1) : pCoreOf 2 (mcOf T) ≠ ⊥ :=
  pCoreOf_ne_bot_of_isTwoLocal st.hyp.mc_max.1

theorem exists_cComp_mcOf (h37 : A37ForSQTK) (h39 : A39ForSQTK) (st : Setting1427 T M H K1)
    {B : Subgroup G} (hB : B ∈ lFamily T) (hBM : B ≤ mcOf T) :
    ∃ Kc ∈ cComp (mcOf T), B ≤ Kc :=
  lemma_1_2_4_exists st.hyp.qtke st.hyp.simple st.hyp.nonabelian h37 h39
    (pCoreOf_mcOf_ne_bot st) (isSylowTwoOf_mcOf st) hBM hB

theorem isLocal_of_cComp_mcOf (st : Setting1427 T M H K1) {Kc : Subgroup G}
    (hKc : Kc ∈ cComp (mcOf T)) : quasithinIsLocal T Kc :=
  isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_mcOf st) (pCoreOf_mcOf_ne_bot st) hKc

theorem isLocal_of_cComp_H (st : Setting1427 T M H K1) {L : Subgroup G} (hL : L ∈ cComp H) :
    quasithinIsLocal T L :=
  isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_H st) st.hStar.1.2 hL

end Q9

end CFSG.Quasithin
