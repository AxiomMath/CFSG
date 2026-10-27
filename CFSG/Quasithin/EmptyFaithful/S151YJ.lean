module

public import CFSG.Quasithin.EmptyFaithful.S151YI
public import CFSG.Quasithin.EmptyFaithful.S153F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem input15122A7Local_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (kN : A7NotA38Type) :
    Input15122A7Local := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L α P hc hα hP hstab
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L ⟨α, hα.1, hα.2.1⟩)
  have hcore : Ya7Core L (s1516 T Z₁) α P :=
    ⟨hα.1, by rw [hα.2.1], hc.h20.sylow, hc.h18.four.2.1, hSN, hP, hstab⟩
  have hHG : ya7Pre L α P ⊔ s1516 T Z₁ ≤ g1_1516 Z₁ :=
    sup_le ((ya7Pre_le L α P).trans hLG) (s1516_le_g1 T Z₁)
  have hSH : IsSylowTwoOf (s1516 T Z₁) (ya7Pre L α P ⊔ s1516 T Z₁) :=
    ya7_isSylowTwoOf_restrict hc.h18.four le_sup_right hHG
  exact ⟨hcore.charTwo (ya7_centralizer_le hα), hcore.isMinParabolic hSH, hcore.not_C126Third hα⟩

theorem input15122A7_of_inputs (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kN : A7NotA38Type) : Input15122A7 :=
  input15122A7_of_local h118 h126 (input15122A7Local_of h37 h38 kN)

end CFSG.Quasithin
