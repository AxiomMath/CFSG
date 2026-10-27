module

public import CFSG.Quasithin.Vol2.Ch11SecFExcl
public import CFSG.Quasithin.Vol2.Ch11SecFOblAlpha
public import CFSG.Quasithin.Vol2.Ch11SecFMS
public import CFSG.Quasithin.Vol2.Ch11SecFO2L
public import CFSG.Quasithin.Vol2.Ch11SecFQ3
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

theorem false_of_obl_alpha (hF : Sp4Facts) (hGen : FactSp4Gen) (hN : SecA.NatFacts)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) (hW : ¬ IsMulCommutative ↥(wH T I V₁))
    {X : Subgroup G} (hX : IsCartanX T L X) {y : G} (hy : y ∈ L)
    (hopp : conjSubgroup V₁ y ⊓ V₃ = ⊥) {Q₀ : Subgroup G}
    (hQ₀ : Q₀ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) (hQ₀1 : Q₀ ≠ ⊥)
    (hchar : (Q₀.subgroupOf (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))).Characteristic)
    (hQ₀N : wH T I V₁ ⊔ conjSubgroup (wH T I V₁) y ≤ Subgroup.normalizer (Q₀ : Set G)) :
    False := by
  have hRC : Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) : Set G) ≤
      Subgroup.normalizer (Q₀ : Set G) := by
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (Q₀.subgroupOf (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))))
    rwa [Subgroup.map_subgroupOf_eq_of_le hQ₀] at this
  have hG₁ := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hRC
  have hTQ₀ := (SecA.IsVi.le_normalizer hV₁).trans hG₁
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_sylow h.fsu.sylow le_sup_right
  obtain ⟨hGen₁, -⟩ := gen_wH hF hGen hN h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂
    hV₃ hk hW hX hy hopp
  have hLQ₀ : L ≤ Subgroup.normalizer (Q₀ : Set G) := hGen₁.trans (sup_le
    (sup_le ((SecD.lOf_le_normalizer L V₁).trans hG₁) (le_sup_right.trans hQ₀N))
    (hOT.trans hTQ₀))
  have hM := SecA.normalizer_le_of_isPGroup h331 h
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hQ₀) hQ₀1 (sup_le hLQ₀ hTQ₀)
  exact normalizer_V₁_not_le h1154 h hV₁ (hG₁.trans hM)

theorem pCoreOf_eq_fsuV_of_le (hF : Sp4Facts) (hV3R1 : FactSp4V3R1) (hOpp : FactSp4Opp)
    (hTr : FactSp4Trans) (hGen : FactSp4Gen) (hRL : FactSp4RL) (hF15 : SecA.Facts15)
    (hN : SecA.NatFacts) (h13 : ASInputs.AS_I_1_3_Sp4) (h132 : ASInputs.AS_C_1_32)
    (hCX : Obl11_5_7Sp4CX) (hAl : Obl11_5_7Sp4Alpha) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1113 : Stmt11_1_3)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) (hV₁₃ : V₁ ≤ V₃)
    (hW : ¬ IsMulCommutative ↥(wH T I V₁))
    (hR : Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L = fsuV T I := by
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  obtain ⟨y, hy, hyX, hopp⟩ := hOpp G T L I n V₁ V₃ X hset hk hV₁ hV₃ hX
  have hQ := qOf_le_pCoreOf_normalizer hF hTr hCX hN h1102 h1103 h1110 h1113 h1141 h1143 h1154
    h1156 h hV₁ hV₂ hV₃ hk hV₁₃ hW hR hX hy hyX hopp
  have hOQ := pCoreOf_L_le hF hGen h13 hN h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂
    hV₃ hk hW hX hy hopp hQ
  by_cases hVQ : ⁅V₃, pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))⁆ = ⊥
  · exfalso
    by_cases hK : KOf L V₁ V₁ = LOf L V₁
    · apply hV3R1 G T L I n V₁ V₃ hset hk hV₁ hV₃
      have hO : pCoreOf 2 (LOf L V₁) ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
        rw [← hK]
        exact pCoreOf_le_pCoreOf_of_le_normalizer (kOf_le_normalizer_V₁ L V₁)
          (SecD.normalizer_le_normalizer_kOf L V₁ V₁)
      exact eq_bot_iff.mpr ((Subgroup.commutator_mono le_rfl hO).trans hVQ.le)
    · obtain ⟨Q₀, hQ₀, hQ₀1, hchar, hQ₀N⟩ :=
        hAl G T L I n V₁ V₃ X y h hV₁ hV₃ hk hW hR hK hX hy hyX hopp hOQ hVQ
      exact false_of_obl_alpha hF hGen hN h331 h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁
        hV₂ hV₃ hk hW hX hy hopp hQ₀ hQ₀1 hchar hQ₀N
  · have hMS := isMSPair_Q₁ h331 hF15 hN hRL h1102 h1141 h1154 h hV₁ hV₃ hk hOQ hVQ
    exact pCoreOf_eq_fsuV_of_isSp4Block hF h13 h1102 h hset hk hV₂
      (isSp4Block_of_isMSPair h132 hset hk hMS (mem_cComp_sup_pCoreOf h hV₁)
        (coe_sup_pCoreOf h hV₁))

end CFSG.Quasithin.Vol2.Ch11.SecF
