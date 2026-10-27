module

public import CFSG.Quasithin.Vol2.Ch11SecBNPMainS
public import CFSG.Quasithin.Vol2.Ch11SecE44S
public import CFSG.Quasithin.Vol2.Ch11SecD552

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem not_kindG2_of_kOf_eqS (hp778 : SecB.AS_p778_nParamS) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1122 : Stmt11_2_2) (h1143 : Stmt11_4_3)
    (h1144 : SecE.Stmt11_4_4S) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hK : KOf L V₁ V₁ = LOf L V₁) : ¬ KindG2 L (fsuV T I) n := by
  intro hG2
  have hT2 : IsPGroup 2 T := h.fsu.sylow.1
  have hV₁T : V₁ ≤ T := (SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)
  obtain ⟨z, hzV₁, hz1, hzT⟩ := exists_z h hV₁
  have hzV : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨SecA.IsVi.le_fsuV hV₁ hzV₁, hzT⟩
  set Y := Subgroup.centralizer ({z} : Set G) ⊓
    sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) with hY
  have hYM : ¬ Y ≤ Subgroup.normalizer (L : Set G) := (h1143 G T L I n V₁ h hV₁ z hzV hz1).2.1 hK
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzT) t ht
  have hTK : T ≤ Subgroup.normalizer (KOf L V₁ V₁ : Set G) :=
    (SecA.IsVi.le_normalizer hV₁).trans (normalizer_le_normalizer_kOf L V₁ V₁)
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
    mem_normalizer_inf (Subgroup.le_normalizer (hTz ht)) (mem_normalizer_sectionCentralizer
      (hTK ht) (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hTK ht)))
  have hYTz : Y ⊔ T ≤ Subgroup.centralizer ({z} : Set G) := sup_le inf_le_left hTz
  have hzT2 : IsPGroup 2 (Subgroup.zpowers z) :=
    hT2.to_le (Subgroup.zpowers_le.mpr (hV₁T hzV₁))
  have hP : InH T (Y ⊔ T) :=
    inH_of_le le_sup_right ((Subgroup.zpowers_le.mpr (hV₁T hzV₁)).trans le_sup_right) hzT2
      (Subgroup.zpowers_ne_bot.mpr hz1)
      fun x hx => mem_normalizer_zpowers_of_mem_centralizer (hYTz hx)
  obtain ⟨H, hH, hHP⟩ := exists_isHStar_le _ (Y ⊔ T) rfl hP fun hle => hYM (le_sup_left.trans hle)
  have hO2 : oTwoUpper H ≤ Y := oTwoUpper_le_of_le_sup' hHP hT2 hTY
  have hlie := h1144 G T L I n V₁ h hV₁ hK z hzV hz1 H hH (hHP.trans hYTz)
  set R₁ := ROf T L V₁ with hR₁
  have hR₁T := ROf_le_T h V₁
  have hn1 := hp778 G T (Subgroup.normalizer (L : Set G)) H R₁ h.fsu.simple h.fsu.nonabelian
    h.fsu.qtke h.fsu.sylow ⟨SecA.isMaxTwoLocal_M h331 h, h.normal⟩ hH hlie hR₁T
  have hsylH : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1
  have hHO : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hTO := A4.isSylowTwoOf_inf_normal hsylH (oTwoUpper_le H) hHO
  have hTOR : T ⊓ oTwoUpper H ≤ R₁ := by
    have h1 := inf_sectionCentralizer_le_ROf h hV₁
    rw [← hK] at h1
    exact fun x hx => h1 ⟨hx.1, (hO2 hx.2).2⟩
  have hReq : R₁ ⊓ oTwoUpper H = T ⊓ oTwoUpper H :=
    le_antisymm (inf_le_inf_right _ hR₁T) (le_inf hTOR inf_le_right)
  have hS : IsSylowIn 2 R₁ (R₁ ⊔ oTwoUpper H) := isSylowIn_sup_of_normal
    (hT2.to_le hR₁T) (hR₁T.trans (hH.1.1.trans hHO)) (by rw [hReq]; exact hTO.2.2)
  have hV₁R : V₁ ≤ R₁ ⊔ oTwoUpper H := (le_ROf hV₁T (hT2.to_le hV₁T)
    (lOf_le_normalizer L V₁) (SecA.IsVi.le_normalizer hV₁)).trans le_sup_left
  have heven : Even (Nat.card ↥(R₁ ⊔ oTwoUpper H)) := by
    rw [even_iff_two_dvd]
    exact dvd_trans (two_dvd_card_of_ne_bot (hT2.to_le hV₁T) (SecA.IsVi.ne_bot h hV₁ le_rfl))
      (Subgroup.card_dvd_of_le hV₁R)
  have hle := le_M_of_sylow_R₁ h1102 h1110 h1122 h hG2 hV₁ hS
    (nParam_eq_one_of_le_one hn1 heven)
  apply hH.2.1
  rw [← oTwoUpper_sup_eq_of_sylow' hsylH]
  exact sup_le (le_sup_right.trans hle) h.normal

theorem false_of_kindG2S (hp778 : SecB.AS_p778_nParamS) (hFact : FactSolvPointG2)
    (hMult : SL2pMultFact) (hSig : L2pSignalizerFact) (hTI : PointsTIFact) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h1122 : Stmt11_2_2)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1144 : SecE.Stmt11_4_4S) (h : Hyp11 G T L I n)
    [IsMulCommutative ↥(fsuV T I)] (hG2 : KindG2 L (fsuV T I) n)
    (hreal : G2NaturalDerived (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) n) : False := by
  obtain ⟨V₁, hV₁, -⟩ := (h1110 G T L I n h).1 1 le_rfl (by norm_num)
  rcases (le_conjClosure (LOf L V₁) (Subgroup.normalizer (V₁ : Set G))).eq_or_lt with heq | hlt
  · exact not_kindG2_of_kOf_eqS hp778 h331 h1102 h1110 h1122 h1143 h1144 h hV₁ heq.symm hG2
  · obtain ⟨X, hX⟩ := exists_isCartanX h
    rcases (h1141 G T L I n V₁ X h hV₁ hX).2.1 _
        (kOf_cComp_centralizer hTI h1102 h1110 h1112 h1141 h1143 h hV₁) hlt with h1 | h2
    · exact false_of_case_one hFact hMult hTI h1102 h1110 h1112 h1122 h1141 h1143 h hG2 hreal
        hV₁ h1
    · exact false_of_case_two hSig h1102 h1110 h1112 h1122 h hG2 hV₁ hlt h2

theorem stmt11_5_1_ofS (hp778 : SecB.AS_p778_nParamS) (hFact : FactSolvPointG2)
    (hMult : SL2pMultFact) (hSig : L2pSignalizerFact) (hTI : PointsTIFact) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h1122 : Stmt11_2_2)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1144 : SecE.Stmt11_4_4S) : Stmt11_5_1 := by
  intro G _ _ T L I n h
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  rcases hk with ⟨K, hF, hK, hc, he, -⟩ | ⟨K, hF, hK, hc, he, -⟩ | ⟨K, hF, hK, hc, he, hreal⟩
  · exact Or.inl ⟨K, hF, hK, hc, he⟩
  · exact Or.inr ⟨K, hF, hK, hc, he⟩
  · exact (false_of_kindG2S hp778 hFact hMult hSig hTI h331 h1102 h1110 h1112 h1122 h1141 h1143
      h1144 h ⟨K, hF, hK, hc, he⟩ hreal).elim

end CFSG.Quasithin.Vol2.Ch11.SecD
