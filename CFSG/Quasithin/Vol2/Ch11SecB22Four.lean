module

public import CFSG.Quasithin.Vol2.Ch11SecB22Two
public import CFSG.Quasithin.Vol2.Ch11SecB23

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem mem_TL_of_mem_sup (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {t : G} (ht : t ∈ T)
    (htL : t ∈ L ⊔ Subgroup.centralizer (fsuV T I : Set G)) : t ∈ TL T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := L_le_normalizer_fsuV hyp
  have hCn : L ≤ Subgroup.normalizer (Subgroup.centralizer (fsuV T I : Set G) : Set G) :=
    B2F.le_normalizer_centralizer hLV
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L _ hCn] at htL
  obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.mp htL
  have hcLT : c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨?_, hc⟩
    have : c = l⁻¹ * (l * c) := by group
    rw [this]
    exact (L ⊔ T).mul_mem (Subgroup.mem_sup_left (L.inv_mem hl)) (Subgroup.mem_sup_right ht)
  have hY2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    isPGroup_sup_inf_centralizer h1102 hyp
  have hYn : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer
      (B2F.le_normalizer_centralizer (sup_le hLV (T_le_normalizer_fsuV T I)))
  have hcO : c ∈ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hYn hY2 hcLT
  exact ⟨ht, (L ⊔ pCoreOf 2 (L ⊔ T)).mul_mem (Subgroup.mem_sup_left hl)
    (Subgroup.mem_sup_right hcO)⟩

theorem TL_le_centralizer (hFC1 : FactFlagOneCentral) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    TL T L ≤ Subgroup.centralizer (V₁ : Set G) := by
  obtain ⟨hV, hn, hLV, hVL, hnat, -, -⟩ := natSetting h1102 hyp
  have hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  have hTLC := hFC1 G L (fsuV T I) T V₁ n hV hn hLV hVL hnat hTS (T_le_normalizer_fsuV T I)
    hyp.normal (IsVi.cV_le hV₁) (IsVi.le_fsuV hV₁) (IsVi.isEndStable hV₁)
    (by rw [IsVi.relIndex_eq hV₁, mul_one]) (IsVi.le_normalizer hV₁)
  obtain ⟨-, -, hO2⟩ := h3228 G T L I hyp.fsu
  rw [fsuL0_eq hyp] at hO2
  have hOC : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V₁ : Set G) :=
    hO2 ▸ inf_le_right.trans (Subgroup.centralizer_le (IsVi.le_fsuV hV₁))
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := hO2 ▸ inf_le_left
  have hON : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) := hOT.trans hyp.normal
  intro t ht
  obtain ⟨htT, htL⟩ := Subgroup.mem_inf.mp ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L _ hON] at htL
  obtain ⟨l, hl, o, ho, rfl⟩ := Set.mem_mul.mp htL
  have hlT : l ∈ T := by
    have : l = l * o * o⁻¹ := by group
    rw [this]
    exact T.mul_mem htT (T.inv_mem (hOT ho))
  exact Subgroup.mul_mem _ (hTLC ⟨hlT, hl⟩) (hOC ho)

theorem wClos_le_TL (hFM : FactMParam) (hFH : FactHyperplaneT) (hS44 : FactSp4FourExt)
    (hN : FactNot4213) (hA2 : FactA2InL) (hFC1 : FactFlagOneCentral) (h4213 : TmpL6_4_2_13)
    (h311 : Theorem311Stmt) (h63 : ASInputs.AS_E_6_3) (h664 : ASInputs.AS_E_6_6_four)
    (h614 : ASInputs.AS_E_6_14) (h3228 : Ch10.TmpL6_3_2_2_eight) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) {m : ℕ}
    (hm : KindG2 L (fsuV T I) n ∧ m = 2 * n ∨ ¬ KindG2 L (fsuV T I) n ∧ m = n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (j : ℕ) (hj : j + 1 < m) :
    E3.wClos (fsuV T I) j T ≤ TL T L ∧
      V₁ ≤ Subgroup.centralizer (E3.wClos (fsuV T I) j T : Set G) := by
  obtain ⟨hV, hn, hLV, hVL, hnat, -, -⟩ := natSetting h1102 hyp
  have hTV := T_le_normalizer_fsuV T I
  have hs := sParam_eq hFM hFH hS44 hN h4213 h311 h63 h664 h614 h331 h1102 h1103 hyp hm hV
  have hW : E3.wClos (fsuV T I) j T ≤ TL T L := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hAj⟩ := hA
    intro a ha
    have haT : a ∈ T := hAT ha
    by_cases haC : a ∈ Subgroup.centralizer (fsuV T I : Set G)
    · exact mem_TL_of_mem_sup h1102 hyp haT (Subgroup.mem_sup_right haC)
    have hAAg : A ≤ conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G) :=
      le_inf hAg (hAT.trans hTV)
    have hb : E3.mQuot (conjSubgroup (fsuV T I) g)
        (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G)) ≤ j :=
      hAj ▸ E3.mQuot_mono (V := conjSubgroup (fsuV T I) g) hAAg
    have hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥ := by
      intro h
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact haC (h (hAg ha))
    have hmem := E3.e3_10_two hV (by rw [hs]; omega) hnc
    have hmem2 : autI hV (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G)) ∈
        E3.aSet 2 (autI hV ⊤) := by
      obtain ⟨h1, h2, h3, h4⟩ := hmem
      exact ⟨h1, h2, h3, fun B hB hBk => h4 B hB (by rw [hs]; omega)⟩
    have hle := hA2 G L (fsuV T I) ⊤ n hV hn hLV hVL hnat le_top
      (inf_le_right.trans (normalizer_fsuV_le h331 hyp)) _ hmem2
    have haN : a ∈ Subgroup.normalizer (fsuV T I : Set G) := hTV haT
    obtain ⟨l, hl, hlV, hla⟩ := mem_autOn_iff.mp
      (hle (conjV_mem_autOn (hAAg ha) haN))
    have hc : l⁻¹ * a ∈ Subgroup.centralizer (fsuV T I : Set G) :=
      (conjV_eq_conjV_iff hlV haN).mp hla.symm
    have e : a = l * (l⁻¹ * a) := by group
    rw [e] at haT ⊢
    exact mem_TL_of_mem_sup h1102 hyp haT
      ((L ⊔ Subgroup.centralizer (fsuV T I : Set G)).mul_mem (Subgroup.mem_sup_left hl)
        (Subgroup.mem_sup_right hc))
  refine ⟨hW, fun v hv => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (TL_le_centralizer hFC1 h3228 h1102 hyp hV₁ (hW hw))
    v hv).symm

end CFSG.Quasithin.Vol2.Ch11.SecB
