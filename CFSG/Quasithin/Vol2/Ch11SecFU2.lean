module

public import CFSG.Quasithin.Vol2.Ch11SecFU
public import CFSG.Quasithin.Vol2.Ch11SecFBlock
public import CFSG.Quasithin.Vol2.Ch11SecFFacts2
public import CFSG.Quasithin.Vol2.Ch11SecFW

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem le_conjClosure_self {G : Type} [Group G] (Z H : Subgroup G) : Z ≤ conjClosure Z H :=
  fun z hz => by simpa using mem_conjClosure (Subgroup.one_mem H) hz

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

theorem conjClosure_V₃_le_pCoreOf_sup (hF : Sp4Facts) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3)
    (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) :
    conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 (L ⊔ T) := by
  have hQ := fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  have hUW : conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) ≤
      conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) :=
    conjClosure_mono (SecA.IsVi.le_fsuV hV₃) le_rfl
  have hUT : conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) ≤ T :=
    hUW.trans ((conjClosure_le_pCoreOf hQ).trans (pCoreOf_normalizer_V₁_le_T h hV₁))
  have hUC : conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) ≤
      Subgroup.centralizer (fsuV T I : Set G) :=
    (conjClosure_V₃_le_centralizer hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃
      hk).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure_self _ _)))
  exact (le_inf hUT hUC).trans (inf_centralizer_le_pCoreOf_sup h1102 h)

theorem conjClosure_V₃_le_pCoreOf_L (hF : Sp4Facts) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3)
    (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃)
    (hk : KindSp4 L (fsuV T I) n) (hK : KOf L V₁ V₁ = LOf L V₁) :
    conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 L := by
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  obtain ⟨-, -, -, h3⟩ := h1155 G T L I n V₁ V₃ (Subgroup.normalizer (V₁ : Set G)) h hV₁ hV₃
    (inH_normalizer_V₁ h hV₁) (normalizer_V₁_not_le h1154 h hV₁) le_rfl
  obtain ⟨s, W, F, _, _, -, hWU, -, hsup, hnat⟩ := h3 hK
  have hUO := conjClosure_V₃_le_pCoreOf_sup hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h
    hV₁ hV₂ hV₃ hk
  have hV₁O : V₁ ≤ pCoreOf 2 L := (SecA.IsVi.le_fsuV hV₁).trans (fsuV_le_pCoreOf_L hF h hset hk hV₂)
  rw [← hsup]
  refine sup_le hV₁O (iSup_le fun i => ?_)
  have hKN : KOf L V₁ V₁ ≤ Subgroup.normalizer (V₁ : Set G) := kOf_le_normalizer_V₁ L V₁
  refine (le_commutator_sup_of_isNaturalSection (hnat i) (hWU i).1 hKN).trans (sup_le ?_ hV₁O)
  refine (Subgroup.commutator_mono ((hWU i).2.trans hUO) ?_).trans (commutator_pCoreOf_sup_le h)
  rw [hK]
  exact (perfectCore_le _).trans inf_le_left

theorem conjClosure_V₃_eq (hVL1 : FactSp4VL1) (h1102 : Stmt11_0_2)
    (h1141 : Stmt11_4_1) (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hK : KOf L V₁ V₁ = LOf L V₁) (hO : pCoreOf 2 L = fsuV T I)
    (hUO : conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 L)
    (hV₁₃ : V₁ ≤ V₃) : conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) = V₃ := by
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  obtain ⟨-, -, -, h3⟩ := h1155 G T L I n V₁ V₃ (Subgroup.normalizer (V₁ : Set G)) h hV₁ hV₃
    (inH_normalizer_V₁ h hV₁) (normalizer_V₁_not_le h1154 h hV₁) le_rfl
  obtain ⟨s, W, F, _, _, -, hWU, -, hsup, hnat⟩ := h3 hK
  refine le_antisymm ?_ (le_conjClosure_self _ _)
  rw [← hsup]
  refine sup_le hV₁₃ (iSup_le fun i => ?_)
  have hKN : KOf L V₁ V₁ ≤ Subgroup.normalizer (V₁ : Set G) := kOf_le_normalizer_V₁ L V₁
  refine (le_commutator_sup_of_isNaturalSection (hnat i) (hWU i).1 hKN).trans (sup_le ?_ hV₁₃)
  have hWV : W i ≤ fsuV T I := ((hWU i).2.trans hUO).trans hO.le
  rw [hK]
  exact (Subgroup.commutator_mono hWV le_rfl).trans (hVL1 G T L I n V₁ V₃ hset hk hV₁ hV₃)

theorem false_of_kOf_eq_of_pCoreOf_eq (hF : Sp4Facts) (hVL1 : FactSp4VL1) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3) (h1114 : Stmt11_1_4) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) (h1156 : Stmt11_5_6)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) (hK : KOf L V₁ V₁ = LOf L V₁)
    (hO : pCoreOf 2 L = fsuV T I) (hV₁₃ : V₁ ≤ V₃) : False := by
  have hUO := conjClosure_V₃_le_pCoreOf_L hF h1102 h1103 h1113 h1141 h1143 h1154 h1155 h1156 h
    hV₁ hV₂ hV₃ hk hK
  have hU := conjClosure_V₃_eq hVL1 h1102 h1141 h1154 h1155 h hV₁ hV₃ hk hK hO hUO hV₁₃
  apply normalizer_V₁_not_le h1154 h hV₁
  refine le_trans ?_ (h1114 G T L I n V₁ V₃ h hV₁ hV₃).2
  refine le_inf ?_ ?_
  · have := le_normalizer_conjClosure V₃ (Subgroup.normalizer (V₁ : Set G))
    rwa [hU] at this
  · have := SecD.normalizer_le_normalizer_kOf L V₁ V₁
    rwa [hK] at this

end CFSG.Quasithin.Vol2.Ch11.SecF
