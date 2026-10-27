module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Alpha
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Ext2

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative

theorem leaf_E1a_of (hLS1 : Leaf_LS1) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q → coreIn (a2G1 L T ⊓ a2G2 K T) (a2G1 L T) = a2Q L T := by
  intro G _ _ T M L D H K q c
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : a2G1 L T ⊓ a2G2 K T = H := hLS1 G T M L D H K q c
  obtain ⟨hTL, ⟨e⟩, hc, hmodE, -, -⟩ := c.site
  obtain ⟨α, hαs, hαk, -, hCZ⟩ :=
    L3321.exists_alpha_ext_of_TL h9 hGA c.nf.hyp c.mPlus_eq hTL e hmodE
  show coreIn (a2G1 L T ⊓ a2G2 K T) (a2G1 L T) = a2Q L T
  rw [hXH]
  refine le_antisymm ?_ (le_coreIn (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    (c.Q_le_R.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)))
  have hC1 : coreIn H (L ⊔ T) ≤ L ⊔ T := coreIn_le_left _ _
  have hCH : coreIn H (L ⊔ T) ≤ H := coreIn_le_right _ _
  have hCN : L ⊔ T ≤ Subgroup.normalizer (coreIn H (L ⊔ T) : Set G) :=
    le_normalizer_coreIn _ _
  have hHZ : H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [c.Heq]; exact inf_le_right
  have hDZ : coreIn H (L ⊔ T) ⊓ L ≤
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun x hx => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, hHZ (hCH (Subgroup.mem_inf.1 hx).1)⟩
  have hLD : L ≤ Subgroup.normalizer ((coreIn H (L ⊔ T) ⊓ L : Subgroup G) : Set G) :=
    F7.le_normalizer_inf ((le_sup_left : L ≤ L ⊔ T).trans hCN) Subgroup.le_normalizer
  have hDn : ((coreIn H (L ⊔ T) ⊓ L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_right : coreIn H (L ⊔ T) ⊓ L ≤ L)).2 hLD
  have hiff : ∀ l : ↥L, α l ∈ L3321.P2 ↔
      (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro l
    rw [hCZ]
    constructor
    · intro h
      exact Subgroup.mem_map.2 ⟨l, Subgroup.mem_comap.2 h, rfl⟩
    · intro h
      obtain ⟨y, hy, hyl⟩ := Subgroup.mem_map.1 h
      have hyl' : y = l := Subtype.ext hyl
      rw [hyl'] at hy
      exact Subgroup.mem_comap.1 hy
  have hDP : ((coreIn H (L ⊔ T) ⊓ L).subgroupOf L).map α ≤ L3321.P2 := by
    rw [Subgroup.map_le_iff_le_comap]
    intro d hd
    exact Subgroup.mem_comap.2 ((hiff d).2 (hDZ (Subgroup.mem_subgroupOf.1 hd)))
  haveI : IsSimpleGroup L3321.SL4 := FLc.isSimpleGroup_SLt (n := 4) (by norm_num)
  haveI : (((coreIn H (L ⊔ T) ⊓ L).subgroupOf L).map α).Normal :=
    Subgroup.Normal.map hDn α hαs
  have hDcore : coreIn H (L ⊔ T) ⊓ L ≤ pCoreOf 2 L := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((coreIn H (L ⊔ T) ⊓ L).subgroupOf L).map α) with hb | ht
    · intro x hx
      have hxL : x ∈ L := (Subgroup.mem_inf.1 hx).2
      have h1 : α ⟨x, hxL⟩ ∈ ((coreIn H (L ⊔ T) ⊓ L).subgroupOf L).map α :=
        Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.2 hx)
      rw [hb, Subgroup.mem_bot] at h1
      have h2 : (⟨x, hxL⟩ : ↥L) ∈ α.ker := MonoidHom.mem_ker.2 h1
      rw [hαk] at h2
      exact (Lem3328.mem_pCore_iff ⟨x, hxL⟩).1 h2
    · exfalso
      apply L3321.inf_centralizer_ne c.mPlus_eq e
      intro l hl
      have hmem : α ⟨l, hl⟩ ∈ ((coreIn H (L ⊔ T) ⊓ L).subgroupOf L).map α := by
        rw [ht]; exact Subgroup.mem_top _
      exact ((hiff ⟨l, hl⟩).1 (hDP hmem)).2
  have hCL : IsPGroup 2 ↥(coreIn H (L ⊔ T) ⊓ L) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hDcore
  have hC2 : IsPGroup 2 ↥(coreIn H (L ⊔ T)) :=
    isPGroup_two_of_le_sup c.nf.hyp.sylow.1 hTL hC1 hCL
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hC1 hCN hC2

theorem leaf_LSCV_of (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) :
    Leaf_LSCV := by
  intro G _ _ T M L D H K q c
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, ⟨e⟩, hc, hmodE, -, -⟩ := c.site
  obtain ⟨α, hαs, hαk, -, -⟩ :=
    L3321.exists_alpha_ext_of_TL h9 hGA c.nf.hyp c.mPlus_eq hTL e hmodE
  show (L ⊔ T) ⊓ Subgroup.centralizer (vPlus L T : Set G) ≤ pCoreOf 2 (L ⊔ T)
  obtain ⟨-, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hVN : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := sup_le hLV hTV
  have h7' := h7 G T M L D c.nf.hyp
  rw [c.mPlus_eq] at h7'
  have hQV : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (vPlus L T : Set G) := by
    rw [← h7'.1.2]; exact inf_le_right
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (c.TL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)]
    rfl
  have hKidx : ((L ⊓ Subgroup.centralizer (vPlus L T : Set G)).subgroupOf L).index = 20160 := by
    have h := CFSG.Quasithin.AutOn.card_autOn_eq_relIndex hLV
    rw [hcard] at h
    exact h.symm
  have hkerIdx : α.ker.index = 20160 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hαs, Subgroup.card_top,
      Ln2.card_specialLinear 4 (Or.inl rfl)]
    rfl
  have hkerLE : α.ker ≤ (L ⊓ Subgroup.centralizer (vPlus L T : Set G)).subgroupOf L := by
    intro l hl
    have hl0 : l ∈ CFSG.pCore 2 ↥L := by rw [← hαk]; exact hl
    have hlC : (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G) :=
      hQV (hOL ((Lem3328.mem_pCore_iff l).1 hl0))
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨l.2, hlC⟩)
  have hK_le : (L ⊓ Subgroup.centralizer (vPlus L T : Set G)).subgroupOf L ≤ α.ker := by
    have h1 := Subgroup.relIndex_mul_index hkerLE
    rw [hKidx, hkerIdx] at h1
    exact Subgroup.relIndex_eq_one.1 (by omega)
  have hLC : L ⊓ Subgroup.centralizer (vPlus L T : Set G) ≤ pCoreOf 2 L := by
    intro x hx
    have hxk : (⟨x, (Subgroup.mem_inf.1 hx).1⟩ : ↥L) ∈ α.ker :=
      hK_le (Subgroup.mem_subgroupOf.2 hx)
    rw [hαk] at hxk
    exact (Lem3328.mem_pCore_iff _).1 hxk
  have hC'L : ((L ⊔ T) ⊓ Subgroup.centralizer (vPlus L T : Set G)) ⊓ L ≤ pCoreOf 2 L := by
    intro x hx
    obtain ⟨hxC, hxL⟩ := Subgroup.mem_inf.1 hx
    exact hLC (Subgroup.mem_inf.2 ⟨hxL, (Subgroup.mem_inf.1 hxC).2⟩)
  have hC'2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (vPlus L T : Set G)) :=
    isPGroup_two_of_le_sup c.nf.hyp.sylow.1 hTL inf_le_left
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hC'L)
  have hCN : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (vPlus L T : Set G) : Subgroup G) : Set G) :=
    F7.le_normalizer_inf Subgroup.le_normalizer
      (hVN.trans (F7.normalizer_le_normalizer_centralizer _))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCN hC'2

end CFSG.Quasithin.H13.NFa2
