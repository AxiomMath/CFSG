module

public import CFSG.Quasithin.MS93.S512JFrame

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512J

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem uSub_inf_centralizer_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (μ γ : Vtx (puAmalgam h.le)) :
    S5.uSub h.le L (g • μ) ⊓
        Subgroup.centralizer (ZM _ (g • γ) : Set (puAmalgam h.le).Universal) =
      (S5.uSub h.le L μ ⊓
        Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).map
          (MulAut.conj g).toMonoidHom := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  rw [S5B.uSub_smul h.le hLn, zm_smul, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

theorem zm_inf_zm_inf_zm_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (x y z : Vtx (puAmalgam h.le)) :
    ZM (puAmalgam h.le) (g • x) ⊓ ZM _ (g • y) ⊓ ZM _ (g • z) =
      (ZM (puAmalgam h.le) x ⊓ ZM _ y ⊓ ZM _ z).map (MulAut.conj g).toMonoidHom := by
  rw [zm_smul, zm_smul, zm_smul, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

theorem commutator_zm_zm_smul (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    (x y : Vtx (puAmalgam h.le)) :
    ⁅ZM (puAmalgam h.le) (g • x), ZM (puAmalgam h.le) (g • y)⁆ =
      ⁅ZM (puAmalgam h.le) x, ZM (puAmalgam h.le) y⁆.map (MulAut.conj g).toMonoidHom := by
  rw [zm_smul, zm_smul, Subgroup.map_commutator]

theorem three56ResL_base (h32 : S32) (h52 : S52) (h54 : S54) (hZ : S5Q2.Q2EvenZ)
    (hone : S512Z.OneCF) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a)
    {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)}
    (hchS : S5B.IsChain512Sel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) α' ν μ₁ μ₂)
    (hq1 : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hc56 : S5.Concl56 h (2 ^ k) a α' l g x)
    {w : (puAmalgam h.le).Universal}
    (hwcase : (w = x ∧ μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ∨
      (w = x⁻¹ ∧ μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2))
    (hnw : ¬ ZM _ (w • α') ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal))
    (hlarge : 2 ^ k < (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁))
    (hcrit : IsCritical _ μ₁ (w • geo _ (baseA (puAmalgam h.le)) α' 2)) :
    w ∈ stab _ (baseA (puAmalgam h.le)) ∧
      S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer
          (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Set (puAmalgam h.le).Universal) ≠
        S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer
          (ZM _ (w • geo _ (baseA (puAmalgam h.le)) α' 2) : Set (puAmalgam h.le).Universal) ∧
      ⁅ZM (puAmalgam h.le) μ₁, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
        stabCenter _ (baseA (puAmalgam h.le)) ∧
      ⁅ZM (puAmalgam h.le) μ₁, ZM (puAmalgam h.le) (w • geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
        stabCenter _ (baseA (puAmalgam h.le)) ∧
      (Xq M = Uq M T L ⊔ Zq M L → ZM _ μ₁ ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
        ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ stabCenter _ (baseA (puAmalgam h.le))) ∧
      (Xq M = Uq M T L ⊔ Zq M L → ZM _ μ₁ ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
        ZM _ (w • geo _ (baseA (puAmalgam h.le)) α' 2) ≤
          stabCenter _ (baseA (puAmalgam h.le))) := by
  have hch := S5B.isChain512Sel_subset hchS
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨hc, hαβ, hcμ, ⟨y, hy, hμy⟩, -, -, hβγ⟩ := S512T.chain_geo h hb4 hch
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγ
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hxP : x ∈ S5.vPre h.le a (MSP.stab l) := hc56.2.2.2 hq1
  have hopp : S5.Opp56 h (2 ^ k) a l g x := S512R.opp56_of_mem_stab h hxst hc56 hxP
  have hμ : μ₁ = g⁻¹ • γ ∨ μ₁ = x⁻¹ • g⁻¹ • γ := by
    rcases hwcase with ⟨-, he⟩ | ⟨-, he⟩
    · exact Or.inl he
    · exact Or.inr he
  have hwst : w ∈ stab _ (baseA (puAmalgam h.le)) := by
    rcases hwcase with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hxst
    · exact inv_mem hxst
  have hν : w⁻¹ • μ₁ = g⁻¹ • γ ∨ w⁻¹ • μ₁ = x⁻¹ • g⁻¹ • γ := by
    rcases hwcase with ⟨rfl, he⟩ | ⟨rfl, he⟩
    · right
      rw [he]
    · left
      rw [he, inv_inv, smul_inv_smul]
  have hμlam : μ₁ ∈ S5.lam h (2 ^ k) a α' γ := ⟨g, x, hg, hx, Or.inr ⟨l, hl, hc56⟩, hμ⟩
  have hνlam : w⁻¹ • μ₁ ∈ S5.lam h (2 ^ k) a α' γ := ⟨g, x, hg, hx, Or.inr ⟨l, hl, hc56⟩, hν⟩
  have hZ2 : ZM _ (w • α') ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (w • γ)) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) :
        Set (puAmalgam h.le).Universal) := by
    have h1 := hone G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS (w⁻¹ • μ₁) hνlam
    rw [S512T.zHat_eq h hd hc hq1] at h1
    have h2 := S512R.zm_le_normalizer_smul h hwst h1
    rwa [smul_inv_smul] at h2
  have hneO : S5.uSub h.le L μ₁ ⊓
        Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) ≠
      S5.uSub h.le L μ₁ ⊓
        Subgroup.centralizer (ZM _ (w • γ) : Set (puAmalgam h.le).Universal) := by
    rw [← S512T.uSub_inf_qv_eq h hb4 hcμ, ← S512T.uSub_inf_qv_eq h hb4 hcrit]
    intro heq
    apply hnw
    rw [heq]
    exact hZ2
  have hcent := S512R.cent56F_holds_e h32 h52 hZ G M T L h hmin hb k F _ _ a hd α' hc hαβ l hl
    g hg x hx hc56 hopp
  have hR₂O : ⁅ZM (puAmalgam h.le) μ₁, ZM (puAmalgam h.le) (w • γ)⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
    have h1 := S512R.commutator_zm_smul_le_stabCenter h hwst (hcent (w⁻¹ • μ₁) hν)
    rwa [smul_inv_smul] at h1
  have hlgγ : S512Z.Large h k γ (baseA _) := by
    have h1 : S512Z.Large h k (y • γ) (y • baseA _) := by
      unfold S512Z.Large
      rw [(mem_stab _).1 hy, ← hμy]
      exact hlarge
    exact (S512Z.large_smul h y _ _).1 h1
  have hcentO : ∀ μ ∈ S5.lam h (2 ^ k) a α' γ, Xq M = Uq M T L ⊔ Zq M L →
      ZM _ μ ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
        stabCenter _ (baseA (puAmalgam h.le)) := by
    intro μ hμ' hXU
    have hZc := S5Q2.UC.zq_le_centralizer_of_relIndex_eq h hd hc hq1
    have hlg : S512Z.Large h k (baseA _) γ :=
      (S512Z.large_symm hZc h54 h hmin hb hd hXU hβγ hl).2 hlgγ
    exact S5C56.zm_inf_le_stabCenter_of_mem_lam h hd
      (fun l'' hl'' => S512Z.zz56_of_large hZc h hd hXU hβγ hl'' hlg) ⟨l, hl⟩ hq1 hμ'
  refine ⟨hwst, hneO, hcent μ₁ hμ, hR₂O, hcentO μ₁ hμlam, fun hXU => ?_⟩
  have e := zm_inf_zm_inf_zm_smul h w (w⁻¹ • μ₁) (baseA (puAmalgam h.le)) γ
  rw [smul_inv_smul, (mem_stab _).1 hwst] at e
  have e' := S510.stabCenter_smul w (baseA (puAmalgam h.le))
  rw [(mem_stab _).1 hwst] at e'
  rw [e, e']
  exact Subgroup.map_mono (hcentO (w⁻¹ • μ₁) hνlam hXU)

theorem false_of_lamSel (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (hZ : S5Q2.Q2EvenZ) (hcore : S512T.Core)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hTB : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex (Qv _ (baseB (puAmalgam h.le))))
    {c₁ c₂ m : Vtx (puAmalgam h.le)}
    (hc₁ : IsCritical _ (baseA (puAmalgam h.le)) c₁)
    (hβ₁ : geo _ (baseA (puAmalgam h.le)) c₁ 1 = baseB _)
    (hc₂ : IsCritical _ (baseA (puAmalgam h.le)) c₂)
    (hβ₂ : geo _ (baseA (puAmalgam h.le)) c₂ 1 = baseB _)
    (hmid : geo _ (baseA (puAmalgam h.le)) c₂ 2 = geo _ (baseA (puAmalgam h.le)) c₁ 2)
    (hq₁ : (Qv _ c₁).relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (hq₂ : (Qv _ c₂).relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (hne : S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (ZM _ c₁ : Set (puAmalgam h.le).Universal) ≠
      S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (ZM _ c₂ : Set (puAmalgam h.le).Universal))
    (hR₁ : critR _ (baseA (puAmalgam h.le)) c₁ ≤
      stabCenter _ (geo _ (baseA (puAmalgam h.le)) c₁ 2))
    (hR₂ : critR _ (baseA (puAmalgam h.le)) c₂ ≤
      stabCenter _ (geo _ (baseA (puAmalgam h.le)) c₁ 2))
    (hcent₁ : Xq M = Uq M T L ⊔ Zq M L →
      ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) c₁ 2) ⊓ ZM _ c₁ ≤
        stabCenter _ (geo _ (baseA (puAmalgam h.le)) c₁ 2))
    (hcent₂ : Xq M = Uq M T L ⊔ Zq M L →
      ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) c₁ 2) ⊓ ZM _ c₂ ≤
        stabCenter _ (geo _ (baseA (puAmalgam h.le)) c₁ 2))
    (hlarge : S512Z.Large h k (baseA _) (geo _ (baseA (puAmalgam h.le)) c₁ 2))
    {y₁ y₂ : (puAmalgam h.le).Universal}
    (hy₁ : y₁ ∈ stab _ (geo _ (baseA (puAmalgam h.le)) c₁ 2))
    (hy₁e : y₁ • baseA (puAmalgam h.le) = c₁)
    (hy₂ : y₂ ∈ stab _ (geo _ (baseA (puAmalgam h.le)) c₁ 2))
    (hy₂e : y₂ • baseA (puAmalgam h.le) = c₂)
    (hmS : m ∈ S5B.lamSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) c₁
      (geo _ (baseA (puAmalgam h.le)) c₁ 2))
    (hcm : IsCritical _ m (geo _ (baseA (puAmalgam h.le)) c₁ 2)) :
    False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) c₁ = 4 := hc₁.2.1.trans hb4
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) c₁ 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := c₁) (i := 1) (by omega)
    rwa [hβ₁] at this
  have hδM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) c₁ 2) := isMVtx_geo_two _ hyp hb0 hc₁
  have hJT := jOff_eq_qv_of_le_qLine h54 h hmin hb hd hl hTl
  have hCase : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) c₁ 2) l :=
    ⟨(S512T.jOff_eq_qv_of_point h hJT hδM hβδ.symm).trans hJT.symm, hl,
      hTl.trans (Subgroup.map_mono (Subgroup.comap_mono (MSP.fixer_le_stab l))),
      hJT ▸ hTl⟩
  obtain ⟨g', x', hg', hx', hcase, hm⟩ := hmS
  obtain ⟨l', hl', hc56, hopp⟩ : ∃ l', S5.Case56 h (2 ^ k) a
      (geo _ (baseA (puAmalgam h.le)) c₁ 2) l' ∧ S5.Concl56 h (2 ^ k) a c₁ l' g' x' ∧
        S5.Opp56 h (2 ^ k) a l' g' x' := by
    rcases hcase with ⟨hno, -⟩ | hyes
    · exact absurd hCase (hno l)
    · exact hyes
  have hR4 : ⁅ZM (puAmalgam h.le) m, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) c₁ 2)⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le)) :=
    S512R.cent56F_holds_e h32 h52 hZ G M T L h hmin hb k F _ _ a hd c₁ hc₁ hβ₁ l' hl' g' hg' x'
      hx' hc56 hopp m hm
  have hqm : (Qv _ (geo _ (baseA (puAmalgam h.le)) c₁ 2)).relIndex (ZM _ m) = 2 ^ k := by
    refine le_antisymm ?_ (S512T.le_relIndex_qv_zm h hb4 hd hcm)
    by_contra hbad
    push Not at hbad
    have hmlam : m ∈ S5.lam h (2 ^ k) a c₁ (geo _ (baseA (puAmalgam h.le)) c₁ 2) :=
      ⟨g', x', hg', hx', Or.inr ⟨l', hl', hc56⟩, hm⟩
    exact hcore G M T L h hmin hb4 k F _ _ a hd c₁ hc₁ hβ₁ l' hl' m
      (S5B.exists_mem_stab_of_mem_lam hmlam) hcm hbad hR4
  exact false_of_frame h14 hSQ hT h32 hX2 h52 h54 h hmin hb4 hd hl hTl hTB hc₁ hβ₁ hc₂ hβ₂ hmid
    hq₁ hq₂ hne hR₁ hR₂ hcent₁ hcent₂ hlarge hy₁ hy₁e hy₂ hy₂e hg' hx' hl' hc56 hopp hm hcm hqm
    hR4

theorem three56ResL_of_core (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (hZ : S5Q2.Q2EvenZ) (hone : S512Z.OneCF) (hcore : S512T.Core) : S512R.Three56ResL := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS hq1 hq l hl g hg x hx hc56 w hwcase
    hnw hlarge hcrit hqw hTl hTρ
  exfalso
  obtain ⟨hwst, hneO, hR₁O, hR₂O, hcentO₁, hcentO₂⟩ := three56ResL_base h32 h52 h54 hZ hone h
    hmin hb4 hd hchS hq1 hl hg hx hc56 hwcase hnw hlarge hcrit
  have hch := S5B.isChain512Sel_subset hchS
  obtain ⟨-, -, hcμ, ⟨y, hy, hμy⟩, hdμ, hmid, -⟩ := S512T.chain_geo h hb4 hch
  obtain ⟨-, ⟨c, hc1, hc2, hc3⟩, hcμ₂⟩ := hchS.2.2.2.2.2.2
  rw [hmid] at hc3 hcμ₂
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγ
  obtain ⟨-, -, -, -, hμρ, hρα, -, -, -, hαγ, -, -⟩ := S512T.pair_facts h hb4 hcμ
  rw [hmid] at hρα hαγ
  have hdwγ : (puAmalgam h.le).treeGraph.dist (baseA _) (w • γ) = 2 := by
    have := dist_smul _ w (baseA (puAmalgam h.le)) γ
    rw [(mem_stab _).1 hwst] at this
    rw [this, hαγ]
  have hmidw : geo _ μ₁ (w • γ) 2 = baseA _ := by
    have h1 : (puAmalgam h.le).treeGraph.dist μ₁ (baseA _) = 2 := by
      rw [SimpleGraph.dist_comm]; exact hdμ
    have h2 : (puAmalgam h.le).treeGraph.dist μ₁ (w • γ) = 4 := hcrit.2.1.trans hb4
    exact (eq_geo_of_dist _ h1 (by rw [h1, hdwγ, h2])).symm
  have hρw : geo _ μ₁ (w • γ) 1 = geo _ μ₁ γ 1 :=
    (S512T.eq_geo_one_of_adj h hb4 hcrit hmidw hρα.symm hμρ.symm).symm
  have hgf : geo _ (baseA (puAmalgam h.le)) (c • γ) 2 = c • baseA (puAmalgam h.le) := by
    have e := geo_smul _ c μ₁ γ 2
    rwa [hc1, hmid] at e
  have hgf₂ : geo _ (baseA (puAmalgam h.le)) (c • w • γ) 2 = c • baseA (puAmalgam h.le) := by
    have e := geo_smul _ c μ₁ (w • γ) 2
    rwa [hc1, hmidw] at e
  have hc₁ : IsCritical _ (baseA (puAmalgam h.le)) (c • γ) := by
    have e := (isCritical_smul _ c μ₁ γ).2 hcμ
    rwa [hc1] at e
  have hβ₁ : geo _ (baseA (puAmalgam h.le)) (c • γ) 1 = baseB _ := by
    have e := geo_smul _ c μ₁ γ 1
    rwa [hc1, hc2] at e
  have hc₂ : IsCritical _ (baseA (puAmalgam h.le)) (c • w • γ) := by
    have e := (isCritical_smul _ c μ₁ (w • γ)).2 hcrit
    rwa [hc1] at e
  have hβ₂ : geo _ (baseA (puAmalgam h.le)) (c • w • γ) 1 = baseB _ := by
    have e := geo_smul _ c μ₁ (w • γ) 1
    rwa [hc1, hρw, hc2] at e
  have hq₁ : (Qv _ (c • γ)).relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k := by
    have e := S5B.relIndex_qv_zm_smul c γ μ₁
    rw [hc1] at e
    rw [e]
    exact hq
  have hq₂ : (Qv _ (c • w • γ)).relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k := by
    have e := S5B.relIndex_qv_zm_smul c (w • γ) μ₁
    rw [hc1] at e
    rw [e]
    exact hqw
  have hTB : (2 ^ k) ^ 2 <
      (Qv _ (baseA (puAmalgam h.le))).relIndex (Qv _ (baseB (puAmalgam h.le))) := by
    have e : (Qv _ (c • μ₁)).relIndex (Qv _ (c • geo _ μ₁ γ 1)) =
        (Qv _ μ₁).relIndex (Qv _ (geo _ μ₁ γ 1)) := by
      rw [qv_smul, qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]
    rw [hc1, hc2] at e
    rw [e]
    exact hTρ
  have hne : S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (ZM _ (c • γ) : Set (puAmalgam h.le).Universal) ≠
      S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (ZM _ (c • w • γ) : Set (puAmalgam h.le).Universal) := by
    intro heq
    apply hneO
    have e1 := uSub_inf_centralizer_smul h c μ₁ γ
    have e2 := uSub_inf_centralizer_smul h c μ₁ (w • γ)
    rw [hc1] at e1 e2
    exact Subgroup.map_injective (MulAut.conj c).injective (e1.symm.trans (heq.trans e2))
  have hR₁ : critR _ (baseA (puAmalgam h.le)) (c • γ) ≤
      stabCenter _ (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    have e := commutator_zm_zm_smul h c μ₁ γ
    rw [hc1] at e
    rw [hgf, critR, e, S510.stabCenter_smul]
    exact Subgroup.map_mono hR₁O
  have hR₂ : critR _ (baseA (puAmalgam h.le)) (c • w • γ) ≤
      stabCenter _ (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    have e := commutator_zm_zm_smul h c μ₁ (w • γ)
    rw [hc1] at e
    rw [hgf, critR, e, S510.stabCenter_smul]
    exact Subgroup.map_mono hR₂O
  have hcent₁ : Xq M = Uq M T L ⊔ Zq M L →
      ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) ⊓
        ZM _ (c • γ) ≤ stabCenter _ (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    intro hXU
    have e := zm_inf_zm_inf_zm_smul h c μ₁ (baseA (puAmalgam h.le)) γ
    rw [hc1] at e
    rw [hgf, e, S510.stabCenter_smul]
    exact Subgroup.map_mono (hcentO₁ hXU)
  have hcent₂ : Xq M = Uq M T L ⊔ Zq M L →
      ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) ⊓
        ZM _ (c • w • γ) ≤ stabCenter _ (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    intro hXU
    have e := zm_inf_zm_inf_zm_smul h c μ₁ (baseA (puAmalgam h.le)) (w • γ)
    rw [hc1] at e
    rw [hgf, e, S510.stabCenter_smul]
    exact Subgroup.map_mono (hcentO₂ hXU)
  have hlargef : S512Z.Large h k (baseA _) (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    have e := (S512Z.large_smul (k := k) h c μ₁ (baseA _)).2 hlarge
    rw [hc1] at e
    rw [hgf]
    exact e
  have hcμ₁ : c⁻¹ • baseA (puAmalgam h.le) = μ₁ := by rw [← hc1, inv_smul_smul]
  have hyγ : y⁻¹ • μ₁ = γ := by rw [hμy, inv_smul_smul]
  have hy₁ : c * y⁻¹ * c⁻¹ ∈ stab _ (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    rw [hgf, mem_stab, mul_smul, mul_smul, inv_smul_smul, (mem_stab _).1 (inv_mem hy)]
  have hy₁e : (c * y⁻¹ * c⁻¹) • baseA (puAmalgam h.le) = c • γ := by
    rw [mul_smul, mul_smul, hcμ₁, hyγ]
  have hy₂ : c * w * y⁻¹ * c⁻¹ ∈ stab _ (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    rw [hgf, mem_stab, mul_smul, mul_smul, mul_smul, inv_smul_smul, (mem_stab _).1 (inv_mem hy),
      (mem_stab _).1 hwst]
  have hy₂e : (c * w * y⁻¹ * c⁻¹) • baseA (puAmalgam h.le) = c • w • γ := by
    rw [mul_smul, mul_smul, mul_smul, hcμ₁, hyγ]
  have hmS : c • μ₂ ∈ S5B.lamSel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) (c • γ)
      (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    rw [hgf]
    exact hc3
  have hcm : IsCritical _ (c • μ₂) (geo _ (baseA (puAmalgam h.le)) (c • γ) 2) := by
    rw [hgf]
    exact (isCritical_smul _ c μ₂ (baseA _)).2 hcμ₂
  exact false_of_lamSel h14 hSQ hT h32 hX2 h52 h54 hZ hcore h hmin hb4 hd hl.2.1 hTl hTB hc₁ hβ₁
    hc₂ hβ₂ (hgf₂.trans hgf.symm) hq₁ hq₂ hne hR₁ hR₂ hcent₁ hcent₂ hlargef hy₁ hy₁e hy₂ hy₂e hmS
    hcm

end S512J

end CFSG.Quasithin.MS93
