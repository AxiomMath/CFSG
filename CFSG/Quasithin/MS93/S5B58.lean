module

public import CFSG.Quasithin.MS93.S5B58A
public import CFSG.Quasithin.MS93.S5NQD

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S5B

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Hyp

theorem inf_eq_of_relIndex_le {Γ : Type*} [Group Γ] {U B C : Subgroup Γ} [Finite U]
    (hBC : U ⊓ B ≤ C) (hle : B.relIndex U ≤ C.relIndex U) : U ⊓ B = U ⊓ C := by
  have h1 : B ⊓ U ≤ C ⊓ U := fun x hx => ⟨hBC ⟨hx.2, hx.1⟩, hx.2⟩
  have h2 := Subgroup.relIndex_mul_relIndex (B ⊓ U) (C ⊓ U) U h1 inf_le_right
  rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at h2
  have : Finite ↥(C ⊓ U) :=
    Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have hpos : 0 < C.relIndex U :=
    Nat.pos_of_ne_zero (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have hne : (B ⊓ U).relIndex (C ⊓ U) ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hx1 : (B ⊓ U).relIndex (C ⊓ U) ≤ 1 :=
    Nat.le_of_mul_le_mul_right (by rw [h2, one_mul]; exact hle) hpos
  have h4 := Subgroup.relIndex_eq_one.1 (show (B ⊓ U).relIndex (C ⊓ U) = 1 by omega)
  exact le_antisymm (le_inf inf_le_left hBC) fun x hx => ⟨hx.1, (h4 ⟨hx.2, hx.1⟩).1⟩

theorem uSub_inf_bSub_le_centralizer (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ε ε' ρ ν : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγε : (puAmalgam h.le).treeGraph.Adj γ ε) (hγε' : (puAmalgam h.le).treeGraph.Adj γ ε')
    (hερ : (puAmalgam h.le).treeGraph.Adj ε ρ) (hν : IsMVtx _ ν)
    (hγν : (puAmalgam h.le).treeGraph.dist γ ν < critDist (puAmalgam h.le))
    (hε'ν : (puAmalgam h.le).treeGraph.dist ε' ν + 2 ≤ critDist (puAmalgam h.le))
    (hνε : (puAmalgam h.le).treeGraph.dist ν ε < critDist (puAmalgam h.le))
    (hνρ : ¬ ZM _ ν ≤ Qv _ ρ) :
    S5.uSub h.le L ρ ⊓ S5.bSub h.le L γ ≤
        Subgroup.centralizer (ZM _ ν : Set (puAmalgam h.le).Universal) ∧
      ZM _ ν ≤ stab _ ρ ∧ IsPGroup 2 (ZM _ ν) ∧
      2 ^ k ≤ (Subgroup.centralizer (ZM _ ν : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L ρ) ∧
      (Subgroup.centralizer (ZM _ ν : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L ρ) ≤ (S5.bSub h.le L γ).relIndex (S5.uSub h.le L ρ) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hεM : ¬ IsMVtx _ ε := (isMVtx_iff_of_adj _ hγε).1 hγ
  have hρ : IsMVtx _ ρ := by
    have := isMVtx_iff_of_adj _ hερ
    tauto
  have hQν : ZM _ ν ≤ Qv _ ε := zm_le_qv_of_dist_lt _ hν hνε
  have hst : ZM _ ν ≤ stab _ ρ := hQν.trans (qv_le_stab_of_adj _ hερ)
  have h2 : IsPGroup 2 (ZM _ ν) := (isPGroup_qv _ hyp hεM).to_le hQν
  have hBC : S5.uSub h.le L ρ ⊓ S5.bSub h.le L γ ≤
      Subgroup.centralizer (ZM _ ν : Set (puAmalgam h.le).Universal) :=
    (uSub_inf_bSub_le_qv h hb hγ hγε hγε' hερ hγν hε'ν).trans
      ((qv_le_centralizer_xm _ ν).trans (Subgroup.centralizer_le (zm_le_xm _ hyp hb0 hν)))
  have hfin : Finite ↥(S5.uSub h.le L ρ) := finite_of_le_qv h hρ
    ((uSub_le_zm h.le ρ).trans (zm_le_qv_self _ hρ hb0))
  refine ⟨hBC, hst, h2, le_relIndex_centralizer h hd hρ hst h2 hνρ, ?_⟩
  rw [← Subgroup.inf_relIndex_right (S5.bSub h.le L γ),
    ← Subgroup.inf_relIndex_right (Subgroup.centralizer _)]
  refine Subgroup.relIndex_le_of_le_left (fun x hx => ⟨hBC ⟨hx.2, hx.1⟩, hx.2⟩) ?_
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem uSub_inf_bSub_eq_centralizer (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ ε ε' ρ ν : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγε : (puAmalgam h.le).treeGraph.Adj γ ε) (hγε' : (puAmalgam h.le).treeGraph.Adj γ ε')
    (hερ : (puAmalgam h.le).treeGraph.Adj ε ρ) (hν : IsMVtx _ ν)
    (hγν : (puAmalgam h.le).treeGraph.dist γ ν < critDist (puAmalgam h.le))
    (hε'ν : (puAmalgam h.le).treeGraph.dist ε' ν + 2 ≤ critDist (puAmalgam h.le))
    (hνε : (puAmalgam h.le).treeGraph.dist ν ε < critDist (puAmalgam h.le))
    (hνρ : ¬ ZM _ ν ≤ Qv _ ρ)
    (hP : (S5.bSub h.le L γ).relIndex (S5.uSub h.le L ρ) ≤ 2 ^ k) :
    S5.uSub h.le L ρ ⊓ S5.bSub h.le L γ =
        S5.uSub h.le L ρ ⊓ Subgroup.centralizer (ZM _ ν : Set (puAmalgam h.le).Universal) ∧
      (Subgroup.centralizer (ZM _ ν : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L ρ) ≤ 2 ^ k ∧
      ZM _ ν ≤ stab _ ρ ∧ IsPGroup 2 (ZM _ ν) := by
  obtain ⟨hBC, hst, h2, hLB, hle⟩ :=
    uSub_inf_bSub_le_centralizer h hb hd hγ hγε hγε' hερ hν hγν hε'ν hνε hνρ
  have hρ : IsMVtx _ ρ := by
    have h1 := isMVtx_iff_of_adj _ hγε
    have h2 := isMVtx_iff_of_adj _ hερ
    tauto
  have hfin : Finite ↥(S5.uSub h.le L ρ) := finite_of_le_qv h hρ
    ((uSub_le_zm h.le ρ).trans (zm_le_qv_self _ hρ h.critDist_pos))
  exact ⟨inf_eq_of_relIndex_le hBC (hP.trans hLB), hle.trans hP, hst, h2⟩

end Hyp

section Mu

theorem s58_mu_sel (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h55 : S55)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h56S : Prod56 h k a S) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hδB : ¬ S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _))
    (hδ : ∀ μ ∈ lamSel h (2 ^ k) a S α' δ,
      ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2)) :
    ∃ μ, IsMVtx _ μ ∧ (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 ∧
      ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) ∧
      Nat.card ↥⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k ∧
      (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k ∧
      Xq M = Uq M T L ⊔ Zq M L ∧
      ⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
        critR _ (baseA (puAmalgam h.le)) α' ⊔ stabCenter _ α' := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have h32' := (h32 G M T L h).2.1
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hδα : δ ≠ baseA _ := by
    rintro rfl
    apply hδB
    intro u hu
    refine Subgroup.subset_closure ⟨zm_le_vv_of_dist hα (by simp) (uSub_le_zm h.le _ hu),
      fun y hy => ?_⟩
    exact commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans
      (stab_le_normalizer_zm _ _)) (Subgroup.commutator_mem_commutator (uSub_le_zm h.le _ hu) hy)
  have hBy : ∀ y ∈ stab _ (baseA (puAmalgam h.le)),
      ¬ S5.uSub h.le L (y⁻¹ • δ) ≤ S5.bSub h.le L (baseA _) := by
    intro y hy hle
    apply hδB
    rw [← Subgroup.relIndex_eq_one, ← relIndex_bSub_uSub_smul h (inv_mem hy) δ]
    exact Subgroup.relIndex_eq_one.2 hle
  by_cases hcase : ∃ l, S5.Case56 h (2 ^ k) a δ l
  ·
    obtain ⟨l, hJδ, hline, hTl, hJl⟩ := hcase
    obtain ⟨g, hg, x, hx, hconc, hS⟩ := h56S α' hc hαβ l hline hTl hJl
    have hmem₁ : g⁻¹ • δ ∈ lamSel h (2 ^ k) a S α' δ :=
      ⟨g, x, hg, hx, Or.inr ⟨l, ⟨hJδ, hline, hTl, hJl⟩, hconc, hS⟩, Or.inl rfl⟩
    have hmem₂ : x⁻¹ • g⁻¹ • δ ∈ lamSel h (2 ^ k) a S α' δ :=
      ⟨g, x, hg, hx, Or.inr ⟨l, ⟨hJδ, hline, hTl, hJl⟩, hconc, hS⟩, Or.inr rfl⟩
    have hZ₁ := hδ _ hmem₁
    have hZ₂ := hδ _ hmem₂
    obtain ⟨-, -, hc6, -⟩ := hconc
    have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
    obtain ⟨hαβ₁, hβ₁α₁, hα₁, hdα₁⟩ := s57_vert h hβδ hδα hg
    have hα₂eq : x⁻¹ • g⁻¹ • δ = (g * x)⁻¹ • δ := by rw [mul_inv_rev, mul_smul]
    obtain ⟨-, -, hα₂, hdα₂⟩ := s57_vert h hβδ hδα (mul_mem hg hxst)
    rw [← hα₂eq] at hα₂ hdα₂
    by_cases hn₁ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
        ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)
    · by_cases hn₂ : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
          ((ZM _ (x⁻¹ • g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)
      ·
        exfalso
        have hxX : (XM _ (baseA (puAmalgam h.le))).map (MulAut.conj x).toMonoidHom =
            XM _ (baseA (puAmalgam h.le)) := by
          rw [← xm_smul, (mem_stab _).1 hxst]
        have h1 : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ≤
            Qv _ (g⁻¹ • baseB (puAmalgam h.le)) := by
          rw [rconj_eq_map, qv_smul]
          exact Subgroup.map_mono (jOff_le_qv h.le L _ _ _)
        have hJn : S5.rconj g (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) ≤
            Subgroup.normalizer ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) :
              Subgroup _) : Set _) :=
          le_normalizer_sup (h1.trans ((qv_le_stab_of_adj _ hβ₁α₁).trans
            (stab_le_normalizer_zm _ _))) (h1.trans ((qv_le_stab_of_isMVtx _ hyp
              (isMVtx_baseA _) hαβ₁).trans (stab_le_normalizer_xm _ _)))
        have hZn₂ : S5.rconj x⁻¹ (S5.zHat _ (baseA (puAmalgam h.le)) α') ≤
            Subgroup.normalizer ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) :
              Subgroup _) : Set _) := by
          have hW : ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) =
              (ZM _ (x⁻¹ • g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le))).map
                (MulAut.conj x).toMonoidHom := by
            rw [Subgroup.map_sup, ← zm_smul, smul_inv_smul, hxX]
          rw [rconj_eq_map, inv_inv, hW, normalizer_map_conj, map_conj_le_map_conj_iff]
          exact hn₂
        have hall := hc6.trans (sup_le (sup_le hJn hn₁) hZn₂)
        have hZB := le_bSub_of_xm h hb h32' (isMVtx_baseA _) hdα₁ (zm_le_xm _ hyp hb0 hα₁)
          (zm_le_vv_of_dist hα₁ hdα₁.le) hall
        exact hBy g hg ((uSub_le_zm h.le _).trans hZB)
      · obtain ⟨hidx, hXU, hcard, hR⟩ :=
          s57_s33 h32 hX2 h52 h hmin hb hd hc hα₂ hdα₂ hZ₂ hn₂
        exact ⟨_, hα₂, hdα₂, hZ₂, hcard, hidx, hXU, hR⟩
    · obtain ⟨hidx, hXU, hcard, hR⟩ :=
        s57_s33 h32 hX2 h52 h hmin hb hd hc hα₁ hdα₁ hZ₁ hn₁
      exact ⟨_, hα₁, hdα₁, hZ₁, hcard, hidx, hXU, hR⟩
  ·
    push Not at hcase
    have hne : S5.jOff h.le L (2 ^ k) δ (baseB _) ≠
        S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ∨
        ∀ l : Submodule F (MSP.V4 F), MSP.IsLine l →
          Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) →
          ¬ S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤
            S5.vPre h.le a (MSP.qLine l) := by
      by_cases hJ : S5.jOff h.le L (2 ^ k) δ (baseB _) =
          S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)
      · exact Or.inr fun l hl hTl hJl => hcase l ⟨hJ, hl, hTl, hJl⟩
      · exact Or.inl hJ
    obtain ⟨g, hg, x, hx, hconc⟩ := h55 G M T L h hmin hb k F _ _ a hd α' hc hαβ δ hβδ hne
    have hmem₁ : g⁻¹ • δ ∈ lamSel h (2 ^ k) a S α' δ :=
      ⟨g, x, hg, hx, Or.inl ⟨hcase, hconc⟩, Or.inl rfl⟩
    have hZ₁ := hδ _ hmem₁
    obtain ⟨hαβ₁, hβ₁α₁, hα₁, hdα₁⟩ := s57_vert h hβδ hδα hg
    have hT₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
      qv_le_stab_of_isMVtx _ hyp hα hαβ₁
    have hT₁α₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (g⁻¹ • δ) :=
      qv_le_stab_of_adj _ hβ₁α₁
    have hn : ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
        ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
      intro hZ
      apply hBy g hg
      have hTn : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ Subgroup.normalizer
          ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) :=
        le_normalizer_sup (hT₁α₁.trans (stab_le_normalizer_zm _ _))
          (hT₁.trans (stab_le_normalizer_xm _ _))
      have hall : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
          ((ZM _ (g⁻¹ • δ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
        rw [← hconc.1.1]
        exact sup_le hTn hZ
      have := le_bSub_of_xm h hb h32' hα hdα₁ (zm_le_xm _ hyp hb0 hα₁)
        (zm_le_vv_of_dist hα₁ hdα₁.le) ((puTrans_le_stab h.le L _).trans hall)
      exact (uSub_le_zm h.le _).trans this
    obtain ⟨hidx, hXU, hcard, hR⟩ :=
      s57_s33 h32 hX2 h52 h hmin hb hd hc hα₁ hdα₁ hZ₁ hn
    exact ⟨_, hα₁, hdα₁, hZ₁, hcard, hidx, hXU, hR⟩

theorem s58_zu (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {μ : Vtx (puAmalgam h.le)} (hZμ : ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hcard : Nat.card ↥⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k)
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) :
    ∃ z ∈ ZM _ μ, ∃ u ∈ S5.uSub h.le L α', u ∈ Qv _ (baseA (puAmalgam h.le)) ∧ ⁅z, u⁆ ≠ 1 := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hcr := ms22_iii _ hyp hb0 hC hc
  have hd' : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) :=
    hcr.2.1
  have hAZ : critA _ (baseA (puAmalgam h.le)) α' ≤ ZM _ α' := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by have := hd.1; omega
      have hidx' : (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') ≤ 2 :=
        S5Q2.relIndex_qv_zm_le_two h hd hc (by rw [hidx]; norm_num)
      refine le_trans ?_ (S5Q2.xm_inf_centralizer_zm_le_zm h hd hXU hcr hidx')
      rintro x ⟨hxX, hxQ⟩
      refine ⟨hxX, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1
        (zm_le_centralizer_qv _ hyp (isMVtx_baseA _) hw) x hxQ).symm
    · obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hα'
      have hXZ : XM _ α' = ZM _ α' := by
        rw [← hg, xm_smul, zm_smul,
          xm_eq_zm h hXU (S5Q2.zq_le_centralizer_of_two_le h hd hk)]
      exact inf_le_left.trans hXZ.le
  obtain ⟨z, hz, x, hx, hzx⟩ : ∃ z ∈ ZM _ μ, ∃ x ∈ critA _ (baseA (puAmalgam h.le)) α',
      ⁅z, x⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply commutator_ne_bot_of_card hd hcard
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro z hz x hx
    rw [hcon z hz x hx]
    exact one_mem _
  set a₁ := geo _ α' (baseA (puAmalgam h.le)) 1 with ha₁def
  set a₂ := geo _ α' (baseA (puAmalgam h.le)) 2 with ha₂def
  have h1 : (puAmalgam h.le).treeGraph.Adj α' a₁ := adj_geo_one _ (by omega)
  have h12 : (puAmalgam h.le).treeGraph.Adj a₁ a₂ := adj_geo _ (i := 1) (by omega)
  have ha₂ : IsMVtx _ a₂ := isMVtx_geo_two _ hyp hb0 hcr
  have hda₂ : (puAmalgam h.le).treeGraph.dist a₂ (baseA _) < critDist (puAmalgam h.le) := by
    rw [ha₂def, dist_geo_right _ (by omega)]
    omega
  have hxZ : x ∈ ZH _ a₁ ⊔ S5.uSub h.le L α' := by
    rw [← zm_eq_zh_sup_uSub h hα' h1]
    exact hAZ hx
  have hn : ZH _ a₁ ≤ Subgroup.normalizer (S5.uSub h.le L α' : Set _) :=
    ((zh_le_qv _ a₁).trans (qv_le_stab_of_adj _ h1.symm)).trans
      (le_normalizer_commutator (stab_le_normalizer_zm _ _) (stab_le_normalizer_puTrans h.le hLn _))
  have hx' : x ∈ ((ZH _ a₁ : Set (puAmalgam h.le).Universal) *
      (S5.uSub h.le L α' : Set (puAmalgam h.le).Universal)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn]
    exact hxZ
  obtain ⟨c, hc', u, hu, rfl⟩ := hx'
  have hcZ : c ∈ ZM _ a₂ := zh_le_zm _ h12.symm hc'
  have hcQ : c ∈ Qv _ (baseA (puAmalgam h.le)) := zm_le_qv_of_dist_lt _ ha₂ hda₂ hcZ
  have hzc : c * z = z * c := Subgroup.mem_centralizer_iff.1
    (qv_le_centralizer_xm _ a₂ (hZμ hz)) c (zm_le_xm _ hyp hb0 ha₂ hcZ)
  refine ⟨z, hz, u, hu, ?_, ?_⟩
  · have := mul_mem (inv_mem hcQ) hx.2
    simpa using this
  · intro hzu
    apply hzx
    calc ⁅z, c * u⁆ = z * c * u * z⁻¹ * u⁻¹ * c⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = c * z * u * z⁻¹ * u⁻¹ * c⁻¹ := by rw [← hzc]
      _ = c * ⁅z, u⁆ * c⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = 1 := by rw [hzu]; group

end Mu

section Contra

theorem critR_le_commutator (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    critR _ (baseA (puAmalgam h.le)) α' ≤
      ⁅ZM _ (baseA (puAmalgam h.le)), S5.uSub h.le L α'⁆ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hcr := ms22_iii _ hyp hb0 hC hc
  have hd' : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) :=
    hcr.2.1
  have h1 : (puAmalgam h.le).treeGraph.Adj α' (geo _ α' (baseA (puAmalgam h.le)) 1) :=
    adj_geo_one _ (by omega)
  have hda₁ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ α' (baseA (puAmalgam h.le)) 1) <
      critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd']
    omega
  have hZαQ : ZM _ (baseA (puAmalgam h.le)) ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) :=
    zm_le_qv_of_dist_lt _ hα hda₁
  obtain ⟨hZ'st, -, -, -, -, -⟩ := crit_facts h hc
  have hUst : stab _ α' ≤ Subgroup.normalizer (S5.uSub h.le L α' : Set _) :=
    le_normalizer_commutator (stab_le_normalizer_zm _ _) (stab_le_normalizer_puTrans h.le hLn _)
  have hZhst : ZH _ (geo _ α' (baseA (puAmalgam h.le)) 1) ≤ stab _ (baseA (puAmalgam h.le)) :=
    (zh_le_zm _ h1).trans hZ'st
  rw [critR, zm_eq_zh_sup_uSub h hα' h1, Subgroup.commutator_comm]
  refine commutator_sup_le_of_le (le_normalizer_commutator
      (hZhst.trans (stab_le_normalizer_zm _ _))
      (((zh_le_qv _ _).trans (qv_le_stab_of_adj _ h1.symm)).trans hUst))
    (le_normalizer_commutator
      (((uSub_le_zm h.le _).trans hZ'st).trans (stab_le_normalizer_zm _ _))
      (((uSub_le_zm h.le _).trans ((zm_le_qv_self _ hα' hb0).trans (qv_le_stab _ _))).trans hUst))
    ?_ ?_
  · have hcen : ZH _ (geo _ α' (baseA (puAmalgam h.le)) 1) ≤
        Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _) :=
      ((PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right).trans
        (Subgroup.centralizer_le hZαQ)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcen]
    exact bot_le
  · rw [Subgroup.commutator_comm]

theorem s58_contra (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    (hP : ∀ γ ε ρ : Vtx (puAmalgam h.le), IsMVtx _ γ → (puAmalgam h.le).treeGraph.Adj γ ε →
      (puAmalgam h.le).treeGraph.Adj ε ρ →
        (S5.bSub h.le L γ).relIndex (S5.uSub h.le L ρ) ≤ 2 ^ k)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2)
    (hZμ : ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))
    (hR : ⁅ZM _ μ, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
      critR _ (baseA (puAmalgam h.le)) α' ⊔ stabCenter _ α')
    {z u : (puAmalgam h.le).Universal} (hz : z ∈ ZM _ μ) (hu : u ∈ S5.uSub h.le L α')
    (huQ : u ∈ Qv _ (baseA (puAmalgam h.le))) (hzu : ⁅z, u⁆ ≠ 1) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hcr := ms22_iii _ hyp hb0 hC hc
  have hd' : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) :=
    hcr.2.1
  have hb4 : 4 ≤ critDist (puAmalgam h.le) := by
    obtain ⟨m, hm⟩ := ms21_v _ hyp
    omega
  set a₁ := geo _ α' (baseA (puAmalgam h.le)) 1 with ha₁def
  set a₂ := geo _ α' (baseA (puAmalgam h.le)) 2 with ha₂def
  set a₃ := geo _ α' (baseA (puAmalgam h.le)) 3 with ha₃def
  set a₄ := geo _ α' (baseA (puAmalgam h.le)) 4 with ha₄def
  have h1 : (puAmalgam h.le).treeGraph.Adj α' a₁ := adj_geo_one _ (by omega)
  have h12 : (puAmalgam h.le).treeGraph.Adj a₁ a₂ := adj_geo _ (i := 1) (by omega)
  have h23 : (puAmalgam h.le).treeGraph.Adj a₂ a₃ := adj_geo _ (i := 2) (by omega)
  have h34 : (puAmalgam h.le).treeGraph.Adj a₃ a₄ := adj_geo _ (i := 3) (by omega)
  have ha₂ : IsMVtx _ a₂ := (isMVtx_geo _ (by omega)).2 (iff_of_true hα' even_two)
  have ha₄ : IsMVtx _ a₄ := (isMVtx_geo _ (by omega)).2 (iff_of_true hα' (by decide))
  have hda₁ : (puAmalgam h.le).treeGraph.dist a₁ (baseA _) = critDist (puAmalgam h.le) - 1 := by
    rw [ha₁def, dist_geo_right _ (by omega), hd']
  have hda₂ : (puAmalgam h.le).treeGraph.dist a₂ (baseA _) = critDist (puAmalgam h.le) - 2 := by
    rw [ha₂def, dist_geo_right _ (by omega), hd']
  have hda₃ : (puAmalgam h.le).treeGraph.dist a₃ (baseA _) = critDist (puAmalgam h.le) - 3 := by
    rw [ha₃def, dist_geo_right _ (by omega), hd']
  have hda₄ : (puAmalgam h.le).treeGraph.dist a₄ (baseA _) = critDist (puAmalgam h.le) - 4 := by
    rw [ha₄def, dist_geo_right _ (by omega), hd']
  obtain ⟨hW₀, -⟩ := uSub_inf_bSub_eq_centralizer h hb hd ha₂ h12.symm h23 h1.symm hα
    (by omega) (by omega) (by rw [SimpleGraph.dist_comm]; omega) hc.2.2
    (hP _ _ _ ha₂ h12.symm h1.symm)
  have huB : u ∈ S5.bSub h.le L a₂ := by
    have hmem : u ∈ S5.uSub h.le L α' ⊓
        Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _) :=
      ⟨hu, Subgroup.centralizer_le (zm_le_xm _ hyp hb0 hα) (qv_le_centralizer_xm _ _ huQ)⟩
    rw [← hW₀] at hmem
    exact hmem.2
  obtain ⟨s, hs, hsa⟩ := exists_puTrans_smul h ha₂ h12.symm h23
  have hsa₂ : s • a₂ = a₂ := (mem_stab _).1 (puTrans_le_stab h.le L _ hs)
  have hσ3 : (puAmalgam h.le).treeGraph.Adj a₃ (s • α') := by
    rw [← hsa]
    exact (adj_smul _ s _ _).2 h1.symm
  have hσ : IsMVtx _ (s • α') := (isMVtx_smul _ s _).2 hα'
  have hus : s * u * s⁻¹ ∈ S5.uSub h.le L (s • α') := by
    rw [uSub_smul h.le hLn]
    exact ⟨u, hu, rfl⟩
  have husB : s * u * s⁻¹ ∈ S5.bSub h.le L a₂ := by
    have e := bSub_smul h.le hLn s a₂
    rw [hsa₂] at e
    rw [e]
    exact ⟨u, huB, rfl⟩
  have hda₂' : (puAmalgam h.le).treeGraph.dist a₂ α' = 2 := by
    rw [SimpleGraph.dist_comm, ha₂def, dist_geo _ (by omega)]
  have huQ₂ : u ∈ Qv _ a₂ :=
    zm_le_qv_of_dist_lt _ hα' (by rw [SimpleGraph.dist_comm, hda₂']; omega) (uSub_le_zm h.le _ hu)
  have hzus_eq : ⁅z, s * u * s⁻¹⁆ = ⁅z, u⁆ := by
    have hcs : ⁅u, s⁆ ∈ ZM _ a₂ := commutator_mem_zm_of_mem_bSub h hb ha₂ huB hs
    have hcX : ⁅u, s⁆ ∈ XM _ a₂ := zm_le_xm _ hyp hb0 ha₂ hcs
    have hzuQ : ⁅z, u⁆ ∈ Qv _ a₂ := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hZμ hz) huQ₂) (inv_mem (hZμ hz))) (inv_mem huQ₂)
    have hzc : ⁅u, s⁆ * z = z * ⁅u, s⁆ := Subgroup.mem_centralizer_iff.1
      (qv_le_centralizer_xm _ a₂ (hZμ hz)) _ hcX
    have hc2 : ⁅u, s⁆ * ⁅z, u⁆ = ⁅z, u⁆ * ⁅u, s⁆ := Subgroup.mem_centralizer_iff.1
      (qv_le_centralizer_xm _ a₂ hzuQ) _ hcX
    set c := ⁅u, s⁆ with hcdef
    have hsu : s * u * s⁻¹ = c⁻¹ * u := by
      rw [hcdef]
      simp only [commutatorElement_def]
      group
    have hzc' : z * c⁻¹ = c⁻¹ * z := by
      calc z * c⁻¹ = c⁻¹ * (c * z) * c⁻¹ := by group
        _ = c⁻¹ * (z * c) * c⁻¹ := by rw [hzc]
        _ = c⁻¹ * z := by group
    rw [hsu]
    calc ⁅z, c⁻¹ * u⁆ = c⁻¹ * ⁅z, u⁆ * c := by
          simp only [commutatorElement_def]
          calc z * (c⁻¹ * u) * z⁻¹ * (c⁻¹ * u)⁻¹ = z * c⁻¹ * u * z⁻¹ * u⁻¹ * c := by group
            _ = c⁻¹ * z * u * z⁻¹ * u⁻¹ * c := by rw [hzc']
            _ = c⁻¹ * (z * u * z⁻¹ * u⁻¹) * c := by group
      _ = ⁅z, u⁆ := by rw [mul_assoc, ← hc2, ← mul_assoc, inv_mul_cancel, one_mul]
  have hzus : ⁅z, s * u * s⁻¹⁆ ≠ 1 := by
    rw [hzus_eq]
    exact hzu
  have hZμσ : ¬ ZM _ μ ≤ Qv _ (s • α') := by
    intro hle
    apply hzus
    have hw : s * u * s⁻¹ ∈ XM _ (s • α') := zm_le_xm _ hyp hb0 hσ (uSub_le_zm h.le _ hus)
    have hcomm := Subgroup.mem_centralizer_iff.1 (qv_le_centralizer_xm _ _ (hle hz)) _ hw
    rw [commutatorElement_def, ← hcomm, mul_inv_cancel_right, mul_inv_cancel]
  have hdμ₃ : (puAmalgam h.le).treeGraph.dist μ a₃ ≤ critDist (puAmalgam h.le) - 1 := by
    have h1 : (puAmalgam h.le).treeGraph.dist μ (baseA _) = 2 := by
      rw [SimpleGraph.dist_comm]
      exact hdμ
    have h2 : (puAmalgam h.le).treeGraph.dist (baseA _) a₃ = critDist (puAmalgam h.le) - 3 := by
      rw [SimpleGraph.dist_comm]
      exact hda₃
    have := dist_triangle _ μ (baseA (puAmalgam h.le)) a₃
    omega
  have hdμ₄ : (puAmalgam h.le).treeGraph.dist a₄ μ ≤ critDist (puAmalgam h.le) - 2 := by
    have := dist_triangle _ a₄ (baseA (puAmalgam h.le)) μ
    rw [hda₄, hdμ] at this
    omega
  have hdσμ : critDist (puAmalgam h.le) ≤ (puAmalgam h.le).treeGraph.dist (s • α') μ := by
    by_contra hlt
    exact hZμσ (zm_le_qv_of_dist_lt _ hμ (by rw [SimpleGraph.dist_comm]; omega))
  have hμ₄ : 0 < (puAmalgam h.le).treeGraph.dist a₄ μ := by
    by_contra h0
    have he : a₄ = μ := (dist_eq_zero_iff _).1 (by omega)
    have := dist_triangle _ (s • α') a₃ a₄
    rw [dist_eq_one_of_adj _ hσ3.symm, dist_eq_one_of_adj _ h34, he] at this
    omega
  have hsa₃ : (puAmalgam h.le).treeGraph.Adj a₂ (s • a₃) := by
    have := (adj_smul _ s _ _).2 h23
    rwa [hsa₂] at this
  have hνα : ¬ ZM _ (s • baseA (puAmalgam h.le)) ≤ Qv _ (s • α') := by
    rw [zm_smul, qv_smul, map_conj_le_map_conj_iff]
    exact hc.2.2
  obtain ⟨hW₁, hrel₁, hst₁, h2₁⟩ := uSub_inf_bSub_eq_centralizer h hb hd ha₂ h23 hsa₃ hσ3
    ((isMVtx_smul _ s _).2 hα)
    (by rw [← hsa₂, dist_smul, hda₂]; omega) (by rw [dist_smul, hda₃]; omega)
    (by rw [← hsa, dist_smul, SimpleGraph.dist_comm, hda₁]; omega) hνα
    (hP _ _ _ ha₂ h23 hσ3)
  obtain ⟨hW₂, hrel₂, hst₂, h2₂⟩ := uSub_inf_bSub_eq_centralizer h hb hd ha₄ h34.symm
    (adj_geo_one _ hμ₄) hσ3 hμ (by omega)
    (by rw [dist_geo_right _ (by omega)]; omega) (by omega) hZμσ (hP _ _ _ ha₄ h34.symm hσ3)
  have hDs : s * ⁅z, u⁆ * s⁻¹ = ⁅z, u⁆ := by
    have hD := S5NQ.commutator_mem_dSub h hb ha₂ hda₂' (uSub_le_zm h.le _ hu) huB (hZμ hz)
    have hsc : s * ⁅u, z⁆ = ⁅u, z⁆ * s := Subgroup.mem_centralizer_iff.1 hD.2 s hs
    calc s * ⁅z, u⁆ * s⁻¹ = (s * ⁅u, z⁆ * s⁻¹)⁻¹ := by rw [← commutatorElement_inv]; group
      _ = ⁅u, z⁆⁻¹ := by rw [hsc, mul_inv_cancel_right]
      _ = ⁅z, u⁆ := commutatorElement_inv u z
  have huA : u ∈ critA _ (baseA (puAmalgam h.le)) α' :=
    ⟨zm_le_xm _ hyp hb0 hα' (uSub_le_zm h.le _ hu), huQ⟩
  have hzu_mem : ⁅z, u⁆ ∈ ⁅ZM _ (baseA (puAmalgam h.le)), S5.uSub h.le L α'⁆ ⊔
      (stab _ α' ⊓ Subgroup.centralizer (stab _ α' : Set (puAmalgam h.le).Universal)) :=
    sup_le_sup (critR_le_commutator h hb hc) (stabCenter_le_inf α')
      (hR (Subgroup.commutator_mem_commutator hz huA))
  have hcσ : ⁅z, s * u * s⁻¹⁆ ∈ ⁅ZM _ (s • baseA (puAmalgam h.le)), S5.uSub h.le L (s • α')⁆ ⊔
      (stab _ (s • α') ⊓
        Subgroup.centralizer (stab _ (s • α') : Set (puAmalgam h.le).Universal)) := by
    have e : ⁅ZM _ (s • baseA (puAmalgam h.le)), S5.uSub h.le L (s • α')⁆ ⊔
        (stab _ (s • α') ⊓
          Subgroup.centralizer (stab _ (s • α') : Set (puAmalgam h.le).Universal)) =
        (⁅ZM _ (baseA (puAmalgam h.le)), S5.uSub h.le L α'⁆ ⊔
          (stab _ α' ⊓ Subgroup.centralizer (stab _ α' : Set (puAmalgam h.le).Universal))).map
            (MulAut.conj s).toMonoidHom := by
      rw [Subgroup.map_sup, Subgroup.map_commutator,
        Subgroup.map_inf _ _ _ (MulAut.conj s).injective, ← zm_smul, ← uSub_smul h.le hLn,
        ← PU.centralizer_map_mulEquiv, ← stab_smul]
    rw [e, hzus_eq, ← hDs]
    exact ⟨_, hzu_mem, rfl⟩
  have hus' : s * u * s⁻¹ ∈ S5.uSub h.le L (s • α') ⊓
      Subgroup.centralizer (ZM _ (s • baseA (puAmalgam h.le)) : Set _) := by
    rw [← hW₁]
    exact ⟨hus, husB⟩
  exact hzus (commutator_eq_one h hd hσ hst₁ hst₂ h2₁ h2₂ hνα hZμσ hrel₁ hrel₂ hus' hz hcσ)

end Contra

section Main

omit [Fintype F] in
theorem lamAll_facts (h : PUHyp M T L) {q : ℕ} {α' μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ S5.lamAll h q a α') :
    IsMVtx _ μ ∧ (puAmalgam h.le).treeGraph.dist (baseA _) μ ≤ 2 := by
  obtain ⟨δ, hβδ, -, g, x, hg, hx, -, hμeq⟩ := hμ
  have hδ : IsMVtx _ δ := by
    have := isMVtx_iff_of_adj _ hβδ
    have hβ := not_isMVtx_baseB (puAmalgam h.le)
    tauto
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  obtain ⟨y, hy, rfl⟩ : ∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ = y • δ := by
    rcases hμeq with rfl | rfl
    · exact ⟨g⁻¹, inv_mem hg, rfl⟩
    · exact ⟨x⁻¹ * g⁻¹, mul_mem (inv_mem hxst) (inv_mem hg), by rw [mul_smul]⟩
  refine ⟨(isMVtx_smul _ y δ).2 hδ, ?_⟩
  rw [← (mem_stab _).1 hy, dist_smul]
  have := dist_triangle _ (baseA (puAmalgam h.le)) (baseB _) δ
  rw [dist_eq_one_of_adj _ (adj_baseA_baseB _), dist_eq_one_of_adj _ hβδ] at this
  exact this

theorem s58_first_sel (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {S : Submodule F (MSP.V4 F) → (puAmalgam h.le).Universal → (puAmalgam h.le).Universal → Prop}
    (h56S : Prod56 h k a S) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) :
    ∃ μ ∈ lamAllSel h (2 ^ k) a S α', IsCritical _ μ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hcr := ms22_iii _ hyp hb0 hC hc
  have hd' : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) :=
    hcr.2.1
  have hda₂ : (puAmalgam h.le).treeGraph.dist (baseA (puAmalgam h.le))
      (geo _ α' (baseA (puAmalgam h.le)) 2) = critDist (puAmalgam h.le) - 2 := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd']
  by_contra hno
  push Not at hno
  have hlam : ∀ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
      ¬ S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _) →
      ∀ μ ∈ lamSel h (2 ^ k) a S α' δ,
        ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
    intro δ hβδ hδB μ hμ
    have hμall : μ ∈ lamAllSel h (2 ^ k) a S α' := ⟨δ, hβδ, hδB, hμ⟩
    obtain ⟨hμM, hdμ⟩ := lamAll_facts h (lamAllSel_subset hμall)
    have hdist : (puAmalgam h.le).treeGraph.dist μ (geo _ α' (baseA (puAmalgam h.le)) 2) ≤
        critDist (puAmalgam h.le) := by
      have := dist_triangle _ μ (baseA (puAmalgam h.le)) (geo _ α' (baseA (puAmalgam h.le)) 2)
      rw [SimpleGraph.dist_comm (u := μ) (v := baseA _), hda₂] at this
      omega
    by_contra hZ
    have hge : critDist (puAmalgam h.le) ≤
        (puAmalgam h.le).treeGraph.dist μ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
      by_contra hlt
      exact hZ (zm_le_qv_of_dist_lt _ hμM (by omega))
    exact hno μ hμall ⟨hμM, le_antisymm hdist hge, hZ⟩
  have hP : ∀ δ, (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
      (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L δ) ≤ 2 ^ k := by
    intro δ hβδ
    by_cases hδB : S5.uSub h.le L δ ≤ S5.bSub h.le L (baseA _)
    · rw [Subgroup.relIndex_eq_one.2 hδB]
      exact Nat.one_le_two_pow
    · exact s57_sel h32 hX2 h52 h54 h55 h hmin hb hd h56S hc hαβ hβδ
        (hlam δ hβδ hδB)
  obtain ⟨δ₀, hβδ₀, hδ₀B⟩ := exists_uSub_not_le_bSub h hb
  obtain ⟨μ, hμ, hdμ, hZμ, hcard, hidx, hXU, hR⟩ :=
    s58_mu_sel h32 hX2 h52 h55 h hmin hb hd h56S hc hαβ hβδ₀ hδ₀B (hlam δ₀ hβδ₀ hδ₀B)
  obtain ⟨z, hz, u, hu, huQ, hzu⟩ := s58_zu h hb hd hc hZμ hcard hidx hXU
  exact s58_contra h hb hd (fun γ ε ρ hγ hγε hερ => relIndex_bSub_uSub_le h hP hγ hγε hερ) hc
    hμ hdμ hZμ hR hz hu huQ hzu

theorem s58_first (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) :
    ∃ μ ∈ S5.lamAll h (2 ^ k) a α', IsCritical _ μ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
  obtain ⟨μ, hμ, hμc⟩ := s58_first_sel h32 hX2 h52 h54 h55 h hmin hb hd
    (prod56_top h56 hmin hb hd) hc hαβ
  exact ⟨μ, lamAllSel_subset hμ, hμc⟩

theorem s58_hV (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) :
    ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' → ¬ Vv _ δ ≤ Qv _ (geo _ δ' δ 2) := by
  intro δ δ' hc
  have hb0 := h.critDist_pos
  have hdd : (puAmalgam h.le).treeGraph.dist δ δ' = critDist (puAmalgam h.le) := hc.2.1
  have hadj : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ δ' 1) := adj_geo_one _ (by omega)
  obtain ⟨g, rfl, hgβ⟩ := exists_smul_base_edge _ hc.1 hadj
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • δ') := by
    have := (isCritical_smul _ g⁻¹ _ _).2 hc
    rwa [inv_smul_smul] at this
  have hβ' : geo _ (baseA (puAmalgam h.le)) (g⁻¹ • δ') 1 = baseB _ := by
    have := geo_smul _ g⁻¹ (g • baseA (puAmalgam h.le)) δ' 1
    rw [hgβ] at this
    simpa only [inv_smul_smul] using this
  obtain ⟨μ, hμ, hμc⟩ := s58_first h32 hX2 h52 h54 h55 h56 h hmin hb hd hc' hβ'
  obtain ⟨hμM, hdμ⟩ := lamAll_facts h hμ
  intro hle
  apply hμc.2.2
  refine (zm_le_vv_of_dist hμM hdμ).trans ?_
  have e1 : geo _ δ' (g • baseA (puAmalgam h.le)) 2 =
      g • geo _ (g⁻¹ • δ') (baseA (puAmalgam h.le)) 2 := by
    rw [← geo_smul, smul_inv_smul]
  rw [e1, Vv, vi_smul, qv_smul, map_conj_le_map_conj_iff] at hle
  exact hle

theorem exists_isCritical_step (h : PUHyp M T L) {δ δ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ δ δ') (hV : ¬ Vv _ δ ≤ Qv _ (geo _ δ' δ 2)) :
    ∃ ρ, (puAmalgam h.le).treeGraph.dist δ ρ = 2 ∧ IsCritical _ ρ (geo _ δ' δ 2) := by
  have hyp := h.hyp20
  have hb := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist δ δ' = critDist (puAmalgam h.le) := hc.2.1
  have hb2 := two_le_critDist _ hyp hb
  set ε := geo _ δ' δ 2 with hεdef
  have hδε : (puAmalgam h.le).treeGraph.dist δ ε = critDist (puAmalgam h.le) - 2 := by
    rw [SimpleGraph.dist_comm, hεdef, dist_geo_right _ (by rw [SimpleGraph.dist_comm]; omega),
      SimpleGraph.dist_comm, hd]
  obtain ⟨ρ, hρ, hρε⟩ : ∃ ρ, (puAmalgam h.le).treeGraph.dist δ ρ ≤ 2 ∧
      ¬ Zv (puAmalgam h.le) ρ ≤ Qv _ ε := by
    by_contra hcon
    push Not at hcon
    exact hV (iSup₂_le fun ρ hρ => hcon ρ hρ)
  have htri := dist_triangle _ ρ δ ε
  rw [tdist_comm _ ρ δ] at htri
  by_cases hρM : IsMVtx _ ρ
  · rw [zv_of_isMVtx _ hρM] at hρε
    have hge : critDist (puAmalgam h.le) ≤ (puAmalgam h.le).treeGraph.dist ρ ε := by
      by_contra hlt
      exact hρε (zm_le_qv_of_dist_lt _ hρM (by omega))
    exact ⟨ρ, by omega, hρM, by omega, hρε⟩
  · exfalso
    rw [zv_of_not_isMVtx _ hρM] at hρε
    have hodd : ¬ Even ((puAmalgam h.le).treeGraph.dist δ ρ) := by
      rw [even_dist_iff]
      have := hc.1
      tauto
    have h1 : (puAmalgam h.le).treeGraph.dist δ ρ = 1 := by
      have h0 : (puAmalgam h.le).treeGraph.dist δ ρ ≠ 0 := fun h0 => hodd (h0 ▸ ⟨0, rfl⟩)
      have h2 : (puAmalgam h.le).treeGraph.dist δ ρ ≠ 2 := fun h2 => hodd (h2 ▸ ⟨1, rfl⟩)
      omega
    exact hρε ((zh_le_zm _ (SimpleGraph.dist_eq_one_iff_adj.mp h1)).trans
      (zm_le_qv_of_dist_lt _ hc.1 (by omega)))

theorem exists_isCritical_iter (h : PUHyp M T L)
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' → ¬ Vv _ δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ α α') :
    ∀ i, 2 * i + 2 ≤ critDist (puAmalgam h.le) →
      ∃ ρ, IsCritical _ ρ (geo _ α α' (critDist (puAmalgam h.le) - 2 * i)) ∧
        (puAmalgam h.le).treeGraph.dist ρ α = 2 * i := by
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨α, ?_, by simp⟩
    rw [Nat.mul_zero, Nat.sub_zero, ← hd, geo_dist]
    exact hc
  | succ i ih =>
    intro hi
    obtain ⟨ρ, hρc, hρα⟩ := ih (by omega)
    set v := geo _ α α' (critDist (puAmalgam h.le) - 2 * i)
    set w := geo _ α α' (critDist (puAmalgam h.le) - 2 * (i + 1))
    have hαw : (puAmalgam h.le).treeGraph.dist α w = critDist (puAmalgam h.le) - 2 * (i + 1) :=
      dist_geo _ (by omega)
    have hwv : (puAmalgam h.le).treeGraph.dist w v = 2 := by
      rw [dist_geo_geo _ (by omega) (by omega)]
      omega
    have hρv : (puAmalgam h.le).treeGraph.dist ρ v = critDist (puAmalgam h.le) := hρc.2.1
    have hw : w = geo _ v ρ 2 := by
      have t1 := dist_triangle _ ρ α w
      have t2 := dist_triangle _ ρ w v
      rw [hαw, hρα] at t1
      rw [hwv, hρv] at t2
      have e1 : (puAmalgam h.le).treeGraph.dist v w = 2 := by
        rw [SimpleGraph.dist_comm]
        exact hwv
      apply eq_geo_of_dist _ e1
      rw [e1, tdist_comm _ w ρ, tdist_comm _ v ρ, hρv]
      omega
    obtain ⟨ρ', hρρ', hρ'c⟩ := exists_isCritical_step h hρc (hV ρ v hρc)
    rw [← hw] at hρ'c
    refine ⟨ρ', hρ'c, ?_⟩
    have hρ'w : (puAmalgam h.le).treeGraph.dist ρ' w = critDist (puAmalgam h.le) := hρ'c.2.1
    have t1 := dist_triangle _ ρ' ρ α
    have t2 := dist_triangle _ ρ' α w
    rw [tdist_comm _ ρ' ρ, hρρ', hρα] at t1
    rw [hαw, hρ'w] at t2
    omega

theorem s58_third (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' → ¬ Vv _ δ ≤ Qv _ (geo _ δ' δ 2))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) :
    2 ^ k ≤ (S5.bSub h.le L (baseA _)).relIndex
      (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) := by
  have hyp := h.hyp20
  have hd' : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨m, hm⟩ := ms21_v _ hyp
  obtain ⟨ν, hνc, hνα⟩ := exists_isCritical_iter h hV hc (m - 1) (by omega)
  rw [show critDist (puAmalgam h.le) - 2 * (m - 1) = 2 by omega] at hνc
  have hαν : (puAmalgam h.le).treeGraph.dist (baseA _) ν = critDist (puAmalgam h.le) - 2 := by
    rw [SimpleGraph.dist_comm, hνα]
    omega
  have hβρ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hαε' : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) ν 1) :=
    adj_geo_one _ (by omega)
  have hε'ν : (puAmalgam h.le).treeGraph.dist (geo _ (baseA (puAmalgam h.le)) ν 1) ν =
      critDist (puAmalgam h.le) - 3 := by
    rw [dist_geo_right _ (by omega), hαν]
    omega
  have hνβ : (puAmalgam h.le).treeGraph.dist ν (baseB _) < critDist (puAmalgam h.le) := by
    have := dist_triangle _ ν (baseA (puAmalgam h.le)) (baseB _)
    rw [hνα, dist_eq_one_of_adj _ (adj_baseA_baseB _)] at this
    omega
  obtain ⟨-, -, -, hLB, hle⟩ := uSub_inf_bSub_le_centralizer h hb hd (isMVtx_baseA _)
    (adj_baseA_baseB _) hαε' hβρ hνc.1 (by omega) (by omega) hνβ hνc.2.2
  exact hLB.trans hle

theorem s58_of (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55) (h56 : S56) :
    S58 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hαβ
  have h1 := s58_first h32 hX2 h52 h54 h55 h56 h hmin hb hd hc hαβ
  refine ⟨h1, ?_,
    s58_third h hb hd (s58_hV h32 hX2 h52 h54 h55 h56 h hmin hb hd) hc hαβ⟩
  obtain ⟨μ, hμ, hμc⟩ := h1
  obtain ⟨hμM, hdμ⟩ := lamAll_facts h hμ
  intro hle
  exact hμc.2.2 ((zm_le_vv_of_dist hμM hdμ).trans hle)

end Main

end S5B

end CFSG.Quasithin.MS93
