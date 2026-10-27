module

public import CFSG.Quasithin.MS93.S512RLem
public import CFSG.Quasithin.MS93.S512RLine
public import CFSG.Quasithin.MS93.S512RQ2
public import CFSG.Quasithin.MS93.S512RThree

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512R

section Sp4

variable {F : Type} [Field F]

theorem xPoint_inf_xPoint_eq_bot {p₁ p₂ : Submodule F (MSP.V4 F)} (hp₁ : MSP.IsPoint p₁)
    (hp₂ : MSP.IsPoint p₂) (hp : p₁ ≠ p₂) : MSP.xPoint p₁ ⊓ MSP.xPoint p₂ = ⊥ := by
  have hinf : p₁ ⊓ p₂ = ⊥ := by
    rw [← Submodule.finrank_eq_zero (R := F)]
    by_contra hne0
    have hle1 : Module.finrank F ↥(p₁ ⊓ p₂) ≤ 1 := by
      have := Submodule.finrank_mono (inf_le_left : p₁ ⊓ p₂ ≤ p₁)
      unfold MSP.IsPoint at hp₁
      omega
    have h1 : Module.finrank F ↥(p₁ ⊓ p₂) = 1 := by omega
    have e1 : p₁ ⊓ p₂ = p₁ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hp₁])
    have e2 : p₁ ⊓ p₂ = p₂ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, hp₂])
    exact hp (e1.symm.trans e2)
  refine MSP.fixSp_eq_top_iff.1 (eq_top_iff.2 fun v _ => MSP.mem_fixSp.2 fun g hg => ?_)
  have h3 : MSP.mat g *ᵥ v - v ∈ p₁ ⊓ p₂ :=
    ⟨MSP.sub_mem_of_mem_fixer_perp hg.1 v, MSP.sub_mem_of_mem_fixer_perp hg.2 v⟩
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at h3
  exact h3

theorem card_xPoint_sup_ge [Finite F] {p₁ p₂ : Submodule F (MSP.V4 F)} (hp₁ : MSP.IsPoint p₁)
    (hp₂ : MSP.IsPoint p₂) (hp : p₁ ≠ p₂) :
    Nat.card F ^ 2 ≤ Nat.card ↥(MSP.xPoint p₁ ⊔ MSP.xPoint p₂) := by
  have e1 := Subgroup.relIndex_mul_relIndex ⊥ (MSP.xPoint p₁) (MSP.xPoint p₁ ⊔ MSP.xPoint p₂)
    bot_le le_sup_left
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, MSP.card_xPoint hp₁] at e1
  have h2 : (MSP.xPoint p₁).relIndex (MSP.xPoint p₂) ≤
      (MSP.xPoint p₁).relIndex (MSP.xPoint p₁ ⊔ MSP.xPoint p₂) :=
    Subgroup.relIndex_le_of_le_right le_sup_right
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  rw [← Subgroup.inf_relIndex_right, xPoint_inf_xPoint_eq_bot hp₁ hp₂ hp,
    Subgroup.relIndex_bot_left, MSP.card_xPoint hp₂] at h2
  calc Nat.card F ^ 2 = Nat.card F * Nat.card F := sq _
    _ ≤ Nat.card F * (MSP.xPoint p₁).relIndex (MSP.xPoint p₁ ⊔ MSP.xPoint p₂) :=
        Nat.mul_le_mul_left _ h2
    _ = _ := e1

end Sp4

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem sq_lt_card_imSp_M (h51 : S51) (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) (hTl : (T.subgroupOf M).map a ≤ MSP.qLine l)
    {E₁ E₂ : Subgroup G} (hE₁T : E₁ ≤ T) (hE₂T : E₂ ≤ T)
    (hc₁ : (pCoreOf 2 M).relIndex E₁ = 2 ^ k)
    (hu₁ : (Subgroup.centralizer (E₁ : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hc₂ : (pCoreOf 2 M).relIndex E₂ = 2 ^ k)
    (hu₂ : (Subgroup.centralizer (E₂ : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hne : Uq M T L ⊓ Subgroup.centralizer (E₁ : Set G) ≠
      Uq M T L ⊓ Subgroup.centralizer (E₂ : Set G)) :
    (2 ^ k) ^ 2 < Nat.card ((T.subgroupOf M).map a) := by
  by_contra hle
  push Not at hle
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hF : 1 < Nat.card F := by
    rw [hFq]
    exact Nat.one_lt_two_pow (by have := hd.1; omega)
  obtain ⟨p₁, hp₁, hE₁a⟩ := S51.exists_imSp_eq_xPoint hd h hE₁T hc₁ hu₁
  obtain ⟨p₂, hp₂, hE₂a⟩ := S51.exists_imSp_eq_xPoint hd h hE₂T hc₂ hu₂
  have hp : p₁ ≠ p₂ := by
    rintro rfl
    apply hne
    obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
    have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
    have hfix : MSP.fixSp ((E₁.subgroupOf M).map a) = MSP.fixSp ((E₂.subgroupOf M).map a) := by
      have e1 : (E₁.subgroupOf M).map a = MSP.xPoint p₁ := hE₁a
      have e2 : (E₂.subgroupOf M).map a = MSP.xPoint p₁ := hE₂a
      rw [e1, e2]
    ext u
    constructor
    · rintro ⟨hu, huc⟩
      refine ⟨hu, (S5B.mem_centralizer_iff_vec h hlift c (hE₂T.trans h.le) ⟨u, hu⟩).2 ?_⟩
      rw [← hfix]
      exact (S5B.mem_centralizer_iff_vec h hlift c (hE₁T.trans h.le) ⟨u, hu⟩).1 huc
    · rintro ⟨hu, huc⟩
      refine ⟨hu, (S5B.mem_centralizer_iff_vec h hlift c (hE₁T.trans h.le) ⟨u, hu⟩).2 ?_⟩
      rw [hfix]
      exact (S5B.mem_centralizer_iff_vec h hlift c (hE₂T.trans h.le) ⟨u, hu⟩).1 huc
  have hsub : MSP.xPoint p₁ ⊔ MSP.xPoint p₂ ≤ (T.subgroupOf M).map a := by
    rw [← hE₁a, ← hE₂a]
    exact sup_le (S5.imSp_mono a hE₁T) (S5.imSp_mono a hE₂T)
  have hcard := card_xPoint_sup_ge hp₁ hp₂ hp
  rw [hFq] at hcard
  have hTeq : MSP.xPoint p₁ ⊔ MSP.xPoint p₂ = (T.subgroupOf M).map a :=
    Subgroup.eq_of_le_of_card_ge hsub (hle.trans hcard)
  have hJT : S5.jOffM M T L (2 ^ k) ≤ T := iSup₂_le fun E hE => hE.1.1
  have hJM : S5.jOffM M T L (2 ^ k) ≤ M := hJT.trans h.le
  have hJ : S5.jOffM M T L (2 ^ k) = T := by
    rcases h54 G M T L h hmin hb k F _ _ a hd with ⟨-, -, hJ2⟩ | ⟨-, -, p, hp, hTq⟩
    · rw [S5B.qv_baseA_eq h, S5.jOff_baseA h, S5B.relIndex_imM h.le hJM] at hJ2
      have hJ2' : (2 ^ k) ^ 2 ≤ Nat.card (((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a) :=
        le_of_le_of_eq hJ2 (S5.IsSp4Data.card_imSp hd h hJT).symm
      exact S512T.jOffM_eq_of_le_qLine_M h hd hl hTl hJ2'
    · exfalso
      rw [puAmalgam.qv_baseB, S5.vIm_imM h] at hTq
      exact S512T.not_qPoint_le_qLine hF hp hl ((le_of_eq hTq.symm).trans hTl)
  refine S5.jOffM_ne_xPoint_sup h51 hd h hmin hb hp₁ hp₂ ?_
  rw [hJ]
  exact hTeq.symm

theorem sq_lt_relIndex_of_two (h51 : S51) (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    {δ ε : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδε : (puAmalgam h.le).treeGraph.Adj δ ε)
    {E₁ E₂ : Subgroup (puAmalgam h.le).Universal} (hE₁ε : E₁ ≤ Qv _ ε) (hE₂ε : E₂ ≤ Qv _ ε)
    (hc₁ : (Qv _ δ).relIndex E₁ = 2 ^ k) (hc₂ : (Qv _ δ).relIndex E₂ = 2 ^ k)
    (hr₁ : (Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    (hr₂ : (Subgroup.centralizer (E₂ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    (hne : S5.uSub h.le L δ ⊓ Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal) ≠
      S5.uSub h.le L δ ⊓ Subgroup.centralizer (E₂ : Set (puAmalgam h.le).Universal)) :
    (2 ^ k) ^ 2 < (Qv _ δ).relIndex (Qv _ ε) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨c, rfl, rfl⟩ := exists_smul_base_edge _ hδ hδε
  have hE₁st : E₁ ≤ stab _ (c • baseA (puAmalgam h.le)) :=
    hE₁ε.trans (qv_le_stab_of_adj _ hδε.symm)
  have hE₂st : E₂ ≤ stab _ (c • baseA (puAmalgam h.le)) :=
    hE₂ε.trans (qv_le_stab_of_adj _ hδε.symm)
  obtain ⟨E₁₀, hE₁₀M, rfl⟩ := S5B.exists_eq_map_imM h.le c hE₁st
  obtain ⟨E₂₀, hE₂₀M, rfl⟩ := S5B.exists_eq_map_imM h.le c hE₂st
  have hU : S5.uSub h.le L (c • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj c).toMonoidHom := by
    rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h]
  have hQε : Qv _ (c • baseB (puAmalgam h.le)) =
      (imM h.le T).map (MulAut.conj c).toMonoidHom := by
    rw [qv_smul, puAmalgam.qv_baseB]
  have hQδ : Qv _ (c • baseA (puAmalgam h.le)) =
      (imM h.le (pCoreOf 2 M)).map (MulAut.conj c).toMonoidHom := by
    rw [qv_smul, S5B.qv_baseA_eq h]
  have hT : ∀ {E₀ : Subgroup G}, E₀ ≤ M →
      (imM h.le E₀).map (MulAut.conj c).toMonoidHom ≤ Qv _ (c • baseB (puAmalgam h.le)) →
      E₀ ≤ T := by
    intro E₀ hE₀M hE
    rw [hQε, map_conj_le_map_conj_iff, imM_le_imM_iff h.le hE₀M] at hE
    exact hE
  have hidx : ∀ {E₀ : Subgroup G}, E₀ ≤ M →
      (Qv _ (c • baseA (puAmalgam h.le))).relIndex
        ((imM h.le E₀).map (MulAut.conj c).toMonoidHom) = (pCoreOf 2 M).relIndex E₀ := by
    intro E₀ hE₀M
    rw [hQδ, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
      S5B.relIndex_imM h.le hE₀M]
  have hrel : ∀ {E₀ : Subgroup G}, E₀ ≤ M →
      (Subgroup.centralizer (((imM h.le E₀).map (MulAut.conj c).toMonoidHom : Subgroup _) :
        Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (c • baseA _)) = 2 ^ k →
      (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) = 2 ^ k := by
    intro E₀ hE₀M hr
    rw [hU, PU.centralizer_map_mulEquiv,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
      S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M] at hr
    exact hr
  have hinf : ∀ {E₀ : Subgroup G}, E₀ ≤ M →
      S5.uSub h.le L (c • baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (((imM h.le E₀).map (MulAut.conj c).toMonoidHom : Subgroup _) :
          Set (puAmalgam h.le).Universal) =
        (imM h.le (Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G))).map
          (MulAut.conj c).toMonoidHom := by
    intro E₀ hE₀M
    rw [hU, PU.centralizer_map_mulEquiv,
      ← Subgroup.map_inf _ _ _ (MulAut.conj c).injective, imM_inf_centralizer h.le _ hE₀M]
  have hne₀ : Uq M T L ⊓ Subgroup.centralizer (E₁₀ : Set G) ≠
      Uq M T L ⊓ Subgroup.centralizer (E₂₀ : Set G) := by
    intro heq
    apply hne
    rw [hinf hE₁₀M, hinf hE₂₀M, heq]
  have hTl' : (T.subgroupOf M).map a ≤ MSP.qLine l :=
    S512T.imSp_le_of_imM_le_vPre h.le (by rw [← puAmalgam.qv_baseB]; exact hTl)
  have key := sq_lt_card_imSp_M h51 h54 h hmin hb hd hl hTl' (hT hE₁₀M hE₁ε) (hT hE₂₀M hE₂ε)
    (by rw [← hidx hE₁₀M]; exact hc₁) (hrel hE₁₀M hr₁) (by rw [← hidx hE₂₀M]; exact hc₂)
    (hrel hE₂₀M hr₂) hne₀
  rw [hQδ, hQε, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
    S5B.relIndex_imM h.le h.le, ← S5.IsSp4Data.card_imSp hd h le_rfl]
  exact key

@[expose] def Three56ResL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le),
        S5B.IsChain512Sel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) α' ν μ₁ μ₂ →
        (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
        ∀ l : Submodule F (MSP.V4 F),
          S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
        ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
          S5.Concl56 h (2 ^ k) a α' l g x →
          ∀ w : (puAmalgam h.le).Universal,
            ((w = x ∧ μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ∨
              (w = x⁻¹ ∧ μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)) →
          ¬ ZM _ (w • α') ≤ Subgroup.normalizer
            (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
              XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal) →
          2 ^ k < (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
            Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁) →
          IsCritical _ μ₁ (w • geo _ (baseA (puAmalgam h.le)) α' 2) →
          (Qv _ (w • geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
          Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l) →
          (2 ^ k) ^ 2 < (Qv _ μ₁).relIndex
            (Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1)) →
          (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k

theorem three56F_of_s51 (h32 : S32) (h52 : S52) (h54 : S54) (h58 : S5B.S58)
    (hZ : S5Q2.Q2EvenZ) (hone : S512Z.OneCF) (hcore : S512T.Core) (hL : Three56ResL)
    (hA : Three56ResA) : Three56F := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS hq1 hq l hl g hg x hx hc56 hμ hng
    hnx
  have hch := S5B.isChain512Sel_subset hchS
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨hc, hαβ, hcμ, ⟨y, hy, hμy⟩, hdμ, hmid, -⟩ := S512T.chain_geo h hb4 hch
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hxP : x ∈ S5.vPre h.le a (MSP.stab l) := hc56.2.2.2 hq1
  have hopp : S5.Opp56 h (2 ^ k) a l g x := opp56_of_mem_stab h hxst hc56 hxP
  have hthree : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L μ₁) ≤ 2 ^ k →
      (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k := by
    intro hle
    rw [S512T.relIndex_bSub_zm_eq h hb4 hcμ hmid]
    refine le_antisymm hle ?_
    have h1 := (h58 G M T L h hmin hb k F _ _ a hd α' hc hαβ).2.2
    rw [hμy, S5B.relIndex_bSub_uSub_smul h hy]
    exact h1
  obtain ⟨w, hwcase, hnw⟩ : ∃ w : (puAmalgam h.le).Universal,
      ((w = x ∧ μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ∨
        (w = x⁻¹ ∧ μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)) ∧
      ¬ ZM _ (w • α') ≤ Subgroup.normalizer
        (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
          XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    by_cases hμg : μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2
    · exact ⟨x, Or.inl ⟨rfl, hμg⟩, hng hμg⟩
    · have hμx := hμ.resolve_left hμg
      exact ⟨x⁻¹, Or.inr ⟨rfl, hμx⟩, hnx hμx⟩
  have hwst : w ∈ stab _ (baseA (puAmalgam h.le)) := by
    rcases hwcase with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hxst
    · exact inv_mem hxst
  have hν : w⁻¹ • μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
      w⁻¹ • μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 := by
    rcases hwcase with ⟨rfl, he⟩ | ⟨rfl, he⟩
    · right
      rw [he]
    · left
      rw [he, inv_inv, smul_inv_smul]
  have hνlam : w⁻¹ • μ₁ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    ⟨g, x, hg, hx, Or.inr ⟨l, hl, hc56⟩, hν⟩
  have hZ2 : ZM _ (w • α') ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ₁ ⊓ Qv _ (w • geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    have h1 := hone G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS (w⁻¹ • μ₁) hνlam
    rw [S512T.zHat_eq h hd hc hq1] at h1
    have h2 := zm_le_normalizer_smul h hwst h1
    rwa [smul_inv_smul] at h2
  have hY : S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≠
      S5.uSub h.le L μ₁ ⊓ Qv _ (w • geo _ (baseA (puAmalgam h.le)) α' 2) := by
    intro heq
    apply hnw
    rw [heq]
    exact hZ2
  by_cases hlarge : 2 ^ k < (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁)
  swap
  · push Not at hlarge
    exact hthree ((S512Z.relIndex_bSub_le_relIndex_centralizer h32 h hb hcμ.1 hdμ).trans hlarge)
  have hcent := cent56F_holds_e h32 h52 hZ G M T L h hmin hb k F _ _ a hd α' hc hαβ l hl g hg
    x hx hc56 hopp
  have hR₁ := hcent μ₁ hμ
  have hR₂ : ⁅ZM (puAmalgam h.le) μ₁,
      ZM (puAmalgam h.le) (w • geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
        stabCenter _ (baseA (puAmalgam h.le)) := by
    have h1 := commutator_zm_smul_le_stabCenter h hwst (hcent (w⁻¹ • μ₁) hν)
    rwa [smul_inv_smul] at h1
  by_cases hcrit : IsCritical _ μ₁ (w • geo _ (baseA (puAmalgam h.le)) α' 2)
  swap
  · exact hA G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS hq1 hq l hl g hg x hx hc56 w
      hwcase hnw hlarge hcrit
  by_cases hbad : 2 ^ k < (Qv _ (w • geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁)
  ·
    exfalso
    have hcrit' : IsCritical _ (w⁻¹ • μ₁) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
      have := (isCritical_smul _ w⁻¹ _ _).2 hcrit
      rwa [inv_smul_smul] at this
    have hbad' : 2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex
        (ZM _ (w⁻¹ • μ₁)) := by
      have e := S5B.relIndex_qv_zm_smul w⁻¹ (w • geo _ (baseA (puAmalgam h.le)) α' 2) μ₁
      rw [inv_smul_smul] at e
      rw [e]
      exact hbad
    have hy' : ∃ y ∈ stab _ (baseA (puAmalgam h.le)),
        w⁻¹ • μ₁ = y • geo _ (baseA (puAmalgam h.le)) α' 2 := by
      rcases hν with he | he
      · exact ⟨g⁻¹, inv_mem hg, he⟩
      · exact ⟨x⁻¹ * g⁻¹, mul_mem (inv_mem hxst) (inv_mem hg), by rw [he, mul_smul]⟩
    exact hcore G M T L h hmin hb4 k F _ _ a hd α' hc hαβ l hl (w⁻¹ • μ₁) hy' hcrit' hbad'
      (hcent (w⁻¹ • μ₁) hν)
  push Not at hbad
  have hgood : (Qv _ (w • geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k :=
    le_antisymm hbad (S512T.le_relIndex_qv_zm h hb4 hd hcrit)
  obtain ⟨hμM, -, -, -, hμρ, hρα, -, -, -, hαγ, -, -⟩ := S512T.pair_facts h hb4 hcμ
  rw [hmid] at hρα hαγ
  obtain ⟨-, -, -, hd₂, -, -, -, -, -, -, -, -⟩ := S512T.pair_facts h hb4 hcrit
  have hdαwγ : (puAmalgam h.le).treeGraph.dist (baseA _)
      (w • geo _ (baseA (puAmalgam h.le)) α' 2) = 2 := by
    have := dist_smul _ w (baseA (puAmalgam h.le)) (geo _ (baseA (puAmalgam h.le)) α' 2)
    rw [(mem_stab _).1 hwst] at this
    rw [this, hαγ]
  have hmid₂ : geo _ μ₁ (w • geo _ (baseA (puAmalgam h.le)) α' 2) 2 = baseA _ := by
    symm
    refine eq_geo_of_dist _ (by rw [SimpleGraph.dist_comm]; exact hdμ) ?_
    rw [SimpleGraph.dist_comm, hdμ, hdαwγ, hd₂]
  have hρ₂ : geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1 =
      geo _ μ₁ (w • geo _ (baseA (puAmalgam h.le)) α' 2) 1 :=
    S512T.eq_geo_one_of_adj h hb4 hcrit hmid₂ hρα.symm hμρ.symm
  obtain ⟨hE₁, -, -, -⟩ := S512T.zm_facts h hb4 hcμ
  obtain ⟨hE₂, -, -, -⟩ := S512T.zm_facts h hb4 hcrit
  rw [← hρ₂] at hE₂
  have hQst : Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤
      stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_adj _ hρα
  have hcomm : ∀ {δ : Vtx (puAmalgam h.le)},
      ⁅ZM (puAmalgam h.le) μ₁, ZM (puAmalgam h.le) δ⁆ ≤ stabCenter _ (baseA (puAmalgam h.le)) →
      ⁅S5.uSub h.le L μ₁, ZM _ δ⁆ ≤ Subgroup.centralizer
        (Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) :
          Set (puAmalgam h.le).Universal) := by
    intro δ hR r hr
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact S510.commute_of_mem_stabCenter
      (hR (Subgroup.commutator_mono (S5B.uSub_le_zm h.le μ₁) le_rfl hr)) (hQst ht)
  have hr₁ : (Subgroup.centralizer (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁) = 2 ^ k := by
    rw [← S512T.relIndex_qv_zm_eq h hb4 hcμ]
    exact hq
  have hr₂ : (Subgroup.centralizer (ZM _ (w • geo _ (baseA (puAmalgam h.le)) α' 2) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L μ₁) = 2 ^ k := by
    rw [← S512T.relIndex_qv_zm_eq h hb4 hcrit]
    exact hgood
  have hne : S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer
      (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Set (puAmalgam h.le).Universal) ≠
      S5.uSub h.le L μ₁ ⊓ Subgroup.centralizer
        (ZM _ (w • geo _ (baseA (puAmalgam h.le)) α' 2) : Set (puAmalgam h.le).Universal) := by
    rw [← S512T.uSub_inf_qv_eq h hb4 hcμ, ← S512T.uSub_inf_qv_eq h hb4 hcrit]
    exact hY
  have hline := qv_le_vPre_qLine_of_two (s51_of h32) h hmin hb hd hl.2.1 hl.2.2.2 hμM hμρ hE₁ hE₂
    hr₁ hr₂ hne (hcomm hR₁) (hcomm hR₂)
  have hc₁ : (Qv _ μ₁).relIndex (ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2)) = 2 ^ k :=
    le_antisymm (S512T.relIndex_qv_zm_symm h hb4 hd hcμ hq.le)
      (S512T.le_relIndex_qv_zm h hb4 hd (ms22_iii _ h.hyp20 hb0 h.centHyp hcμ))
  have hc₂ : (Qv _ μ₁).relIndex (ZM _ (w • geo _ (baseA (puAmalgam h.le)) α' 2)) = 2 ^ k :=
    le_antisymm (S512T.relIndex_qv_zm_symm h hb4 hd hcrit hgood.le)
      (S512T.le_relIndex_qv_zm h hb4 hd (ms22_iii _ h.hyp20 hb0 h.centHyp hcrit))
  have hT := sq_lt_relIndex_of_two (s51_of h32) h54 h hmin hb hd hl.2.1 hline hμM hμρ hE₁ hE₂
    hc₁ hc₂ hr₁ hr₂ hne
  exact hL G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS hq1 hq l hl g hg x hx hc56 w
    hwcase hnw hlarge hcrit hgood hline hT


end S512R

end CFSG.Quasithin.MS93
