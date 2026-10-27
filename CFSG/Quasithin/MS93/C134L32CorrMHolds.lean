module

public import CFSG.Milestones.ASVolI.C135.WMain
public import CFSG.Quasithin.Background.C134L32CorrM

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement Matrix Pointwise

section Def

variable {G : Type} [Group G]

@[expose] def burnsideC134w_MS93Case13WX (V T L : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
    Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
    centerOf V = V ⊓ Subgroup.centralizer (L : Set G) ⊔ ⁅centerOf V, L⁆ ∧
    V ⊓ Subgroup.centralizer (L : Set G) ⊓ ⁅centerOf V, L⁆ = ⊥ ∧
    IsSumOfNaturalModulesVia L ⁅centerOf V, L⁆ ⊥ α false 1 ∧
    IsChiefSeriesFrom L V V 6 ∧
    QjInfo T L (centerOf V) (2 ^ n) ∧
    V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∧
    ∃ A₃ A₄ : Subgroup G, IsSumOfNaturalModulesVia L A₃ (centerOf V) α true 1 ∧
      IsSumOfNaturalModulesVia L A₄ A₃ α true 2 ∧ IsSumOfNaturalModulesVia L V A₄ α false 2

theorem burnsideC134w_MS93Case13WX.toW {V T L : Subgroup G}
    (h : burnsideC134w_MS93Case13WX V T L) : burnsideC134w_MS93Case13W V T L := by
  obtain ⟨n, F, i₁, i₂, α, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  exact ⟨n, F, i₁, i₂, α, h1, h2, h3, h4, h5, h6, h7⟩

theorem burnsideC134w_MS93Case13WX.mono {V T T₁ L : Subgroup G}
    (h : burnsideC134w_MS93Case13WX V T₁ L) (hT : T₁ ≤ T) :
    burnsideC134w_MS93Case13WX V T L := by
  obtain ⟨n, F, i₁, i₂, α, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨n, F, i₁, i₂, α, h1, h2, h3, h4, h5, h6, h7.mono hT, h8, h9⟩

end Def

section Hloc

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
  {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideC134w_hloc_facts (c : Ctx M T L φ) (hZV : c.HZV)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) (hN : 64 ≤ N)
    {δ : Vtx (puAmalgam c.hyp.le)} (hδ : p 34 = δ) :
    Hloc c.hyp.le L δ ≤ ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓
        Subgroup.centralizer (Ltil c.hyp.le L δ : Set _) ∧ Hloc c.hyp.le L δ ≠ ⊥ := by
  subst hδ
  have h := c.hyp
  have ha : Even 34 := by decide
  have hα := c.isMVtx_of_isGoodPath hp (k := 34) (by omega) ha
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  have hHV : Hloc h.le L (p 34) ≤ ⁅Qv (puAmalgam h.le) (p 34), Ltil h.le L (p 34)⁆ :=
    (c.hloc_le_commutator_qv_ltil hZV (S45Q4.hQ4 c) hp hp' ha le_rfl (by omega) hpp' hU1
      hU3).trans (Subgroup.commutator_le_self _)
  have hH6 : Hloc h.le L (p 34) ≤ Zloc h.le L (p 34) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hα)
  have hZC : Zloc h.le L (p 34) ≤ Subgroup.centralizer (Ltil h.le L (p 34) : Set _) := by
    rw [c.zloc_eq_zm_inf_centralizer hα]
    exact inf_le_right
  refine ⟨le_inf hHV (hH6.trans hZC), ?_⟩
  intro hb
  have hcard := c.card_hloc hp (x := 28) (by decide) (by omega) (by omega)
  rw [show 28 + 6 = 34 from rfl, hb, Subgroup.card_bot] at hcard
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have h4 : 2 ^ 2 ≤ Fintype.card F ^ 2 := Nat.pow_le_pow_left h2 2
  omega

end Hloc

section BaseA

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F] {M T L : Subgroup G}

theorem burnsideC134w_case13WX_of_baseA (h : PUHyp M T L) {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) (hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2)
    (hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) = Fintype.card F)
    {ψ₀ : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSL 3 F)} (hψ₀ : Function.Surjective ψ₀)
    (hU₀ : IsSumOfNaturalModulesVia (stab _ (baseA _)) (Uloc h.le L (baseA _)) ⊥ ψ₀ false 1)
    (hHZ : ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
      Subgroup.centralizer (Ltil h.le L (baseA _) : Set _) ≤ Zloc h.le L (baseA _))
    (hF3 : centerOf ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ =
      Uloc h.le L (baseA _) ⊔ ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
        Subgroup.centralizer (Ltil h.le L (baseA _) : Set _))
    (hZL : ⁅centerOf ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆,
      Ltil h.le L (baseA _)⁆ = Uloc h.le L (baseA _))
    (h₁ : IsSumOfNaturalModulesVia (stab _ (baseA _))
      (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
        (Vcirc h.le L (baseA _) ⊔ ZM _ (baseA _)))
      (centerOf ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆) ψ₀ true 1)
    (h₂ : IsSumOfNaturalModulesVia (stab _ (baseA _))
      (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
        Subgroup.centralizer (Vcirc h.le L (baseA _) : Set _))
      (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
        (Vcirc h.le L (baseA _) ⊔ ZM _ (baseA _))) ψ₀ true 2)
    (h₃ : IsSumOfNaturalModulesVia (stab _ (baseA _))
      ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆
      (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
        Subgroup.centralizer (Vcirc h.le L (baseA _) : Set _)) ψ₀ false 2)
    (hHV : Hloc h.le L (baseA _) ≤ ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
      Subgroup.centralizer (Ltil h.le L (baseA _) : Set _))
    (hH1 : Hloc h.le L (baseA _) ≠ ⊥) :
    burnsideC134w_MS93Case13WX (Vq M L) T L := by
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨-, hZM, -, -⟩ := s41_holds G M T L h hfull
  obtain ⟨n, hn⟩ := hφ.1
  have hZU : Zq M L ⊓ Uq M T L = ⊥ := hφ.2.2.2.1
  have hOM : pCoreOf 2 M ≤ M := pCoreOf_le' M
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hVM : Vq M L ≤ M := Vq_le h.L_le
  have hZqM : Zq M L ≤ M := inf_le_left.trans (Xq_le M)
  have hQ : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hLt : Ltil h.le L (baseA _) = imM h.le L :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)
  have hUl : Uloc h.le L (baseA _) = imM h.le (Uq M T L) :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer hUM).2
      (le_normalizer_Uq h.le_normalizer))
  have hZl : Zloc h.le L (baseA _) = imM h.le (Zq M L) :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer hZqM).2
      (le_normalizer_Zq h.le_normalizer))
  have hV : ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ = imM h.le (Vq M L) := by
    rw [hQ, hLt, imM_commutator h.le hOM h.L_le]
  have hstab : imM h.le M = stab (puAmalgam h.le) (baseA _) := (puAmalgam.stab_baseA h.le).symm
  have hbot : imM h.le (⊥ : Subgroup G) = ⊥ := by
    rw [imM, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hV₀M : ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ≤ imM h.le M := by
    rw [hV]
    exact imM_mono h.le hVM
  set V := Vq M L with hVdef
  set A₃ := S46.imMPull h.le (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
    (Vcirc h.le L (baseA _) ⊔ ZM _ (baseA _))) with hA₃
  set A₄ := S46.imMPull h.le (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
    Subgroup.centralizer (Vcirc h.le L (baseA _) : Set _)) with hA₄
  have hA₃M : A₃ ≤ M := S46.imMPull_le h.le _
  have hA₄M : A₄ ≤ M := S46.imMPull_le h.le _
  have eA₃ : imM h.le A₃ = ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
      (Vcirc h.le L (baseA _) ⊔ ZM _ (baseA _)) :=
    S46.imM_imMPull h.le (inf_le_left.trans hV₀M)
  have eA₄ : imM h.le A₄ = ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
      Subgroup.centralizer (Vcirc h.le L (baseA _) : Set _) :=
    S46.imM_imMPull h.le (inf_le_left.trans hV₀M)
  have hZVM : centerOf V ≤ M := inf_le_left.trans hVM
  have hCLM : V ⊓ Subgroup.centralizer (L : Set G) ≤ M := inf_le_left.trans hVM
  have hZLM : ⁅centerOf V, L⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem (hZVM hx) (h.L_le hy)) (M.inv_mem (hZVM hx)))
      (M.inv_mem (h.L_le hy))
  have eZ : imM h.le (centerOf V) =
      centerOf ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ := by
    rw [S46.imM_centerOf h.le hVM, hV]
  have eCL : imM h.le (V ⊓ Subgroup.centralizer (L : Set G)) =
      ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
        Subgroup.centralizer (Ltil h.le L (baseA _) : Set _) := by
    rw [imM_inf_centralizer h.le V h.L_le, ← hV, ← hLt]
  have eZL : ⁅centerOf V, L⁆ = Uq M T L := by
    rw [← S46.imM_eq_imM_iff h.le hZLM hUM, imM_commutator h.le hZVM h.L_le, eZ, ← hLt, hZL, hUl]
  have hHpZ : V ⊓ Subgroup.centralizer (L : Set G) ≤ Zq M L := by
    rw [← imM_le_imM_iff h.le hCLM, eCL, ← hZl]
    exact hHZ
  have hZs : centerOf V = Uq M T L ⊔ V ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← S46.imM_eq_imM_iff h.le hZVM (sup_le hUM hCLM), imM_sup h.le hUM hCLM, eZ, eCL, ← hUl,
      hF3]
  have hUH : Uq M T L ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
    refine le_bot_iff.mp ((inf_le_inf_left _ hHpZ).trans ?_)
    rw [inf_comm, hZU]
  have hUc : Uq M T L ≤ Subgroup.centralizer (Uq M T L : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      isMulCommutative_subgroup_iff.mp h.isElemAbelian_Uq.1 y hy x hx
  have hψ : Function.Surjective
      (ψ₀.comp ((S46.imMEquiv h.le le_rfl).trans (MulEquiv.subgroupCongr hstab)).toMonoidHom) :=
    hψ₀.comp (MulEquiv.surjective _)
  have hαs : Function.Surjective
      ((ψ₀.comp ((S46.imMEquiv h.le le_rfl).trans (MulEquiv.subgroupCongr hstab)).toMonoidHom).comp
        (Subgroup.inclusion h.L_le)) := by
    intro y
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hψ y
    exact ⟨⟨ℓ, hℓL⟩, hℓ⟩
  have hN1 : IsSumOfNaturalModulesVia L ⁅centerOf V, L⁆ ⊥
      ((ψ₀.comp ((S46.imMEquiv h.le le_rfl).trans (MulEquiv.subgroupCongr hstab)).toMonoidHom).comp
        (Subgroup.inclusion h.L_le)) false 1 := by
    rw [eZL]
    exact S46.isSumOfNaturalModulesVia_restrict
      (S46.isSumOfNaturalModulesVia_of_imM h.le le_rfl hUM bot_le hstab hUl.symm hbot hU₀) h.L_le
  have hN2 := S46.isSumOfNaturalModulesVia_restrict
    (S46.isSumOfNaturalModulesVia_of_imM h.le le_rfl hA₃M hZVM hstab eA₃ eZ h₁) h.L_le
  have hN3 := S46.isSumOfNaturalModulesVia_restrict
    (S46.isSumOfNaturalModulesVia_of_imM h.le le_rfl hA₄M hA₃M hstab eA₄ eA₃ h₂) h.L_le
  have hN4 := S46.isSumOfNaturalModulesVia_restrict
    (S46.isSumOfNaturalModulesVia_of_imM h.le le_rfl hVM hA₄M hstab hV.symm eA₄ h₃) h.L_le
  have hVO : V ≤ pCoreOf 2 L := commutator_le_pCoreOf h.L_le h.le_normalizer
  have hVL : V ≤ L := hVO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hLZ : L ≤ Subgroup.normalizer (centerOf V : Set G) :=
    h.L_le.trans (le_normalizer_centerOf_Vq h)
  have hWZ : ⁅centerOf V, L⁆ ≤ centerOf V := commutator_le_left_of_le_normalizer hLZ
  have hchief : IsChiefSeriesFrom L V V 6 :=
    burnsideC134w_chief_six hVL hVO le_rfl hαs hN1 hWZ hLZ le_rfl hN2 hN3 hN4
  refine ⟨n, F, inferInstance, inferInstance, _, hn, hαs, ?_, ?_, hN1, hchief, ?_, ?_,
    A₃, A₄, hN2, hN3, hN4⟩
  · rw [eZL, sup_comm]
    exact hZs
  · rw [eZL, inf_comm]
    exact hUH
  · rw [hZs, ← hn]
    exact qjInfo_sup_of_le_centralizer (S46.qjInfo_of_card h hφ hT hU) h.le hUM
      (hHpZ.trans hZM) hUH hUc
  ·
    intro hb
    apply hH1
    have h0 : imM h.le (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
      rw [hb]
      exact hbot
    rw [eCL] at h0
    exact eq_bot_iff.mpr (hHV.trans h0.le)


end BaseA

@[expose] def burnsideC134w_S45WX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) → IsSL3Full M T L →
      burnsideC134w_MS93Case13WX (Vq M L) T L

theorem burnsideC134w_s45WX_of (h43 : S43) (h44 : S44) (h14 : MS14AS) (hSQ : SQTKQuot)
    (hQ2a : S45Q2a) : burnsideC134w_S45WX := by
  intro G _ _ M T L h hmin hb hfull
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have c : Ctx M T L φ := Ctx.ofItems h43 h44 h hmin hb hφ
  have hZV : c.HZV := by
    by_cases hq : Fintype.card F = 2
    · exact hQ2a G M T L F φ c hq
    · exact c.hZV_of_ne_two hq
  obtain ⟨p, hp⟩ := c.exists_isGoodPath_of_ctx 28
  have hα := c.isMVtx_of_isGoodPath hp (k := 34) (by omega) (by decide)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hα (isMVtx_baseA _)
  obtain ⟨ψ₀, hψ₀, hU₀, hHZ, hF3, hZL, h₁, h₂, h₃⟩ :=
    burnsideC134w_exists_case13W_of_isGoodPath c h14 hSQ hZV (hp.smul g) (by omega) hg
  obtain ⟨hHV, hH1⟩ := burnsideC134w_hloc_facts c hZV (hp.smul g) (by omega) hg
  have hab := adj_baseA_baseB (puAmalgam h.le)
  have hA := isMVtx_baseA (puAmalgam h.le)
  have hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2 := by
    have := c.relIndex_qv hA hab
    rwa [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, puAmalgam.qv_baseB,
      S46.relIndex_imM h.le h.le] at this
  have hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) =
      Fintype.card F := by
    have := c.relIndex_zh hA hab
    rwa [puAmalgam.zh_baseB, puAmalgam.zm_baseA, S46.relIndex_imM h.le (normalClosureIn_le _ _),
      ← S46.relIndex_Uq_inf_centralizer h hφ] at this
  exact burnsideC134w_case13WX_of_baseA h hφ hT hU hψ₀ hU₀ hHZ hF3 hZL h₁ h₂ h₃ hHV hH1

@[expose] def burnsideC134w_ConclWX {G : Type} [Group G] (M T L : Subgroup G) : Prop :=
  MS93ConclAS M T L ∨ (Xq M ≤ Zq M L ⊔ Uq M T L ∧ burnsideC134w_MS93Case13WX (Vq M L) T L)

section Assembly

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideC134w_conclWX_of_endConcl (h38 : S38) (h45 : burnsideC134w_S45WX)
    (h46 : MRes.S46Two) (h512 : S512) (h7 : S7Two) (h : PUHyp M T L) (hL : MRes.NotSL3Big L)
    (hb : 2 < critDist (puAmalgam h.le)) (he : S34D.EndConcl T L) :
    burnsideC134w_ConclWX M T L := by
  obtain ⟨M₁, T₁, h₁, hT₁T, hmin₁, hor⟩ := he
  have hV₁ : Vq M₁ L = Vq M L := h.vq_eq_vq h₁
  have hpos₁ := h₁.critDist_pos
  obtain ⟨m, hm⟩ := h₁.critDist_even
  by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
  · have h5 := h7 G M T L M₁ T₁ h h₁ hT₁T hmin₁ hV₁ hb hb₁
    have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
      rcases h38 G M T L h hb with hSL | hSp
      · exact hSL.1.le
      · exact (case5_sp4U_false h h5 hSp).elim
    exact Or.inl (MS93ConclAS.of_case5 hX h5)
  have hgood := hor.resolve_left hb₁
  have hb₁' : 2 < critDist (puAmalgam h₁.le) := by omega
  rcases h38 G M₁ T₁ L h₁ hb₁' with hSL₁ | hSp₁
  swap
  · exact (h512 G M₁ T₁ L h₁ hmin₁ hb₁' (hgood.2 hSp₁)).elim
  have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
    rcases h38 G M T L h hb with hSL | hSp
    · exact hSL.1.le
    · exact (sl3U_sp4U_false h h₁ hSL₁ hSp).elim
  have hFull := hgood.1 hSL₁
  rcases (show critDist (puAmalgam h₁.le) = 4 ∨ 4 < critDist (puAmalgam h₁.le) by omega)
    with h4 | h4
  · have h11 := h46 G M₁ T₁ L h₁ hmin₁ h4 hFull hL
    rw [hV₁] at h11
    exact Or.inl (MS93ConclAS.of_case11 hX (h11.mono hT₁T))
  · have h13 := h45 G M₁ T₁ L h₁ hmin₁ h4 hFull
    rw [hV₁] at h13
    exact Or.inr ⟨hX, h13.mono hT₁T⟩

end Assembly

@[expose] def burnsideC134w_MS93ASOrdWX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G), PUHyp M T L → MRes.NotSL3Big L →
    MRes.NoSp4Quot L → burnsideC134w_ConclWX M T L

theorem burnsideC134w_ms93ASOrdWX_of (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18)
    (h38 : S38) (h45 : burnsideC134w_S45WX) (h46 : MRes.S46Two) (h512 : S512) (h7 : S7Two)
    (hred : PUReduce) : burnsideC134w_MS93ASOrdWX := by
  intro G _ _ M T L h hL hS
  by_cases hb : critDist (puAmalgam h.le) = 2
  · exact Or.inl (ms93ConclAS_of_critDist_eq_two h32 h36 h37 h18 h hb)
  · have hpos := h.critDist_pos
    obtain ⟨m, hm⟩ := h.critDist_even
    exact burnsideC134w_conclWX_of_endConcl h38 h45 h46 h512 h7 h hL (by omega)
      (MRes.endConcl_of_noSp4 hred hL hS h)

section C134

variable {G : Type} [Group G] [Finite G]

theorem burnsideC134w_case4Min_of_case13WX {G₀ R L : Subgroup G} (h : PUHyp G₀ R L)
    (hX : Xq G₀ ≤ Zq G₀ L ⊔ Uq G₀ R L)
    (h13 : burnsideC134w_MS93Case13WX (Vq G₀ L) R L) : C134Case4Min G₀ R L := by
  have hNC := burnsideC134w_notCentralizerCore_of_case13W h hX h13.toW
  obtain ⟨n, F, _, _, α, hF, hα, hZeq, hdisj, hU, -, -, hC, A₃, A₄, h₁, h₂, h₃⟩ := h13
  exact ⟨⟨n, F, inferInstance, inferInstance, α, hF, MRes.isModO2Surj_of_surjective h hF hα,
    hZeq, hdisj, hU, ⟨A₃, A₄, h₁, h₂, h₃⟩, hC⟩, hNC⟩

end C134

theorem c134L32CorrM_of_ms93ASOrdWX_of_simple
    (hS : RankTwoLieSimple)
    (hms : burnsideC134w_MS93ASOrdWX) : C134L32CorrM := by
  intro G _ _ G₀ R L hMS hL hG hsl3
  obtain ⟨F, _, _, α, hF2, hα⟩ := hsl3
  have hF : Fintype.card F = 2 ^ 1 := by rw [hF2, pow_one]
  have h := puHyp_of_msPair_of_simple hS hMS hL hG
  rcases hms G G₀ R L h (MRes.notSL3Big_of_isModO2Surj_two hF2 hα)
      (MRes.noSp4Quot_of_isModO2Surj_two hF2 hα) with hc | ⟨hX13, h13⟩
  · obtain ⟨i, hi⟩ := burnsideC134w_caseCorr_of_conclAS hMS hL hG h hF hα hc
    exact ⟨i, IsC134CaseM.of_corr hi⟩
  · exact ⟨4, burnsideC134w_case4Min_of_case13WX h hX13 h13⟩

section Holds

set_option linter.unusedSectionVars false


theorem burnsideC134w_ms93ASOrdWX_holds
    : burnsideC134w_MS93ASOrdWX :=
  have h441 := s441_holds
  have h44 :=
    s44_frontier h441 (S4A.s442_of_s441 ms14AS_holds sqtkQuot_holds s32_holds s43_holds h441)
  burnsideC134w_ms93ASOrdWX_of s32_holds (s36_of_g2 s38G2_holds) s37_holds s18_holds
    (s38_of_g2 s38G2_holds)
    (burnsideC134w_s45WX_of s43_holds h44 ms14AS_holds sqtkQuot_holds S45J.s45Q2a_holds)
    (MRes.s46Two_of s32_holds (s39_of s32_holds) (s42_of s32_holds) s43_holds ms14AS_holds
      sqtkQuot_holds)
    s512_holds (s7two_of s32_holds (s36_of_g2 s38G2_holds) s18_holds) puReduce_holds

theorem c134L32CorrM_holds
    : C134L32CorrM :=
  c134L32CorrM_of_ms93ASOrdWX_of_simple rankTwoLieSimple_holds
    burnsideC134w_ms93ASOrdWX_holds

end Holds

end CFSG.Quasithin.MS93
