module

public import CFSG.Milestones.ASVolI.C135.WVtx
public import CFSG.Milestones.ASVolI.C135.Eta
public import CFSG.Quasithin.MS93.ASC134NC
public import CFSG.Quasithin.MS93.S45Fin
public import CFSG.Quasithin.MS93.S46End
public import CFSG.Quasithin.MS93.SkAssembly

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement Matrix

section Def

variable {G : Type} [Group G]

@[expose] def burnsideC134w_MS93Case13W (V T L : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
    Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
    centerOf V = V ⊓ Subgroup.centralizer (L : Set G) ⊔ ⁅centerOf V, L⁆ ∧
    V ⊓ Subgroup.centralizer (L : Set G) ⊓ ⁅centerOf V, L⁆ = ⊥ ∧
    IsSumOfNaturalModulesVia L ⁅centerOf V, L⁆ ⊥ α false 1 ∧
    IsChiefSeriesFrom L V V 6 ∧
    QjInfo T L (centerOf V) (2 ^ n)

theorem burnsideC134w_MS93Case13W.mono {V T T₁ L : Subgroup G}
    (h : burnsideC134w_MS93Case13W V T₁ L) (hT : T₁ ≤ T) : burnsideC134w_MS93Case13W V T L := by
  obtain ⟨n, F, hF, hFt, α, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨n, F, hF, hFt, α, h1, h2, h3, h4, h5, h6, h7.mono hT⟩

end Def

section Count

variable {G : Type} [Group G] [Finite G]

theorem burnsideC134w_chief_six {L U Q W Z A₃ A₄ : Subgroup G} (hUL : U ≤ L)
    (hUO : U ≤ pCoreOf 2 L) (hQU : Q ≤ U) {F : Type} [Field F] {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) (h1 : IsSumOfNaturalModulesVia L W ⊥ α false 1)
    (hWZ : W ≤ Z) (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (hZc : ⁅Z, L⁆ ≤ W)
    (h2 : IsSumOfNaturalModulesVia L A₃ Z α true 1)
    (h3 : IsSumOfNaturalModulesVia L A₄ A₃ α true 2)
    (h4 : IsSumOfNaturalModulesVia L Q A₄ α false 2) :
    IsChiefSeriesFrom L U Q 6 := by
  have hA₄Q : A₄ ≤ Q := h4.2.1
  have hA₃A₄ : A₃ ≤ A₄ := h3.2.1
  have hZA₃ : Z ≤ A₃ := h2.2.1
  have hZU : Z ≤ U := hZA₃.trans (hA₃A₄.trans (hA₄Q.trans hQU))
  have e1 := F112W.isChiefSeriesFrom_of_between_bot
    (ASVolI.burnsideC135_isChiefSeriesBetween_of_sum hα h1 (hWZ.trans hZU))
  have e0 : F112W.IsChiefSeriesBetween L U W Z 0 := by
    refine (F112W.isChiefSeriesBetween_zero_iff hUL hUO
      (F112W.isNormalIn_of_le_normalizer (hWZ.trans hZU) h1.1)
      (F112W.isNormalIn_of_le_normalizer hZU hLZ) hWZ).mpr ?_
    exact (Subgroup.commutator_mono le_rfl (oTwoUpper_le L)).trans hZc
  have e2 := (ASVolI.burnsideC135_isChiefSeriesBetween_of_sum hα h2
    (hA₃A₄.trans (hA₄Q.trans hQU))).append (e0.append e1)
  have e3 := (ASVolI.burnsideC135_isChiefSeriesBetween_of_sum hα h3 (hA₄Q.trans hQU)).append e2
  exact (ASVolI.burnsideC135_isChiefSeriesBetween_of_sum hα h4 hQU).append e3

end Count

section BaseA

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F] {M T L : Subgroup G}

theorem burnsideC134w_case13W_of_baseA (h : PUHyp M T L) {φ : ↥M →* ↥(StatedSL 3 F)}
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
        Subgroup.centralizer (Vcirc h.le L (baseA _) : Set _)) ψ₀ false 2) :
    burnsideC134w_MS93Case13W (Vq M L) T L := by
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
  refine ⟨n, F, inferInstance, inferInstance, _, hn, hαs, ?_, ?_, hN1, hchief, ?_⟩
  · rw [eZL, sup_comm]
    exact hZs
  · rw [eZL, inf_comm]
    exact hUH
  · rw [hZs, ← hn]
    exact qjInfo_sup_of_le_centralizer (S46.qjInfo_of_card h hφ hT hU) h.le hUM
      (hHpZ.trans hZM) hUH hUc

end BaseA

@[expose] def burnsideC134w_S45W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) → IsSL3Full M T L →
      burnsideC134w_MS93Case13W (Vq M L) T L

theorem burnsideC134w_s45W_of (h43 : S43) (h44 : S44) (h14 : MS14AS) (hSQ : SQTKQuot)
    (hQ2a : S45Q2a) : burnsideC134w_S45W := by
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
  exact burnsideC134w_case13W_of_baseA h hφ hT hU hψ₀ hU₀ hHZ hF3 hZL h₁ h₂ h₃

end CFSG.Quasithin.MS93
