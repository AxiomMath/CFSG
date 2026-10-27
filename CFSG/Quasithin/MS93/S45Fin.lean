module

public import CFSG.Quasithin.MS93.S45Z
public import CFSG.Quasithin.MS93.S45Q4PD
public import CFSG.Quasithin.MS93.S45Y2

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

theorem Ctx.ofItems (h43 : S43) (h44 : S44) {M T L : Subgroup G} (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) : Ctx M T L φ := by
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨hb8, hc1, -, hstr, h444⟩ :=
    h44 G M T L h hmin hb F inferInstance inferInstance φ hφ
  exact
    { hyp := h
      min := hmin
      via := hφ
      cent := S46.centHyp_of_gen23 h hfull
      b8 := hb8
      c1 := hc1
      c444 := h444
      exStr := hstr
      s43 := fun α α' hc => h43 G M T L h hmin (by omega) hfull α α' hc }

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem exists_case13_of_isGoodPath (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    (hQ2b : c.HQ2b) {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N)
    (hN : 64 ≤ N) {δ : Vtx (puAmalgam c.hyp.le)} (hδ : p 34 = δ) :
    ∃ ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1 ∧
      Nat.card ↥(Hloc c.hyp.le L δ) = Fintype.card F ^ 2 ∧
      ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓
          Subgroup.centralizer (Ltil c.hyp.le L δ : Set _) = Hloc c.hyp.le L δ ∧
      centerOf ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ =
        Uloc c.hyp.le L δ ⊔ Hloc c.hyp.le L δ ∧
      ⁅centerOf ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆, Ltil c.hyp.le L δ⁆ =
        Uloc c.hyp.le L δ ∧
      IsSumOfNaturalModulesVia (stab _ δ)
        (frattiniIn ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆)
        (centerOf ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆) ψ true 1 ∧
      IsSumOfNaturalModulesVia (stab _ δ)
        (⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓ Subgroup.centralizer
          (frattiniIn ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ : Set _))
        (frattiniIn ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆) ψ true 2 ∧
      IsSumOfNaturalModulesVia (stab _ δ) ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆
        (⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓ Subgroup.centralizer
          (frattiniIn ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ : Set _)) ψ false 2 := by
  subst hδ
  have hα := c.isMVtx_of_isGoodPath hp (k := 34) (by omega) (by decide)
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα (hp.adj 34 (by omega))
  exact ⟨ψ, hψs, hψ, c.card_hloc hp (x := 28) (by decide) (by omega) (by omega),
    c.case13_vertex h14 hSQ hZV (S45Q4.hQ4 c) hQ2b hp (a := 34) (by decide) le_rfl (by omega)
      hψs hψ hT⟩

end Ctx

section BaseA

variable {M T L : Subgroup G}

theorem case13_of_baseA (h : PUHyp M T L) {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) (hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2)
    (hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) = Fintype.card F)
    {ψ₀ : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSL 3 F)} (hψ₀ : Function.Surjective ψ₀)
    (hU₀ : IsSumOfNaturalModulesVia (stab _ (baseA _)) (Uloc h.le L (baseA _)) ⊥ ψ₀ false 1)
    (hHc : Nat.card ↥(Hloc h.le L (baseA _)) = Fintype.card F ^ 2)
    (hHZ : Hloc h.le L (baseA _) ≤ Zloc h.le L (baseA _))
    (hF4 : ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓
      Subgroup.centralizer (Ltil h.le L (baseA _) : Set _) = Hloc h.le L (baseA _))
    (hF3 : centerOf ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ =
      Uloc h.le L (baseA _) ⊔ Hloc h.le L (baseA _))
    (hZL : ⁅centerOf ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆,
      Ltil h.le L (baseA _)⁆ = Uloc h.le L (baseA _))
    (h₁ : IsSumOfNaturalModulesVia (stab _ (baseA _))
      (frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆)
      (centerOf ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆) ψ₀ true 1)
    (h₂ : IsSumOfNaturalModulesVia (stab _ (baseA _))
      (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓ Subgroup.centralizer
        (frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ : Set _))
      (frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆) ψ₀ true 2)
    (h₃ : IsSumOfNaturalModulesVia (stab _ (baseA _))
      ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆
      (⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓ Subgroup.centralizer
        (frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ : Set _)) ψ₀ false 2) :
    MS93Case13 (Vq M L) T L := by
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
  set V := Vq M L with hVdef
  have hΦM : frattiniIn V ≤ M := (Subgroup.map_subtype_le _).trans hVM
  have hZVM : centerOf V ≤ M := inf_le_left.trans hVM
  have hCM : V ⊓ Subgroup.centralizer (frattiniIn V : Set G) ≤ M := inf_le_left.trans hVM
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
  have eΦ : imM h.le (frattiniIn V) =
      frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ := by
    rw [imM_frattiniIn h.le hVM, hV]
  have eC : imM h.le (V ⊓ Subgroup.centralizer (frattiniIn V : Set G)) =
      ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ ⊓ Subgroup.centralizer
        (frattiniIn ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ : Set _) := by
    rw [imM_inf_centralizer h.le V hΦM, eΦ, hV]
  have eCL : imM h.le (V ⊓ Subgroup.centralizer (L : Set G)) = Hloc h.le L (baseA _) := by
    rw [imM_inf_centralizer h.le V h.L_le, ← hV, ← hLt, hF4]
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
  refine ⟨n, F, inferInstance, inferInstance,
    (ψ₀.comp ((S46.imMEquiv h.le le_rfl).trans (MulEquiv.subgroupCongr hstab)).toMonoidHom).comp
      (Subgroup.inclusion h.L_le), hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hψ y
    exact ⟨⟨ℓ, hℓL⟩, hℓ⟩
  · rw [← card_imM h.le hCLM, eCL, hHc, hn]
  · exact isElemAbelian_of_le h.isElemAbelian_Xq (hHpZ.trans inf_le_left)
  · rw [eZL, sup_comm]
    exact hZs
  · rw [eZL, inf_comm]
    exact hUH
  · rw [eZL]
    exact S46.isSumOfNaturalModulesVia_restrict
      (S46.isSumOfNaturalModulesVia_of_imM h.le le_rfl hUM bot_le hstab hUl.symm hbot hU₀) h.L_le
  · exact S46.isSumOfNaturalModulesVia_restrict
      (S46.isSumOfNaturalModulesVia_of_imM h.le le_rfl hΦM hZVM hstab eΦ eZ h₁) h.L_le
  · exact S46.isSumOfNaturalModulesVia_restrict
      (S46.isSumOfNaturalModulesVia_of_imM h.le le_rfl hCM hΦM hstab eC eΦ h₂) h.L_le
  · exact S46.isSumOfNaturalModulesVia_restrict
      (S46.isSumOfNaturalModulesVia_of_imM h.le le_rfl hVM hCM hstab hV.symm eC h₃) h.L_le
  · rw [hZs, ← hn]
    exact qjInfo_sup_of_le_centralizer (S46.qjInfo_of_card h hφ hT hU) h.le hUM
      (hHpZ.trans hZM) hUH hUc

end BaseA

end CFSG.Quasithin.MS93.S45
