module

public import CFSG.Quasithin.MS93.S34ECrit
public import CFSG.Quasithin.MS93.S4ASL3
import CFSG.Quasithin.MS93.S33SpLin

public section

namespace CFSG.Quasithin.MS93.S34F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem flat_subgroupOf_normal (h : PUHyp M T L) :
    ((L ⊔ pCoreOf 2 M).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le h.L_le (pCoreOf_le' M))).2
    (le_normalizer_sup h.le_normalizer (le_normalizer_pCoreOf M))

theorem pCoreOf_le_centralizer_Uq (h : PUHyp M T L) :
    pCoreOf 2 M ≤ Subgroup.centralizer (Uq M T L : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp
    (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ (h.Uq_le_Xq hu))) t ht).symm

theorem exists_natural_flat (h : PUHyp M T L) (hU : IsSL3U M T L) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSL 3 F)), Fintype.card F = 2 ^ n ∧
      Function.Surjective φ ∧
      IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) ⊥ φ false 1 := by
  obtain ⟨-, -, n, F, _, _, a, hcard, ha, hLV, hZV, β, hβ, hβker, hβα⟩ := hU
  have hQV : pCoreOf 2 M ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (pCoreOf_le' M).trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨φ, hφ, hnat⟩ := exists_natural_of_coordAct (Γ := StatedSL 3 F) (A := L)
    (M := L ⊔ pCoreOf 2 M) (T := pCoreOf 2 M) rfl ha hLV hZV hβ hβker hβα hQV fun t ht =>
      ⟨1, (S33.isCoordAct_id_of_le_centralizer (pCoreOf_le_centralizer_Uq h ht)).congr
        fun x => by simp⟩
  exact ⟨n, F, inferInstance, inferInstance, φ, hcard, hφ, hnat⟩

noncomputable abbrev flat (h : PUHyp M T L) (δ : Vtx (puAmalgam h.le)) :
    Subgroup (puAmalgam h.le).Universal :=
  puTrans h.le (L ⊔ pCoreOf 2 M) δ

theorem exists_natural_flat_at (h : PUHyp M T L) {F : Type} [Field F]
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSL 3 F)} (hφs : Function.Surjective φ)
    (hnat : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) ⊥ φ false 1)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    ∃ ψ : ↥(flat h δ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (flat h δ) (Uloc h.le L δ) ⊥ ψ false 1 := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hn : ((Uq M T L).subgroupOf M).Normal := S33.uq_subgroupOf_normal h
  set e : ↥M →* (puAmalgam h.le).Universal :=
    (MulAut.conj g).toMonoidHom.comp (puAmalgam h.le).ofA with he
  have hei : Function.Injective e :=
    (MulAut.conj g).injective.comp (puAmalgam h.le).ofA_injective
  have h1 := isSumOfNaturalModulesVia_map
    (isSumOfNaturalModulesVia_subgroupOf hnat hKM hUM) e hei
  have hK : flat h (g • baseA _) = ((L ⊔ pCoreOf 2 M).subgroupOf M).map e := by
    rw [flat, puTrans_smul_baseA (flat_subgroupOf_normal h), imM, Subgroup.map_map]
  have hU : Uloc h.le L (g • baseA _) = ((Uq M T L).subgroupOf M).map e := by
    rw [Uloc, puTrans_smul_baseA hn, imM, Subgroup.map_map]
  have hbot : ((⊥ : Subgroup G).subgroupOf M).map e = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h1
  refine ⟨_, ?_, isSumOfNaturalModulesVia_of_equiv h1 (MulEquiv.subgroupCongr hK)
    (MulEquiv.subgroupCongr hU) ((puTrans_le_stab h.le _ _).trans
      (stab_le_normalizer_puTrans h.le hn _)) bot_le (fun v => Iff.rfl) (fun a u v huv => huv)⟩
  exact (hφs.comp (MulEquiv.surjective _)).comp ((MulEquiv.surjective _).comp
    (MulEquiv.surjective _))

theorem pre_zm_le_flat (h : PUHyp M T L) (hU : IsSL3U M T L) {μ : Vtx (puAmalgam h.le)}
    (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo _ (baseA (puAmalgam h.le)) μ 1 = baseB _) :
    S33.pre h.le (ZM _ μ) ≤ L ⊔ pCoreOf 2 M := by
  obtain ⟨-, -, n, F, _, _, a, hcard, ha, -, -, β, hβ, hβker, hβα⟩ := hU
  obtain ⟨hEab, hE2, hUE, -, hEim⟩ := S33.pre_zm_props h hcμ
  have hET := (S34E.pre_zm_le_not_le h hcμ hμβ).1
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  intro e heE
  have heV := hTV (hET heE)
  obtain ⟨f, hf⟩ := S33.exists_isCoordAct' hβ hβker heV
  have hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hF2 : Fintype.card F = 2 := S34R.card_eq_two_of_lt hcard hn2
      intro c x
      rcases S33.eq_zero_or_eq_one_of_card_eq_two hF2 c with rfl | rfl
      · rw [zero_smul, zero_smul, map_zero]
      · rw [one_smul, one_smul]
    · have hF4 : 4 ≤ Fintype.card F := by
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      by_contra hnl
      apply S33.relIndex_qv_zm_ne_two_gen h
        (fun _ hm hnt => S33.four_le_relIndex_centralizer h ha hβ hβker hβα hF4 hm hnt) hcμ
      rw [← hEim, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
        S33.relIndex_imM h.le (S33.pre_le h.le _)]
      exact S33.relIndex_eq_two_of_nonlinear h ha hβ hβker hβα hcard hET hEab hE2 hUE
        ⟨e, heE, f, hf, hnl⟩
  have hbot : e ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  obtain ⟨γ₀, hγ₀⟩ := S34R.exists_gl_of_linear hβ hβker heV hbot hf hlin
  exact S34D.mem_sup_of_isCoordAct_sl h hcard ha hβ hβker hβα (hET heE) hγ₀

theorem zm_le_flat (h : PUHyp M T L) (hU : IsSL3U M T L) {μ δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ δ) : ZM _ μ ≤ flat h δ := by
  obtain ⟨k, hkα, -, hcμ, hμβ⟩ := S33.exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  obtain ⟨-, -, -, -, hEim⟩ := S33.pre_zm_props h hcμ
  have hZ : ZM (puAmalgam h.le) (k⁻¹ • μ) ≤ flat h (baseA _) := by
    rw [← hEim, flat, puTrans_baseA h.le (flat_subgroupOf_normal h)]
    exact imM_mono h.le (pre_zm_le_flat h hU hcμ hμβ)
  have hZμ : ZM (puAmalgam h.le) μ =
      (ZM (puAmalgam h.le) (k⁻¹ • μ)).map (MulAut.conj k).toMonoidHom := by
    rw [← zm_smul, smul_inv_smul]
  rw [hZμ, ← hkα, flat, puTrans_smul h.le (flat_subgroupOf_normal h)]
  exact Subgroup.map_mono hZ

end CFSG.Quasithin.MS93.S34F
