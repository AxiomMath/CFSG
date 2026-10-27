module

public import CFSG.Quasithin.MS93.S33Crit
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem commutator_le_of_le {H K : Subgroup G} (hH : H ≤ M) (hK : K ≤ M) : ⁅H, K⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (hH hx) (hK hy)) (inv_mem (hH hx))) (inv_mem (hK hy))

theorem s33i_of_sl3 (h : PUHyp M T L) (hU : IsSL3U M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') {Y : Subgroup (puAmalgam h.le).Universal}
    (hY : Y ≤ Qv _ (geo _ α' (baseA _) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal))
    (hn : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤ critR (puAmalgam h.le) (baseA _) α') :
    S33i h α' Y := by
  obtain ⟨hX, hZU, n, F, _, _, a, hcard, ha, hnat⟩ := hU
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hnat
  refine ⟨n, F, inferInstance, inferInstance, a, hcard, ha, hnat, hX, hZU, ?_⟩
  have hb := h.critDist_pos
  have h20 := h.hyp20
  have hC := h.centHyp
  obtain ⟨k, hkα, hkβ, hcμ, hμβ⟩ := exists_conj_of_isCritical _ h20 hb hc
  set μ := k⁻¹ • baseA (puAmalgam h.le) with hμ
  have hcinj : Function.Injective (MulAut.conj k⁻¹).toMonoidHom := (MulAut.conj k⁻¹).injective
  have hZμ : (ZM _ (baseA _)).map (MulAut.conj k⁻¹).toMonoidHom = ZM (puAmalgam h.le) μ :=
    (zm_smul _ k⁻¹ _).symm
  have hZα' : (ZM _ α').map (MulAut.conj k⁻¹).toMonoidHom = ZM (puAmalgam h.le) (baseA _) := by
    rw [← zm_smul, ← hkα, inv_smul_smul]
  have hQγ : (Qv _ (geo _ α' (baseA _) 1)).map (MulAut.conj k⁻¹).toMonoidHom =
      Qv (puAmalgam h.le) (baseB _) := by
    rw [← qv_smul, ← hkβ, inv_smul_smul]
  have hQα' : (Qv _ α').map (MulAut.conj k⁻¹).toMonoidHom = Qv (puAmalgam h.le) (baseA _) := by
    rw [← qv_smul, ← hkα, inv_smul_smul]
  have hRc : (critR _ (baseA _) α').map (MulAut.conj k⁻¹).toMonoidHom =
      ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (baseA _)⁆ := by
    rw [critR, Subgroup.map_commutator, hZμ, hZα']
  have hdμ : (puAmalgam h.le).treeGraph.dist μ (baseA _) = critDist (puAmalgam h.le) := hcμ.2.1
  have hZμT : ZM (puAmalgam h.le) μ ≤ Qv _ (baseB _) := by
    refine zm_le_qv_of_dist_lt _ hcμ.1 ?_
    rw [← hμβ, SimpleGraph.dist_comm,
      dist_geo_right _ (by rw [SimpleGraph.dist_comm, hdμ]; exact hb), SimpleGraph.dist_comm, hdμ]
    omega
  have hβT : Qv (puAmalgam h.le) (baseB _) = imM h.le T := puAmalgam.qv_baseB h.le
  have hTM' : imM h.le T ≤ imM h.le M := imM_mono h.le h.le
  set E := pre h.le (ZM (puAmalgam h.le) μ) with hEdef
  set Yp := pre h.le (Y.map (MulAut.conj k⁻¹).toMonoidHom) with hYpdef
  have hEim : imM h.le E = ZM (puAmalgam h.le) μ :=
    imM_pre h.le (hZμT.trans (hβT ▸ hTM'))
  have hY' : Y.map (MulAut.conj k⁻¹).toMonoidHom ≤ imM h.le T := by
    rw [← hβT, ← hQγ]
    exact Subgroup.map_mono hY
  have hYim : imM h.le Yp = Y.map (MulAut.conj k⁻¹).toMonoidHom := imM_pre h.le (hY'.trans hTM')
  have hET : E ≤ T := by
    rw [← imM_le_imM_iff h.le (pre_le h.le _), hEim, ← hβT]
    exact hZμT
  have hYT : Yp ≤ T := by
    rw [← imM_le_imM_iff h.le (pre_le h.le _), hYim]
    exact hY'
  have hZim : imM h.le (Z0q M T) = ZM (puAmalgam h.le) (baseA _) :=
    (puAmalgam.zm_baseA h.le).symm
  have hRM : ⁅E, Z0q M T⁆ ≤ M := commutator_le_of_le (pre_le h.le _) (Z0q_le M T)
  have hRim : imM h.le ⁅E, Z0q M T⁆ = ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (baseA _)⁆ := by
    rw [imM_commutator h.le (pre_le h.le _) (Z0q_le M T), hEim, hZim]
  have hRU : ⁅E, Z0q M T⁆ = ⁅Uq M T L, E⁆ := by
    rw [Subgroup.commutator_comm, commutator_Z0q_eq h hET]
  have hZn : ZM (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) μ : Set (puAmalgam h.le).Universal) := by
    have hd1 : 0 < (puAmalgam h.le).treeGraph.dist μ (baseA _) := by rw [hdμ]; exact hb
    have hadj : (puAmalgam h.le).treeGraph.Adj μ (geo _ μ (baseA _) 1) := adj_geo_one _ hd1
    refine le_trans ?_ ((qv_le_stab_of_adj _ hadj.symm).trans (stab_le_normalizer_zm _ μ))
    refine zm_le_qv_of_dist_lt _ (PU.isMVtx_baseA _) ?_
    rw [SimpleGraph.dist_comm, dist_geo_right _ (show 1 ≤ _ from hd1), hdμ]
    omega
  have hRE : ⁅E, Z0q M T⁆ ≤ E := by
    rw [← imM_le_imM_iff h.le hRM, hRim, hEim]
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hZn
  have hUE : ⁅Uq M T L, E⁆ ≤ E := hRU ▸ hRE
  have hEA := isElemAbelian_zm _ h20 hb hcμ.1
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x :=
    pre_comm h.le (isMulCommutative_subgroup_iff.mp hEA.1)
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := pre_sq h.le hEA.2
  have hRne : ⁅Uq M T L, E⁆ ≠ ⊥ := by
    intro hbot
    apply ms22_ii _ h20 hb hC hcμ
    rw [← hRim, hRU, hbot]
    simp [imM]
  have hYR' : Yp ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) := by
    rw [← hRU]
    refine pre_le_centralizer h.le hRM ?_
    rw [hRim, ← hRc, ← centralizer_map_mulEquiv]
    exact Subgroup.map_mono hYR
  have hYn : ¬ ⁅Uq M T L, Yp⁆ ≤ ⁅Uq M T L, E⁆ := by
    intro hle
    apply hn
    rw [← Subgroup.map_le_map_iff_of_injective hcinj, Subgroup.map_commutator, hZα', hRc,
      ← hRim, ← hZim, ← hYim, ← imM_commutator h.le (Z0q_le M T) (pre_le h.le _)]
    refine imM_mono h.le ?_
    rw [commutator_Z0q_eq h hYT, hRU]
    exact hle
  have hlin : ∀ e ∈ E, ∀ f : (Fin 3 → F) → (Fin 3 → F), IsCoordAct β e f →
      ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hF2 : Fintype.card F = 2 := by
        have h1 : 1 < Fintype.card F := Fintype.one_lt_card
        interval_cases n
        · simp at hcard; omega
        · simpa using hcard
      intro e he f hf c x
      have hf0 : f 0 = 0 := by
        have := hf 1 1 (by simp)
        simpa using this.symm
      rcases eq_zero_or_eq_one_of_card_eq_two hF2 c with rfl | rfl
      · rw [zero_smul, zero_smul, hf0]
      · rw [one_smul, one_smul]
    · have hF4 : 4 ≤ Fintype.card F := by
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      by_contra hnl
      apply relIndex_qv_zm_ne_two h ha hβ hβker hβα hF4 hc
      rw [← Subgroup.relIndex_map_map_of_injective _ _ hcinj, hQα', hZμ, ← hEim,
        puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
        relIndex_imM h.le (pre_le h.le _)]
      refine relIndex_eq_two_of_nonlinear h ha hβ hβker hβα hcard hET hEab hE2 hUE ?_
      by_contra hall
      apply hnl
      intro e he f hf
      by_contra hne
      exact hall ⟨e, he, f, hf, hne⟩
  have hcardR := card_commutator_Uq h ha hβ hβker hβα hcard hET hYT hlin hRne hYR' hYn
  have hEc : E ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun r hr => hEab r (hUE hr) e he
  have hrel := relIndex_commutator_Uq h ha hβ hβker hβα hcard hET hYT hlin hEc hYR' hYn hcardR
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hcinj, hRc, ← hRim, card_imM h.le hRM, hRU]
    exact hcardR
  · have hKT : Yp ⊔ E ≤ T := sup_le hYT hET
    have hKM : ⁅Yp ⊔ E, Z0q M T⁆ ≤ M :=
      commutator_le_of_le (sup_le (pre_le h.le _) (pre_le h.le _)) (Z0q_le M T)
    rw [← Subgroup.relIndex_map_map_of_injective _ _ hcinj, hRc, ← hRim, Subgroup.map_commutator,
      Subgroup.map_sup, hZμ, hZα', ← hYim, ← hEim, ← hZim,
      ← imM_sup h.le (pre_le h.le _) (pre_le h.le _),
      ← imM_commutator h.le (sup_le (pre_le h.le _) (pre_le h.le _)) (Z0q_le M T),
      relIndex_imM h.le hKM, hRU, Subgroup.commutator_comm (Yp ⊔ E) (Z0q M T),
      commutator_Z0q_eq h hKT]
    exact hrel

end CFSG.Quasithin.MS93.S33
