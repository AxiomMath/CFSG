module

public import CFSG.Quasithin.MS93.S51Par
public import CFSG.Quasithin.MS93.S51Thom
public import CFSG.Quasithin.MS93.S5A54
public import CFSG.Quasithin.MS93.S46Base
public import CFSG.Quasithin.MS93.S4ABasic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S51

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_imSp_eq_xPoint (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {E : Subgroup G} (hET : E ≤ T) (hc : (pCoreOf 2 M).relIndex E = 2 ^ k)
    (hu : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k) :
    ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧ S5.imSp a E = MSP.xPoint p := by
  have := hd.charP
  have hl := (S5.sp4Lift G M T L h k F _ _ a hd).2.2
  have hV := hd.card_eq_mul_relIndex hl (hET.trans h.le)
  have hq := hd.nat_card_eq
  have hq1 : 1 < Nat.card F := S5.one_lt_card_F
  rw [hu, MSP.card_V4, MSP.card_fixSp, ← hq] at hV
  have h3 : Module.finrank F (MSP.fixSp (S5.imSp a E)) = 3 := by
    have h' : Nat.card F ^ 4 = Nat.card F ^ (Module.finrank F (MSP.fixSp (S5.imSp a E)) + 1) := by
      rw [pow_succ]
      exact hV
    have := Nat.pow_right_injective hq1 h'
    omega
  refine MSP.eq_xPoint_of_finrank_fixSp_three h3 ?_
  rw [hd.card_imSp h hET, hc, hq]

omit [Finite G] [Fintype F] in
theorem imSp_sup {E₁ E₂ : Subgroup G} (h₁ : E₁ ≤ M) (h₂ : E₂ ≤ M) :
    S5.imSp a (E₁ ⊔ E₂) = S5.imSp a E₁ ⊔ S5.imSp a E₂ := by
  rw [S5.imSp, S5.imSp, S5.imSp, Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem commutator_le_Z0q_of_xPoint (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {p₁ p₂ : Submodule F (MSP.V4 F)} (hp₁ : MSP.IsPoint p₁) (hp₂ : MSP.IsPoint p₂)
    (hJ : S5.imSp a (S5.jOffM M T L (2 ^ k)) = MSP.xPoint p₁ ⊔ MSP.xPoint p₂) :
    ⁅pCoreOf 2 M, L⁆ ≤ Z0q M T := by
  classical
  have := hd.charP
  have hJT : S5.jOffM M T L (2 ^ k) ≤ T := iSup₂_le fun E hE => hE.1.1
  obtain ⟨-, hthom, hnotQ, hbaum⟩ := thompson_conf hd h hp₁ hp₂ hJ
  have hR : IsPGroup 2 (S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hJT1 : ∀ (b : ↥M →* ↥(StatedSp 2 F)), S5.IsSp4Data M T L k F b →
      S5.imSp b (thompsonJ T) ≠ ⊥ := by
    intro b hb hbot
    apply hnotQ
    intro x hx
    have hxT : x ∈ T := (C1GN.thompsonJ_le T) hx
    have hxk : x ∈ S5.kerG b := by
      refine (S5.mem_kerG b).2 ⟨h.le hxT, ?_⟩
      have : b ⟨x, h.le hxT⟩ ∈ S5.imSp b (thompsonJ T) := S5.mem_imSp.2 ⟨x, hx, h.le hxT, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [← hb.inf_kerG h]
    exact ⟨hxT, hxk⟩
  have hJR : MSP.xPoint p₁ ⊔ MSP.xPoint p₂ ≤ S5.imSp a T := hJ ▸ S5.imSp_mono a hJT
  have hne₀ : MSP.pt₀ F ≠ pE₂ F := by
    intro hpt
    have hm : MSP.e₂ F ∈ MSP.pt₀ F := hpt ▸ Submodule.mem_span_singleton_self _
    have := (MSP.mem_pt₀.1 hm).1
    simp at this
  by_cases he : p₁ = p₂
  ·
    subst he
    obtain ⟨g, hg⟩ := exists_map_pE₂_eq (F := F) hp₁
    have hd' := IsSp4Data.conjA hd g⁻¹
    have hp : p₁.map (Matrix.mulVecLin (MSP.mat g⁻¹)) = pE₂ F := by
      rw [← hg]
      exact MSP.map_map_mat_inv' g _
    have hJ' : S5.imSp (conjA g⁻¹ a) (S5.jOffM M T L (2 ^ k)) = ⊥ ⊔ MSP.xPoint (pE₂ F) := by
      rw [imSp_conjA, hJ, sup_idem, MSP.xPoint_map_conj, hp, bot_sup_eq]
    have hJeq' := (thompson_conf hd' h isPoint_pE₂ isPoint_pE₂
      (by rw [hJ', bot_sup_eq, sup_idem])).1
    have hJeq'' : S5.jOffM M T L (2 ^ k) =
        S5.liftT T (conjA g⁻¹ a) (⊥ ⊔ MSP.xPoint (pE₂ F)) := by
      rw [bot_sup_eq]
      rw [sup_idem] at hJeq'
      exact hJeq'
    refine commutator_le_Z0q_of_conf hd' h (Or.inl rfl) hJ' hJeq'' hthom hbaum ?_
    intro hle
    apply hJT1 _ hd'
    have h1 : S5.imSp (conjA g⁻¹ a) (thompsonJ T) ≤ MSP.xPoint (pE₂ F) := by
      have := S5.imSp_mono (conjA g⁻¹ a) hthom
      rwa [hJ', bot_sup_eq] at this
    have h3 : MSP.X₂ F ⊓ MSP.xPoint (pE₂ F) = ⊥ :=
      S5.xPoint_inf_xPoint MSP.isPoint_pt₀ isPoint_pE₂ hne₀
    rw [← le_bot_iff, ← h3]
    exact le_inf hle h1
  ·
    have hperp : p₂ ≤ MSP.perp p₁ := S5.le_perp_of_xPoint_le hp₁ hp₂ he hR
      (le_sup_left.trans hJR) (le_sup_right.trans hJR)
    have hperp' : p₁ ≤ MSP.perp p₂ := by
      intro x hx
      rw [MSP.mem_perp]
      intro w hw
      rw [MSP.form_swap, neg_eq_zero]
      exact (MSP.mem_perp.1 (hperp hw)) x hx
    have hinf : MSP.xPoint p₁ ⊓ MSP.xPoint p₂ = ⊥ := S5.xPoint_inf_xPoint hp₁ hp₂ he
    obtain ⟨q₁, q₂, hq₁, hq₂, hne, hqperp, hJq, hJTq⟩ : ∃ q₁ q₂ : Submodule F (MSP.V4 F),
        MSP.IsPoint q₁ ∧ MSP.IsPoint q₂ ∧ q₁ ≠ q₂ ∧ q₂ ≤ MSP.perp q₁ ∧
        S5.imSp a (S5.jOffM M T L (2 ^ k)) = MSP.xPoint q₁ ⊔ MSP.xPoint q₂ ∧
        ¬ S5.imSp a (thompsonJ T) ≤ MSP.xPoint q₂ := by
      by_cases h2 : S5.imSp a (thompsonJ T) ≤ MSP.xPoint p₂
      · refine ⟨p₂, p₁, hp₂, hp₁, Ne.symm he, hperp', by rw [hJ, sup_comm], fun h1 => ?_⟩
        apply hJT1 _ hd
        rw [← le_bot_iff, ← hinf]
        exact le_inf h1 h2
      · exact ⟨p₁, p₂, hp₁, hp₂, he, hperp, hJ, h2⟩
    obtain ⟨g, hg₁, hg₂⟩ := exists_map_pE₂_pt₀_eq hq₁ hq₂ hne hqperp
    have hd' := IsSp4Data.conjA hd g⁻¹
    have h1 : q₁.map (Matrix.mulVecLin (MSP.mat g⁻¹)) = pE₂ F := by
      rw [← hg₁]
      exact MSP.map_map_mat_inv' g _
    have h2 : q₂.map (Matrix.mulVecLin (MSP.mat g⁻¹)) = MSP.pt₀ F := by
      rw [← hg₂]
      exact MSP.map_map_mat_inv' g _
    have hJ' : S5.imSp (conjA g⁻¹ a) (S5.jOffM M T L (2 ^ k)) =
        MSP.X₂ F ⊔ MSP.xPoint (pE₂ F) := by
      rw [imSp_conjA, hJq, Subgroup.map_sup, MSP.xPoint_map_conj, MSP.xPoint_map_conj, h1, h2,
        sup_comm]
    have hJeq' := (thompson_conf hd' h MSP.isPoint_pt₀ isPoint_pE₂ hJ').1
    refine commutator_le_Z0q_of_conf hd' h (Or.inr rfl) hJ' hJeq' hthom hbaum ?_
    intro hle
    apply hJTq
    have hX : MSP.X₂ F = (MSP.xPoint q₂).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [MSP.xPoint_map_conj, h2]
    rw [imSp_conjA, hX] at hle
    exact (Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective).1 hle

theorem false_of_commutator_le_Z0q (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hcomm : ⁅pCoreOf 2 M, L⁆ ≤ Z0q M T) : False := by
  have h20 := h.hyp20
  have hβ : ¬ IsMVtx (puAmalgam h.le) (baseB _) := not_isMVtx_baseB _
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hKα : Vv (puAmalgam h.le) (baseB _) ≤ Qv _ (baseA _) :=
    S46.vv_le_qv_of_adj_of_not_isMVtx hb hβ hαβ.symm
  have hKβ : Vv (puAmalgam h.le) (baseB _) ≤ Qv _ (baseB _) := by
    rw [S46.vv_eq_iSup_of_not_isMVtx hβ]
    refine iSup₂_le fun δ hδ => ?_
    have hδM : IsMVtx (puAmalgam h.le) δ := by
      have := isMVtx_iff_of_adj _ hδ
      tauto
    refine zm_le_qv_of_dist_lt _ hδM ?_
    rw [tdist_comm, dist_eq_one_of_adj _ hδ]
    omega
  have hZK : ZM (puAmalgam h.le) (baseA _) ≤ Vv _ (baseB _) :=
    S46.zm_le_vv_of_adj hαβ.symm (isMVtx_baseA _)
  have hM : stab (puAmalgam h.le) (baseA _) = imM h.le L ⊔ imM h.le T := by
    rw [puAmalgam.stab_baseA, ← S5.imM_sup_of_le h h.L_le h.le]
    exact congrArg (imM h.le) h.eq_sup
  have hαN : stab (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (Vv (puAmalgam h.le) (baseB _) : Set (puAmalgam h.le).Universal) := by
    rw [hM]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_normalizer_iff_commutator_le_left]
      calc ⁅Vv (puAmalgam h.le) (baseB _), imM h.le L⁆
          ≤ ⁅Qv (puAmalgam h.le) (baseA _), imM h.le L⁆ := Subgroup.commutator_mono hKα le_rfl
        _ = imM h.le ⁅pCoreOf 2 M, L⁆ := by
          rw [S5.qv_baseA_eq h, imM_commutator h.le (pCoreOf_le' M) h.L_le]
        _ ≤ imM h.le (Z0q M T) := imM_mono h.le hcomm
        _ = ZM (puAmalgam h.le) (baseA _) := (puAmalgam.zm_baseA h.le).symm
        _ ≤ Vv (puAmalgam h.le) (baseB _) := hZK
    · rw [← puAmalgam.qv_baseB h.le]
      exact (qv_le_stab _ (baseB _)).trans (stab_le_normalizer_vv h (baseB _))
  have hbot := ms21_iii _ h20 (isMVtx_baseA _) hαβ hKβ hαN (stab_le_normalizer_vv h (baseB _))
  have hZ : ZH (puAmalgam h.le) (baseB _) ≤ ⊥ := hbot ▸ (zh_le_zm _ hαβ).trans hZK
  exact zh_ne_bot _ h20 hβ (le_bot_iff.mp hZ)

end S51

open S51 in
theorem s51_of (_h32 : S32) : S51 := by
  intro G _ _ M T L h _hmin hb k F _ _ a hd E₁ E₂ hE₁ hE₂ hc₁ hu₁ hc₂ hu₂ hJeq
  rw [puAmalgam.qv_baseB] at hE₁ hE₂
  obtain ⟨E₁', hE₁T, hE₁M, rfl⟩ := S5.exists_eq_imM h.le hE₁
  obtain ⟨E₂', hE₂T, hE₂M, rfl⟩ := S5.exists_eq_imM h.le hE₂
  rw [S5.qv_baseA_eq h, S5.relIndex_imM h.le hE₁M] at hc₁
  rw [S5.qv_baseA_eq h, S5.relIndex_imM h.le hE₂M] at hc₂
  rw [S5.uSub_baseA h, S5.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₁M] at hu₁
  rw [S5.uSub_baseA h, S5.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₂M] at hu₂
  rw [S5.jOff_baseA h, ← S5.imM_sup_of_le h hE₁M hE₂M] at hJeq
  have hJM : S5.jOffM M T L (2 ^ k) ≤ M :=
    (iSup₂_le fun E hE => hE.1.1 : S5.jOffM M T L (2 ^ k) ≤ T).trans h.le
  have hJeq' : S5.jOffM M T L (2 ^ k) = E₁' ⊔ E₂' :=
    le_antisymm ((imM_le_imM_iff h.le hJM).1 hJeq.le)
      ((imM_le_imM_iff h.le (sup_le hE₁M hE₂M)).1 hJeq.ge)
  obtain ⟨p₁, hp₁, hE₁a⟩ := exists_imSp_eq_xPoint hd h hE₁T hc₁ hu₁
  obtain ⟨p₂, hp₂, hE₂a⟩ := exists_imSp_eq_xPoint hd h hE₂T hc₂ hu₂
  have hJa : S5.imSp a (S5.jOffM M T L (2 ^ k)) = MSP.xPoint p₁ ⊔ MSP.xPoint p₂ := by
    rw [hJeq', imSp_sup hE₁M hE₂M, hE₁a, hE₂a]
  exact false_of_commutator_le_Z0q h hb (commutator_le_Z0q_of_xPoint hd h hp₁ hp₂ hJa)

end CFSG.Quasithin.MS93
