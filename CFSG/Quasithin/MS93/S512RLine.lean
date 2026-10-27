module

public import CFSG.Quasithin.MS93.S512TBad
public import CFSG.Quasithin.MS93.S512NR2C

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512R

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem map_le_qLine_of_two_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E₁ E₂ K : Subgroup G} (hE₁ : E₁ ≤ M) (hE₂ : E₂ ≤ M) (hK : K ≤ M)
    (hr₁ : (Subgroup.centralizer (E₁ : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hr₂ : (Subgroup.centralizer (E₂ : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hne : Uq M T L ⊓ Subgroup.centralizer (E₁ : Set G) ≠
      Uq M T L ⊓ Subgroup.centralizer (E₂ : Set G))
    (hc₁ : ⁅Uq M T L, E₁⁆ ≤ Subgroup.centralizer (K : Set G))
    (hc₂ : ⁅Uq M T L, E₂⁆ ≤ Subgroup.centralizer (K : Set G))
    {l : Submodule F (MSP.V4 F)} (hl : Module.finrank F l = 2)
    (hKl : MSP.fixSp ((K.subgroupOf M).map a) ≤ l) :
    (K.subgroupOf M).map a ≤ MSP.qLine l := by
  have hk : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hd.1
  have hdim : ∀ {E : Subgroup G}, E ≤ M →
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k →
      Module.finrank F (MSP.commSp ((E.subgroupOf M).map a)) = 1 := by
    intro E hEM hr
    have h1 := S512T.relIndex_eq_pow_M h hd hEM
    rw [hr] at h1
    exact (Nat.pow_right_injective hk (h1.symm.trans (pow_one _).symm))
  set p₁ := MSP.commSp ((E₁.subgroupOf M).map a) with hp₁
  set p₂ := MSP.commSp ((E₂.subgroupOf M).map a) with hp₂
  have hd₁ : Module.finrank F p₁ = 1 := hdim hE₁ hr₁
  have hd₂ : Module.finrank F p₂ = 1 := hdim hE₂ hr₂
  have hK₁ : p₁ ≤ MSP.fixSp ((K.subgroupOf M).map a) :=
    MSP.le_fixer_iff.1 (S512T.map_le_qLine_M h hd hK hc₁)
  have hK₂ : p₂ ≤ MSP.fixSp ((K.subgroupOf M).map a) :=
    MSP.le_fixer_iff.1 (S512T.map_le_qLine_M h hd hK hc₂)
  have hp : p₁ ≠ p₂ := by
    intro heq
    apply hne
    obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
    have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
    have hfix : MSP.fixSp ((E₁.subgroupOf M).map a) = MSP.fixSp ((E₂.subgroupOf M).map a) := by
      rw [S5B.fixSp_eq_perp_commSp, S5B.fixSp_eq_perp_commSp, ← hp₁, ← hp₂, heq]
    ext u
    constructor
    · rintro ⟨hu, huc⟩
      refine ⟨hu, (S5B.mem_centralizer_iff_vec h hlift c hE₂ ⟨u, hu⟩).2 ?_⟩
      rw [← hfix]
      exact (S5B.mem_centralizer_iff_vec h hlift c hE₁ ⟨u, hu⟩).1 huc
    · rintro ⟨hu, huc⟩
      refine ⟨hu, (S5B.mem_centralizer_iff_vec h hlift c hE₁ ⟨u, hu⟩).2 ?_⟩
      rw [hfix]
      exact (S5B.mem_centralizer_iff_vec h hlift c hE₂ ⟨u, hu⟩).1 huc
  have hinf : Module.finrank F ↥(p₁ ⊓ p₂) = 0 := by
    by_contra hne0
    have hle1 : Module.finrank F ↥(p₁ ⊓ p₂) ≤ 1 := by
      have := Submodule.finrank_mono (inf_le_left : p₁ ⊓ p₂ ≤ p₁)
      omega
    have h1 : Module.finrank F ↥(p₁ ⊓ p₂) = 1 := by omega
    have e1 : p₁ ⊓ p₂ = p₁ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hd₁])
    have e2 : p₁ ⊓ p₂ = p₂ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, hd₂])
    exact hp (e1.symm.trans e2)
  have hsup : Module.finrank F ↥(p₁ ⊔ p₂) = 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq p₁ p₂
    omega
  have hle : p₁ ⊔ p₂ ≤ l := (sup_le hK₁ hK₂).trans hKl
  have heq : p₁ ⊔ p₂ = l := Submodule.eq_of_le_of_finrank_eq hle (by rw [hsup, hl])
  rw [← heq]
  exact MSP.le_fixer_iff.2 (sup_le hK₁ hK₂)

theorem qv_le_vPre_qLine_of_two (h51 : S51) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hJl : S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
    {δ ε : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδε : (puAmalgam h.le).treeGraph.Adj δ ε)
    {E₁ E₂ : Subgroup (puAmalgam h.le).Universal} (hE₁ε : E₁ ≤ Qv _ ε) (hE₂ε : E₂ ≤ Qv _ ε)
    (hr₁ : (Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    (hr₂ : (Subgroup.centralizer (E₂ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    (hne : S5.uSub h.le L δ ⊓ Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal) ≠
      S5.uSub h.le L δ ⊓ Subgroup.centralizer (E₂ : Set (puAmalgam h.le).Universal))
    (hc₁ : ⁅S5.uSub h.le L δ, E₁⁆ ≤
      Subgroup.centralizer (Qv _ ε : Set (puAmalgam h.le).Universal))
    (hc₂ : ⁅S5.uSub h.le L δ, E₂⁆ ≤
      Subgroup.centralizer (Qv _ ε : Set (puAmalgam h.le).Universal)) :
    Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hJT : S5.jOffM M T L (2 ^ k) ≤ T := iSup₂_le fun E hE => hE.1.1
  have hJM : S5.jOffM M T L (2 ^ k) ≤ M := hJT.trans h.le
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
  have hT : ∀ {E₀ : Subgroup G}, E₀ ≤ M →
      (imM h.le E₀).map (MulAut.conj c).toMonoidHom ≤ Qv _ (c • baseB (puAmalgam h.le)) →
      E₀ ≤ T := by
    intro E₀ hE₀M hE
    rw [hQε, map_conj_le_map_conj_iff, imM_le_imM_iff h.le hE₀M] at hE
    exact hE
  have hrel : ∀ {E₀ : Subgroup G}, E₀ ≤ M →
      (Subgroup.centralizer (((imM h.le E₀).map (MulAut.conj c).toMonoidHom : Subgroup _) :
        Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (c • baseA _)) = 2 ^ k →
      (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) = 2 ^ k := by
    intro E₀ hE₀M hr
    rw [hU, PU.centralizer_map_mulEquiv,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
      S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M] at hr
    exact hr
  have hcomm : ∀ {E₀ : Subgroup G}, E₀ ≤ M →
      ⁅S5.uSub h.le L (c • baseA _), (imM h.le E₀).map (MulAut.conj c).toMonoidHom⁆ ≤
        Subgroup.centralizer (Qv _ (c • baseB (puAmalgam h.le)) : Set _) →
      ⁅Uq M T L, E₀⁆ ≤ Subgroup.centralizer (T : Set G) := by
    intro E₀ hE₀M hcE
    have hcommM : ⁅Uq M T L, E₀⁆ ≤ M := commutator_le_of_le (Uq_le h.L_le) hE₀M
    rw [hU, ← Subgroup.map_commutator, ← imM_commutator h.le (Uq_le h.L_le) hE₀M, hQε,
      PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
      S512T.imM_le_centralizer_iff h.le hcommM h.le] at hcE
    exact hcE
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
  have hJl' : ((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a ≤ MSP.qLine l :=
    S512T.imSp_le_of_imM_le_vPre h.le (by rw [← S5.jOff_baseA h]; exact hJl)
  have hCl : MSP.fixSp (((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a) = l :=
    S5.fixSp_eq_of_le_qLine hl hJl' (S512N.card_lt_card_imSp_jOffM h51 hd h hmin hb)
  have hTl : MSP.fixSp ((T.subgroupOf M).map a) ≤ l := by
    rw [← hCl]
    refine MSP.fixSp_antitone ?_
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨⟨j, hJM (Subgroup.mem_subgroupOf.1 hj)⟩,
      Subgroup.mem_subgroupOf.2 (hJT (Subgroup.mem_subgroupOf.1 hj)), rfl⟩
  have key := map_le_qLine_of_two_M h hd hE₁₀M hE₂₀M h.le (hrel hE₁₀M hr₁) (hrel hE₂₀M hr₂) hne₀
    (hcomm hE₁₀M hc₁) (hcomm hE₂₀M hc₂) hl.1 hTl
  rw [puAmalgam.qv_baseB]
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, key ⟨t, ht, rfl⟩, rfl⟩

end S512R

end CFSG.Quasithin.MS93
