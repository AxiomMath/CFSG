module

public import CFSG.Quasithin.MS93.S5A55A
public import CFSG.Quasithin.MS93.S5A55B
public import CFSG.Quasithin.MS93.S5A55X
public import CFSG.Quasithin.MS93.S5A55Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5

section Shape

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

theorem zHat_shape55 (hd : IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') (hβ : geo _ (baseA _) α' 1 = baseB _) :
    vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α') ≤ imSp a T ∧
    ((∃ c : Submodule F (MSP.V4 F), MSP.IsPoint c ∧
        vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α') = MSP.xPoint c) ∨
      (Nat.card F ^ 2 ≤ Nat.card ↥(vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α')) ∧
        MSP.commSp (vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α')) ≤
          MSP.fixSp (vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α')) ∧
        Module.finrank F (MSP.fixSp (vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α'))) ≤ 2) ∨
      (Nat.card F = 2 ∧ ∃ v₁ v₂ : MSP.V4 F, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧
        MSP.form F v₁ v₂ = 0 ∧ MSP.transv v₁ 1 ∈ imSp a T ∧ MSP.transv v₂ 1 ∈ imSp a T ∧
        (MSP.transv v₁ 1 ∈ vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α') ∨
          MSP.transv v₂ 1 ∈ vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α') ∨
          MSP.transv v₁ 1 * MSP.transv v₂ 1 ∈
            vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α')))) := by
  have := hd.charP
  have hb0 := h.critDist_pos
  have hZst : ZM (puAmalgam h.le) α' ≤ stab (puAmalgam h.le) (baseA _) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZ2 : IsPGroup 2 (ZM (puAmalgam h.le) α') :=
    (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le (zm_le_qv_baseB h hc hβ)
  have hZT : vIm h.le a (ZM _ α') ≤ imSp a T := by
    have := vIm_mono' (a := a) h (zm_le_qv_baseB h hc hβ)
    rwa [puAmalgam.qv_baseB, vIm_imM h] at this
  refine ⟨(vIm_mono' h inf_le_left).trans hZT, ?_⟩
  rcases S33.shape_of_sp4Data h hd hc with ⟨-, hzh, p, hp, hZp⟩ | ⟨-, hrel2, hfin⟩
  · exact Or.inl ⟨p, hp, by rw [hzh, hZp]⟩
  · by_cases hhat : ∃ t₁ t₂ t₃, IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃ ∧
        t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α'
    · obtain ⟨t₁, t₂, t₃, ht, hn⟩ := hhat
      obtain ⟨hk1, -, -, -⟩ := S33.of_isHatTriple h hd hc ht
      have hq : Nat.card F = 2 := by rw [hd.nat_card_eq, hk1]; rfl
      have hZh := zHat_eq_of_isHatTriple h hd hq hc ht hn
      have hZ4 : 4 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') := by
        rw [hk1] at hrel2
        exact hrel2
      obtain ⟨v₁, v₂, h₁, h₂, h₁₂, hf, hZv₁, hZv₂, hs⟩ := hat_shape h hd hq hc ht hZh hZ4
      exact Or.inr (Or.inr ⟨hq, v₁, v₂, h₁, h₂, h₁₂, hf, hZT hZv₁, hZT hZv₂, hs⟩)
    · have hzh := zHat_eq_of_not hhat
      refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩) <;> rw [hzh]
      · rw [card_vIm h hd hZst hZ2, hd.nat_card_eq]
        exact hrel2
      · exact commSp_le_fixSp_zm h hd hc
      · exact hfin

end Shape

end S5

open S5 in
theorem s55_of (h51 : S51) (h32 : S32) (hq55 : S5Q2.Q2Cent55) (hsp : Sp4Case55) : S55 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hβ δ hβδ hhyp
  have := hd.charP
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  rcases sp4_54M h51 hd h hmin hb with ⟨A₀, l, hA, hl, hTl, hA₀l, hA₀c, hJ⟩ | ⟨p, hp, hTp, hJT⟩
  swap
  ·
    obtain ⟨v, hv, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
    have hJ' : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) = Qv _ (baseB _) := by
      rw [jOff_baseA h, hJT, ← puAmalgam.qv_baseB]
    exact concl55_of_point h hd hc hβ hβδ hJ' hv hTp
  have hA₀ : A₀ ∈ candMax (imSp a T) := hA ▸ Set.mem_singleton A₀
  have hA₀T : A₀ ≤ imSp a T := hA₀.1.1
  have hvJ := vIm_jOff_baseA h hA₀T hJ
  set Jα := jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) with hJα
  set Jδ := jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le)) with hJδ
  have hline : ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
      Qv _ (baseB (puAmalgam h.le)) ≤ vPre h.le a (MSP.stab l) ∧
      Jα ≤ vPre h.le a (MSP.qLine l) := by
    refine ⟨l, hl, ?_, ?_⟩
    · rw [puAmalgam.qv_baseB]
      exact imM_le_vPre h hTl
    · rw [hJα, jOff_baseA h, hJ]
      exact imM_le_vPre h (by rw [imSp_liftT hA₀T]; exact hA₀l)
  have hne : Jδ ≠ Jα := by
    rcases hhyp with hne | hall
    · exact hne
    · obtain ⟨l', hl', hT', hJ'⟩ := hline
      exact absurd hJ' (hall l' hl' hT')
  have hJαst := jOff_le_stab_baseA h (2 ^ k) (baseA (puAmalgam h.le))
  have hJδst := jOff_le_stab_baseA h (2 ^ k) δ
  have hnot : ¬ IsMVtx _ (baseB (puAmalgam h.le)) :=
    (isMVtx_iff_of_adj _ (adj_baseA_baseB _)).1 hα
  have hJδ2 : IsPGroup 2 Jδ := (isPGroup_qv _ hyp hnot).to_le (iSup₂_le fun _ hE => hE.1.1)
  have hJα2 : IsPGroup 2 Jα := (isPGroup_qv _ hyp hnot).to_le (iSup₂_le fun _ hE => hE.1.1)
  have hDT : vIm h.le a Jδ ≤ imSp a T := by
    have := vIm_mono' (a := a) h (iSup₂_le fun _ hE => hE.1.1 : Jδ ≤ Qv _ (baseB _))
    rwa [puAmalgam.qv_baseB, vIm_imM h] at this
  have hrel := relIndex_jOff_le h (q := 2 ^ k) Nat.one_le_two_pow hβδ
  rw [← card_vIm h hd hJαst hJα2, ← card_vIm h hd hJδst hJδ2, hvJ] at hrel
  have hDnc := not_isCandSp_vIm_jOff h hd hA hJ hβδ hne
  have h51' : ∀ p₁ p₂ : Submodule F (MSP.V4 F), MSP.IsPoint p₁ → MSP.IsPoint p₂ →
      A₀ ≠ MSP.xPoint p₁ ⊔ MSP.xPoint p₂ := fun p₁ p₂ hp₁ hp₂ he =>
    jOffM_ne_xPoint_sup h51 hd h hmin hb hp₁ hp₂ (by rw [hJ, imSp_liftT hA₀T, he])
  have hodd : Nat.card F = 2 → ¬ imSp a T ≤ commutator (MSP.Sp4 F) := by
    intro hq hle
    obtain rfl : k = 1 := by
      have h1 := hd.nat_card_eq
      rw [hq] at h1
      exact Nat.pow_right_injective le_rfl (h1.symm.trans (pow_one 2).symm)
    obtain ⟨t, htT, hto⟩ := S5Q2.exists_mem_T_not_mem_commutator h hd
    exact hto (hle ⟨t, Subgroup.mem_subgroupOf.2 htT, rfl⟩)
  obtain ⟨hZT, hshape⟩ := zHat_shape55 h hd hc hβ
  obtain ⟨gb, hfix, hcase⟩ := hsp F (imSp a T) A₀ (vIm h.le a Jδ)
    (vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α')) l (IsSp4Data.isPGroup_imSp (a := a) h) hA
    hl hTl hA₀l hA₀c h51' hodd hDT (le_normalizer_vIm_jOff h (2 ^ k) hβδ) hrel.1 hDnc hZT hshape
  obtain ⟨m₀, hm₀⟩ := hd.surj gb
  set g := (puAmalgam h.le).ofA m₀ with hg
  have hgst : g ∈ stab _ (baseA (puAmalgam h.le)) := ofA_range_eq h.le ▸ ⟨m₀, rfl⟩
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hgst)
  have hginv : g⁻¹ = (puAmalgam h.le).ofA m₀⁻¹ := by rw [hg, map_inv]
  have hconj : ∀ K : Subgroup (puAmalgam h.le).Universal,
      vIm h.le a (K.map (MulAut.conj g⁻¹).toMonoidHom) =
        (vIm h.le a K).map (MulAut.conj gb⁻¹).toMonoidHom := fun K => by
    rw [hginv, vIm_map_conj, map_inv, hm₀]
  obtain ⟨hαβ₁, hβ₁α₁⟩ := adj_smul_inv_baseB h hgst hβδ
  have hst : (puAmalgam h.le).ofA.range = stab (puAmalgam h.le) (baseA _) := ofA_range_eq h.le
  have hT₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_adj _ hαβ₁.symm
  have hZst := zHat_le_stab h hc hβ
  have hJ₁ : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (g⁻¹ • baseB (puAmalgam h.le)) =
      Jα.map (MulAut.conj g⁻¹).toMonoidHom := by
    have e := jOff_smul h.le hLn (2 ^ k) g⁻¹ (baseA (puAmalgam h.le)) (baseB _)
    rwa [hgα] at e
  have hJα₁ : jOff h.le L (2 ^ k) (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) =
      Jδ.map (MulAut.conj g⁻¹).toMonoidHom := jOff_smul h.le hLn _ _ _ _
  have hJα₁st : jOff h.le L (2 ^ k) (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ≤
      stab _ (baseA (puAmalgam h.le)) := (iSup₂_le fun _ hE => hE.1.1).trans hT₁
  have hB : ZH _ (baseB (puAmalgam h.le)) ⊓ Subgroup.centralizer
      (jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (g⁻¹ • baseB (puAmalgam h.le)) :
        Set (puAmalgam h.le).Universal) ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
    refine zh_inf_centralizer_jOff_le h (s53_of h51 h32) hmin hb hd hgst ?_
    rw [puAmalgam.qv_baseB, vIm_imM h, hJ₁, hconj, hvJ]
    exact hfix
  have hLT : puTrans h.le L (baseA (puAmalgam h.le)) ⊔ Qv _ (g⁻¹ • baseB (puAmalgam h.le)) =
      stab _ (baseA (puAmalgam h.le)) := by
    have e := S38E.stab_baseA_eq h
    have e2 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) e
    rw [Subgroup.map_sup, ← qv_smul, ← puTrans_smul h.le hLn, hgα, ← stab_smul, hgα] at e2
    exact e2.symm
  refine ⟨g, hgst, 1, one_mem _, ?_⟩
  rcases hcase with hc1 | ⟨htop, hcardD, hint⟩
  ·
    have hL : puTrans h.le L (baseA (puAmalgam h.le)) ≤
        jOff h.le L (2 ^ k) (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) ⊔
          zHat _ (baseA (puAmalgam h.le)) α' := by
      refine puTrans_le_jOff_sup_zHat h hd (2 ^ k) hc hβ hβδ hgst ?_
      rw [vIm_sup h.le (hJα₁st.trans hst.ge) (hZst.trans hst.ge), hJα₁, hconj]
      exact (imSp_L_le_commutator h).trans hc1
    have hA : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ⊔ zHat _ (baseA (puAmalgam h.le)) α' =
        stab _ (baseA (puAmalgam h.le)) := by
      refine le_antisymm (sup_le hT₁ hZst) ?_
      rw [← hLT]
      refine sup_le (hL.trans (sup_le_sup_right (iSup₂_le fun _ hE => hE.1.1) _)) le_sup_left
    refine ⟨⟨hA, ?_⟩, ⟨hB, by rw [rconj_one]; exact hB⟩, Or.inl ?_⟩
    · rw [rconj_one]
      refine le_antisymm (sup_le hT₁ (zm_le_stab_of_isCritical _ hyp h.critDist_pos hc)) ?_
      rw [← hA]
      exact sup_le_sup_left inf_le_left _
    · rw [rconj_one, inf_idem]
      exact hL
  ·
    have hA : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ⊔ zHat _ (baseA (puAmalgam h.le)) α' =
        stab _ (baseA (puAmalgam h.le)) := by
      refine qv_sup_zHat_eq_stab h hd hc hβ hgst ?_
      rw [vIm_sup h.le (hT₁.trans hst.ge) (hZst.trans hst.ge), qv_smul, hconj,
        puAmalgam.qv_baseB, vIm_imM h]
      exact htop
    have hQJ : Qv _ (baseA (puAmalgam h.le)) ≤ Jδ := hrel.2 (by rw [hcardD])
    have hfα : Module.finrank F (MSP.fixSp (vIm h.le a Jα)) = 2 := by
      have hq : Nat.card F < Nat.card A₀ := by
        have h1 : 1 < Nat.card F := Finite.one_lt_card
        calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
          _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right h1 (by norm_num)
          _ ≤ Nat.card A₀ := hA₀c
      rw [hvJ, fixSp_eq_of_le_qLine hl hA₀l hq, hl.1]
    have hfδ : Module.finrank F (MSP.fixSp (vIm h.le a Jδ)) = 1 :=
      finrank_fixSp_eq_one_of_not_isCandSp (IsSp4Data.isPGroup_imSp (a := a) h) hDT
        (hA₀c.trans hrel.1) hDnc
    have hX := xm_ne_of_finrank_fixSp h hq55 hmin hb hd hβδ hne hQJ hline hfα hfδ
    have hidx : (Qv _ (baseA (puAmalgam h.le))).relIndex (Jδ ⊓ Jα) ≤ Nat.card F ^ 2 := by
      rw [← card_vIm h hd (inf_le_right.trans hJαst) (hJα2.to_le inf_le_right),
        vIm_jOff_inf_jOff h hA₀T hJ]
      exact hint
    refine ⟨⟨hA, ?_⟩, ⟨hB, by rw [rconj_one]; exact hB⟩, Or.inr ⟨hQJ, ?_, hX⟩⟩
    · rw [rconj_one]
      refine le_antisymm (sup_le hT₁ (zm_le_stab_of_isCritical _ hyp h.critDist_pos hc)) ?_
      rw [← hA]
      exact sup_le_sup_left inf_le_left _
    · rwa [hd.nat_card_eq] at hidx

end CFSG.Quasithin.MS93
