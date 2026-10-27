module

public import CFSG.Quasithin.MS93.S5A56Hat
public import CFSG.Quasithin.MS93.S33SpS5
public import CFSG.Quasithin.MS93.S5A56L

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

open S5 in
theorem s56_of (h51 : S51) : S56 := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hβ l hl hTl hJl
  have := hd.charP
  have hb0 := h.critDist_pos
  have hTst : imSp a T ≤ MSP.stab l := by
    have := vIm_le_of_le_vPre' h.le hTl
    rwa [puAmalgam.qv_baseB, vIm_imM h] at this
  have hJst := vIm_le_of_le_vPre' h.le hJl
  rw [jOff_baseA h, vIm_imM h] at hJst
  have hJM : jOffM M T L (2 ^ k) ≤ M := iSup₂_le fun E hE => (offSetM_le _ hE).trans h.le
  have hJq : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤
      stab (puAmalgam h.le) (baseA _) := by
    rw [jOff_baseA h, puAmalgam.stab_baseA]
    exact imM_mono h.le hJM
  have hZst : ZM (puAmalgam h.le) α' ≤ stab (puAmalgam h.le) (baseA _) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZhst : zHat _ (baseA (puAmalgam h.le)) α' ≤ stab (puAmalgam h.le) (baseA _) :=
    inf_le_left.trans hZst
  have hZT : vIm h.le a (ZM _ α') ≤ imSp a T := by
    have := vIm_mono' (a := a) h (zm_le_qv_baseB h hc hβ)
    rwa [puAmalgam.qv_baseB, vIm_imM h] at this
  rcases sp4_54M h51 hd h hmin hb with ⟨A₀, -, hA, -, -, -, hA₀c, hJ⟩ | ⟨p, hp, hTp, hJT⟩
  swap
  · exfalso
    rw [hJT, hTp] at hJst
    have := MSP.fixSp_antitone hJst
    rw [MSP.fixSp_qLine hl, MSP.fixSp_qPoint hp] at this
    have h2 := Submodule.finrank_mono this
    rw [hl.1, hp] at h2
    omega
  have hA₀T : A₀ ≤ imSp a T := (hA ▸ Set.mem_singleton A₀ : A₀ ∈ candMax (imSp a T)).1.1
  rw [hJ, imSp_liftT hA₀T] at hJst
  have hvJ : vIm h.le a (jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) = A₀ := by
    rw [jOff_baseA h, vIm_imM h, hJ, imSp_liftT hA₀T]
  have hA₀max : A₀ ∈ candMax (imSp a T) := hA ▸ Set.mem_singleton A₀
  have hQJ : Qv (puAmalgam h.le) (baseA _) ≤
      jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) := by
    rw [qv_baseA_eq h, jOff_baseA h, hJ]
    exact imM_mono h.le (hd.pCoreOf_le_liftT h A₀)
  have hq2 : Nat.card F ^ 2 ≤ Nat.card A₀ := hA₀c
  rcases S33.shape_of_sp4Data h hd hc with ⟨hrel, hzh, p, hp, hZp⟩ |
    ⟨hrel1, hrel2, hfin⟩
  ·
    have hpl : p ≤ l := MSP.le_of_xPoint_le_stab hp hl (hZp ▸ hZT.trans hTst)
    have hJ2 : Nat.card A₀ = Nat.card F ^ 2 → MSP.xPoint p ≤ A₀ ∧
        ∀ p', MSP.IsPoint p' → p' ≤ l → p' ≠ p → ¬ MSP.xPoint p ⊔ MSP.xPoint p' ≤ A₀ := by
      intro heq
      have hK : Nat.card F ^ 2 ≤ Nat.card ↥(MSP.qLine l ⊓ imSp a T) :=
        hq2.trans (Subgroup.card_le_of_le (le_inf hJst hA₀T))
      have hKeq : MSP.qLine l ⊓ imSp a T = A₀ := (Subgroup.eq_of_le_of_card_ge
        (le_inf hJst hA₀T) ((hA₀max.2 _ (isCandSp_qLine_inf hl hK)))).symm
      refine ⟨hKeq ▸ le_inf (MSP.xPoint_le_qLine hl hpl) (hZp ▸ hZT), fun p' hp' hp'l hne hle => ?_⟩
      have hcard := card_xPoint_sup hp hp' hne.symm (hp'l.trans (le_perp_of_le hl hpl))
      have hE : MSP.xPoint p ⊔ MSP.xPoint p' = A₀ :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [heq]; exact hcard)
      exact jOffM_ne_xPoint_sup h51 hd h hmin hb hp hp' (by rw [hJ, imSp_liftT hA₀T, hE])
    obtain ⟨g₀, x₀, hx₀c, hx₀s, hopp, hopp', htop⟩ := exists_caseP hl hp hpl hJst hq2 hJ2
    refine concl56_of h hd hl hZhst hJq hQJ hx₀c hopp hopp' ?_ fun _ => hx₀s
    rw [hvJ, hzh, hZp, MSP.xPoint_map_conj, htop]
    exact le_top
  ·
    have hZ2 : IsPGroup 2 (ZM (puAmalgam h.le) α') :=
      (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le (zm_le_qv_baseB h hc hβ)
    by_cases hhat : ∃ t₁ t₂ t₃, IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃ ∧
        t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α'
    · obtain ⟨t₁, t₂, t₃, ht, hn⟩ := hhat
      obtain ⟨hk1, -, -, -⟩ := S33.of_isHatTriple h hd hc ht
      have hq : Nat.card F = 2 := by rw [hd.nat_card_eq, hk1]; rfl
      have hZh := zHat_eq_of_isHatTriple h hd hq hc ht hn
      have hZ4 : 4 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') := by
        rw [hk1] at hrel2
        exact hrel2
      obtain ⟨v₁, v₂, h₁, h₂, h₁₂, hf, hZv₁, hZv₂, hs⟩ := hat_shape h hd hq hc ht hZh hZ4
      have hp₁ := MSP.isPoint_span h₁
      have hp₂ := MSP.isPoint_span h₂
      have hX₁ : MSP.xPoint (F ∙ v₁) ≤ imSp a T := (xPoint_span_le_of_card_two hq h₁ hZv₁).trans hZT
      have hX₂ : MSP.xPoint (F ∙ v₂) ≤ imSp a T := (xPoint_span_le_of_card_two hq h₂ hZv₂).trans hZT
      have hv₁l : (F ∙ v₁) ≤ l := MSP.le_of_xPoint_le_stab hp₁ hl (hX₁.trans hTst)
      have hv₂l : (F ∙ v₂) ≤ l := MSP.le_of_xPoint_le_stab hp₂ hl (hX₂.trans hTst)
      have hne : (F ∙ v₁) ≠ (F ∙ v₂) := by
        intro e
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (e ▸ Submodule.mem_span_singleton_self v₂ :
          v₂ ∈ F ∙ v₁)
        rcases eq_zero_or_eq_one_of_card_two hq c with rfl | rfl
        · exact h₂ (by rw [← hc, zero_smul])
        · exact h₁₂ (by rw [← hc, one_smul])
      have hperp : (F ∙ v₂) ≤ MSP.perp (F ∙ v₁) :=
        (Submodule.span_singleton_le_iff_mem _ _).2 (MSP.mem_perp_span.2 hf)
      have hcard4 := card_xPoint_sup hp₁ hp₂ hne hperp
      have hJgt : Nat.card F ^ 2 < Nat.card A₀ := by
        refine lt_of_le_of_ne hq2 fun heq => ?_
        have hsub : MSP.xPoint (F ∙ v₁) ⊔ MSP.xPoint (F ∙ v₂) ≤ MSP.qLine l ⊓ imSp a T :=
          le_inf (sup_le (MSP.xPoint_le_qLine hl hv₁l) (MSP.xPoint_le_qLine hl hv₂l))
            (sup_le hX₁ hX₂)
        have hK : Nat.card F ^ 2 ≤ Nat.card ↥(MSP.qLine l ⊓ imSp a T) :=
          hcard4.trans (Subgroup.card_le_of_le hsub)
        have hKeq : MSP.qLine l ⊓ imSp a T = A₀ := (Subgroup.eq_of_le_of_card_ge
          (le_inf hJst hA₀T) ((hA₀max.2 _ (isCandSp_qLine_inf hl hK)))).symm
        have hE : MSP.xPoint (F ∙ v₁) ⊔ MSP.xPoint (F ∙ v₂) = A₀ :=
          Subgroup.eq_of_le_of_card_ge (hKeq ▸ hsub) (by rw [← heq]; exact hcard4)
        exact jOffM_ne_xPoint_sup h51 hd h hmin hb hp₁ hp₂ (by rw [hJ, imSp_liftT hA₀T, hE])
      have hdq : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k → False := by
        intro hq'
        rw [hq'] at hrel1
        have : 2 ^ k < (2 ^ k) ^ 2 := by
          have : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
          nlinarith
        omega
      have hcaseP : ∀ {v : MSP.V4 F}, v ≠ 0 → (F ∙ v) ≤ l →
          MSP.transv v 1 ∈ vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α') →
          ∃ g ∈ stab _ (baseA (puAmalgam h.le)), ∃ x ∈ puTrans h.le L (baseA _),
            Concl56 h (2 ^ k) a α' l g x := by
        intro v hv hvl hvZ
        have hXZ := xPoint_span_le_of_card_two hq hv hvZ
        obtain ⟨g₀, x₀, hx₀c, -, hopp, hopp', htop⟩ :=
          exists_caseP hl (MSP.isPoint_span hv) hvl hJst hq2 (fun h' => absurd h' hJgt.ne')
        refine concl56_of h hd hl hZhst hJq hQJ hx₀c hopp hopp' ?_ fun hq' => (hdq hq').elim
        rw [hvJ]
        have hle : commutator (StatedSp 2 F) ≤ ⊤ := le_top
        rw [← htop, ← MSP.xPoint_map_conj] at hle
        exact hle.trans (sup_le_sup (sup_le_sup_left hXZ _) (Subgroup.map_mono hXZ))
      rcases hs with hs | hs | hs
      · exact hcaseP h₁ hv₁l hs
      · exact hcaseP h₂ hv₂l hs
      · obtain ⟨g₀, x₀, hx₀c, -, hopp, hopp', htop⟩ := exists_caseHat hq hl h₁ h₂ h₁₂
          ((Submodule.span_singleton_le_iff_mem _ _).1 hv₁l)
          ((Submodule.span_singleton_le_iff_mem _ _).1 hv₂l) hJst hJgt hs
        refine concl56_of h hd hl hZhst hJq hQJ hx₀c hopp hopp' ?_ fun hq' => (hdq hq').elim
        rw [hvJ, htop]
        exact le_top
    · have hzh := zHat_eq_of_not hhat
      have hZc : Nat.card F ^ 2 ≤ Nat.card ↥(vIm h.le a (ZM _ α')) := by
        rw [card_vIm h hd hZst hZ2, hd.nat_card_eq]
        exact hrel2
      obtain ⟨g₀, x₀, hx₀c, hopp, hopp', hcc⟩ := exists_caseL hl
        (IsSp4Data.isPGroup_imSp (a := a) h) hTst hA
        hJst hq2 hZT hZc (commSp_le_fixSp_zm h hd hc) hfin
      refine concl56_of h hd hl hZhst hJq hQJ hx₀c hopp hopp' ?_ fun hq => ?_
      · rwa [hvJ, hzh]
      · exfalso
        rw [hq] at hrel1
        have : 2 ^ k < (2 ^ k) ^ 2 := by
          have : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
          nlinarith
        omega

end CFSG.Quasithin.MS93
