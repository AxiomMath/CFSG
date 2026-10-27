module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGTPRows
public import CFSG.LocalAnalysis.StandardType.GGTPTwE6
public import CFSG.LocalAnalysis.StandardType.GGTPStdFrame
public import CFSG.LocalAnalysis.StandardType.GGTPCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTPFrameK
public import CFSG.LocalAnalysis.StandardType.GGTPDatum
public import CFSG.LocalAnalysis.StandardType.GGTPStabJ
public import CFSG.LocalAnalysis.StandardType.GGTPJLabel
public import CFSG.LocalAnalysis.StandardType.GGE6DepTableRest
public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGE6DepConjAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTPCfg_of_E6row {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    (hM : GGE6DepModelKnown) (hNI : GGE6DepNonIsoPt) (hLB : GGLBalanceInput)
    (hJS : GGTPJStabInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hinn : GGInnerDiagAll 3 B Bs x L D J)
    (hnt : GGNoTransvection 3 Bs) {y : G} {K : Subgroup G} (hnbr : GGNbr 3 B x D J y K)
    (hE : GGE6DepPerpCfg 3 Bs L K) (hconj : GGE6DepConjSetting 3 Bs x y L) (hxL : x ∉ L)
    (hJp : 3 ∣ Nat.card ↥J) {y' : G} {K' : Subgroup G} (hnbr' : GGNbr 3 B x D J y' K')
    {lab₀ : LargeEvenLabel} (hlab₀ : GGE6DepLabel lab₀) (hΛ : LargeEvenInLambda2 lab₀)
    (hmL : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab = lab₀))
    (hK'lab : GGHasLabel lab₀ (↥K' ⧸ Subgroup.center ↥K')) : GGE6DepPerpCfg 3 Bs L K' := by
  have hcardBs : Nat.card Bs = 3 ^ 6 := hE.2.1
  obtain ⟨hxBs, hyBs, ι, hι, hyι⟩ := ggTPStdFrame hRig hM hNI hcfg hinn hnt hnbr hE hxL
  have hSJ := ggTPStab_le_automizerJ hRig hJS hcfg hinn hnbr hE hconj hyBs
  have hD : D = Subgroup.closure {x, y} := hnbr.2.1
  have hCJ := ggTPCentralizerJ_le_D hxBs hyBs hι hyι hD hSJ
  obtain ⟨hmK', hJK', -, κ, hκ⟩ :=
    ggTPFrameK_of_nbr hRig hM hLB hcfg hinn hCJ hJp hnbr' hlab₀ hΛ hcardBs hK'lab
  obtain ⟨hy'Bs, hxy', hKy', -⟩ := ggE6Dep_nbr_facts hcfg hnbr'
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hy'1 : y' ≠ 1 := fun h => hxy' (h ▸ Subgroup.one_mem _)
  have hdat := ggTPDatum_of_stab hxBs hyBs hy'Bs hy'1 (hBs.2 y' hy'Bs) hBs hcardBs hnt hKy' hι hyι hκ
    (fun φ hφ hfix => ggAutomizer_mono Bs hJK' (hSJ φ hφ hfix))
  exact ⟨rfl, hcardBs, hdat, lab₀, hlab₀, hmL, hmK'⟩

theorem ggTPTableRest_of_leaves (hRig : GGLabelRigidInput) (hM : GGE6DepModelKnown)
    (hNI : GGE6DepNonIsoPt) (hX : GGE6DepPerpXNotInL) (hLB : GGLBalanceInput)
    (hJL : GGTPJLayerInput) (hJS : GGTPJStabInput) (hN : GGTPClassicalExcl)
    : GGE6DepPerpTableRest := by
  intro G _ _ p B Bs x L D J hcfg hop hinn hnt y K hnbr hE y' K' hnbr' labJ labK hJΛ hKΛ hhJ hhK
    hrow
  obtain rfl : p = 3 := hE.1
  have hconj : GGE6DepConjSetting 3 Bs x y L :=
    ggE6DepConj_of_known hRig hM hX hNI G 3 B Bs x L D J hcfg hop hinn hnt y K hnbr hE
  have hxL : x ∉ L := hX G 3 B Bs x L D J hcfg hop hinn hnt y K hnbr hE
  obtain ⟨-, -, -, lab₀, hlab₀, hmL, -⟩ := id hE
  obtain ⟨lab, hΛ₀, hhasL, R₀, -, I₀, F₀, θ₀, hlab_eq⟩ := largeEvenMarking_exists_hasLabel hmL
  rw [hlab_eq] at hΛ₀ hhasL
  obtain ⟨hJlab, hZJ, hJp⟩ :=
    ggTPJLabel_of_config hRig hJL hcfg hinn.1 hnbr hE hconj hlab₀ hmL
  have hJK : J ≤ K' := le_of_ggNbr hLB hcfg.1 hcfg.2.2 hJp hnbr'
  have hjΛ : LargeEvenInLambda2 (ggTPJLabel lab₀) := by
    rcases hlab₀ with ⟨ht, -⟩ | ⟨ht, -⟩ <;> simp [ggTPJLabel, ht, LargeEvenInLambda2] <;>
      exact hΛ₀.1
  have hlabJ : ggTPJLabel lab₀ = labJ :=
    ggTPLabelIso_jLabel (hRig (ggTPJLabel lab₀) labJ _ hjΛ hJΛ hJlab hhJ)
  subst hlabJ
  have hclass : GGTPClassicalLab labK → False := fun hcl =>
    hN G 3 B Bs x L D J hcfg hop hinn hnt y K hnbr hE y' K' hnbr' (ggTPJLabel lab₀) labK hjΛ hKΛ hcl
      hhJ hhK hrow
  have hlab₀' := hlab₀
  rcases lab₀ with ⟨t₀, r₀, n₀⟩
  rcases hlab₀ with ⟨ht, h3⟩ | ⟨ht, h3⟩
  ·
    dsimp only at ht h3
    subst ht
    have hr : r₀ = 0 := (by simpa [LargeEvenInLambda2] using hΛ₀ : 1 ≤ n₀ ∧ r₀ = 0).2
    subst hr
    have hj : ggTPJLabel ⟨.E6, 0, n₀⟩ = ⟨.A, 5, n₀⟩ := by simp [ggTPJLabel]
    rw [hj] at hrow hhJ
    rcases ggTPTablePRow_A5 h3 hrow with h | h | h | h | h | h
    · subst h
      exact ggTPCfg_of_E6row hRig hM hNI hLB hJS hcfg hinn hnt hnbr hE hconj hxL hJp hnbr' hlab₀'
        hΛ₀ hmL hhK
    · exact (hclass (by rw [h]; simp [GGTPClassicalLab])).elim
    · exact (hclass (by rw [h]; simp [GGTPClassicalLab])).elim
    · exact (hclass (by rw [h]; simp [GGTPClassicalLab])).elim
    · exact (hclass (by rw [h]; simp [GGTPClassicalLab])).elim
    · exact (hclass (Or.inl h.1)).elim
  ·
    dsimp only at ht h3
    subst ht
    have hr : r₀ = 0 := (by simpa [LargeEvenInLambda2] using hΛ₀ : 1 ≤ n₀ ∧ r₀ = 0).2
    subst hr
    have hj : ggTPJLabel ⟨.twE6, 0, n₀⟩ = ⟨.twA, 5, n₀⟩ := by simp [ggTPJLabel]
    rw [hj] at hrow hhJ
    rcases ggTPTablePRow_twA5 h3 hrow with h | h | h | h | h | h
    · subst h
      exact ggTPCfg_of_E6row hRig hM hNI hLB hJS hcfg hinn hnt hnbr hE hconj hxL hJp hnbr' hlab₀'
        hΛ₀ hmL hhK
    · exact (hclass (by rw [h]; simp [GGTPClassicalLab])).elim
    · exact (hclass (by rw [h]; simp [GGTPClassicalLab])).elim
    · exact (hclass (by rw [h]; simp [GGTPClassicalLab])).elim
    · exact (hclass (by rw [h]; simp [GGTPClassicalLab])).elim
    · obtain ⟨htK, hnK⟩ := h
      rcases labK with ⟨tK, rK, nK⟩
      dsimp only at htK hnK
      subst htK
      have hrK : rK = 0 := (by simpa [LargeEvenInLambda2] using hKΛ : 1 ≤ nK ∧ rK = 0).2
      subst hrK
      exact (ggTPTwE6_excl (n' := nK) hJK (by omega) (hKΛ.1 : 1 ≤ nK) hhJ hhK).elim

end CFSG.StandardType

end
