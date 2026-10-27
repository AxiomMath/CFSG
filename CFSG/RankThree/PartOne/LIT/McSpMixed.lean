module

public import CFSG.RankThree.PartOne.LIT.McSpShape

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith invariant_of_generators)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

section Aux

variable {H : Subgroup (V ≃ₗ[ZMod p] V)} {U L : Submodule (ZMod p) V}

private theorem invariant_of_trIn
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    {W : Submodule (ZMod p) V}
    (hW : ∀ (x : V) (h : Module.Dual (ZMod p) V), TrIn H x h → x ≠ 0 → h ≠ 0 →
      x ∈ W ∨ ∀ y ∈ W, h y = 0) :
    ∀ g ∈ H, ∀ y ∈ W, g y ∈ W := by
  obtain ⟨S, hS, hHS⟩ := hgen
  refine invariant_of_generators hHS fun t ht y hy => ?_
  obtain ⟨v, f, hvf⟩ := hS t ht
  have hTr : TrIn H v f := TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure ht) hvf
  rcases hW v f hTr hvf.1 hvf.2.1 with hv | hf
  · exact ⟨by rw [hvf.2.2.2 y]; exact W.add_mem hy (W.smul_mem _ hv),
      by rw [hvf.inv_apply y]; exact W.sub_mem hy (W.smul_mem _ hv)⟩
  · exact ⟨by rw [hvf.2.2.2 y, hf y hy, zero_smul, add_zero]; exact hy,
      by rw [hvf.inv_apply y, hf y hy, zero_smul, sub_zero]; exact hy⟩

private theorem mem_U_of_projL_eq_zero (hF : IsFrame H U L) {x : V} (h : hF.projL x = 0) :
    x ∈ U := by
  rw [← hF.projU_add_projL x, h, add_zero]
  exact hF.projU_mem x

private theorem mem_L_of_projU_eq_zero (hF : IsFrame H U L) {x : V} (h : hF.projU x = 0) :
    x ∈ L := by
  rw [← hF.projU_add_projL x, h, zero_add]
  exact hF.projL_mem x

private def mixedL (hF : IsFrame H U L) : Submodule (ZMod p) V :=
  Submodule.span (ZMod p) {l | ∃ (x : V) (h : Module.Dual (ZMod p) V), TrIn H x h ∧ h ≠ 0 ∧
    hF.projU x ≠ 0 ∧ hF.projL x ≠ 0 ∧ hF.projL x = l}

private theorem mem_mixedL (hF : IsFrame H U L) {x : V} {h : Module.Dual (ZMod p) V}
    (hxh : TrIn H x h) (hh : h ≠ 0) (hU : hF.projU x ≠ 0) (hL : hF.projL x ≠ 0) :
    hF.projL x ∈ mixedL hF :=
  Submodule.subset_span ⟨x, h, hxh, hh, hU, hL, rfl⟩

private theorem mixedL_le_of (hF : IsFrame H U L) {W : Submodule (ZMod p) V}
    (hW : ∀ (x : V) (h : Module.Dual (ZMod p) V), TrIn H x h → h ≠ 0 → hF.projU x ≠ 0 →
      hF.projL x ≠ 0 → hF.projL x ∈ W) :
    mixedL hF ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, h, hxh, hh, hU, hL, rfl⟩
  exact hW x h hxh hh hU hL

private theorem mixedL_le_L (hF : IsFrame H U L) : mixedL hF ≤ L :=
  mixedL_le_of hF fun x _ _ _ _ _ => hF.projL_mem x

end Aux

variable (H : Subgroup (V ≃ₗ[ZMod p] V))

theorem HasUniqueAxes.exists_mixed
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hua : HasUniqueAxes H) {U L : Submodule (ZMod p) V} (hF : IsFrame H U L) :
    ∃ (x : V) (h : Module.Dual (ZMod p) V),
      TrIn H x h ∧ h ≠ 0 ∧ hF.projU x ≠ 0 ∧ hF.projL x ≠ 0 := by
  obtain ⟨ωU, ωL, hP⟩ := exists_planeForms H hF
  by_contra hcon
  push Not at hcon
  have hinv : ∀ g ∈ H, ∀ y ∈ U, g y ∈ U := by
    refine invariant_of_trIn hgen fun x h hxh hx0 hh0 => ?_
    by_cases hU : hF.projU x = 0
    · refine Or.inr fun y hy => ?_
      obtain ⟨lam, mu, hlm, -, -⟩ := hua.shape_of_planeForms hF hP hx0 hh0 hxh
      rw [hlm y, hP.vanishU_left x y (mem_L_of_projU_eq_zero hF hU),
        hP.vanishL_right x y hy, mul_zero, mul_zero, add_zero]
    · exact Or.inl (mem_U_of_projL_eq_zero hF (hcon x h hxh hh0 hU))
  rcases hirr U hinv with hbot | htop
  · have h2 := hF.2.1
    rw [hbot, finrank_bot] at h2
    omega
  · have hdisj : Disjoint (⊤ : Submodule (ZMod p) V) L := htop ▸ hF.1.disjoint
    have h2 := hF.2.2.1
    rw [top_disjoint.mp hdisj, finrank_bot] at h2
    omega

private theorem le_mixedL
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hua : HasUniqueAxes H) {U L : Submodule (ZMod p) V} (hF : IsFrame H U L) :
    L ≤ mixedL hF := by
  obtain ⟨ωU, ωL, hP⟩ := exists_planeForms H hF
  obtain ⟨x₀, h₀, hx₀, hh₀, hU₀, hL₀⟩ := hua.exists_mixed H hirr hgen hF
  have hl₀ : hF.projL x₀ ∈ mixedL hF := mem_mixedL hF hx₀ hh₀ hU₀ hL₀
  have hcentre : ∀ (v : V) (f : Module.Dual (ZMod p) V), TrIn H v f → v ≠ 0 → f ≠ 0 →
      v ∈ U ⊔ mixedL hF := by
    intro v f hvf hv0 hf0
    by_cases hLv : hF.projL v = 0
    · exact Submodule.mem_sup_left (mem_U_of_projL_eq_zero hF hLv)
    by_cases hUv : hF.projU v = 0
    swap
    · rw [← hF.projU_add_projL v]
      exact Submodule.add_mem_sup (hF.projU_mem v) (mem_mixedL hF hvf hf0 hUv hLv)
    have hvL : v ∈ L := mem_L_of_projU_eq_zero hF hUv
    have hvp : hF.projL v = v := hF.projL_of_mem hvL
    refine Submodule.mem_sup_right ?_
    by_contra hvM
    obtain ⟨lam, mu, hshape, -, hmu⟩ := hua.shape_of_planeForms hF hP hv0 hf0 hvf
    have hmu0 : mu ≠ 0 := hmu hLv
    have hfy : ∀ y, f y = mu * ωL v y := fun y => by
      rw [hshape y, hP.vanishU_left v y hvL, mul_zero, zero_add]
    have hfx₀ : f x₀ ≠ 0 := by
      rw [hfy, hP.right_projL hF]
      refine mul_ne_zero hmu0 fun h0 => hvM ?_
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
        (hP.kerL v hvL hv0 _ (hF.projL_mem x₀) h0)
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ha
        exact hL₀ ha.symm
      have hv : v = a⁻¹ • hF.projL x₀ := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [hv]
      exact (mixedL hF).smul_mem _ hl₀
    have hsmul : f x₀ • v ∈ mixedL hF → v ∈ mixedL hF := fun hmem => by
      have := (mixedL hF).smul_mem (f x₀)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hfx₀, one_smul] at this
    obtain ⟨t, ht, htx⟩ := hvf.2
    have hconj := hx₀.conj ht
    have hU' : hF.projU (t x₀) = hF.projU x₀ := by
      rw [htx, map_add, map_smul, hF.projU_of_mem_L hvL, smul_zero, add_zero]
    have hL' : hF.projL (t x₀) = hF.projL x₀ + f x₀ • v := by
      rw [htx, map_add, map_smul, hvp]
    have hax : h₀ ∘ₗ t.symm.toLinearMap ≠ 0 := by
      intro h0
      refine hh₀ (LinearMap.ext fun z => ?_)
      simpa using LinearMap.congr_fun h0 (t z)
    have hLt : hF.projL (t x₀) ≠ 0 := by
      intro h0
      rw [hL'] at h0
      refine hvM (hsmul ?_)
      rw [eq_neg_of_add_eq_zero_right h0]
      exact (mixedL hF).neg_mem hl₀
    have hmem : hF.projL (t x₀) ∈ mixedL hF :=
      mem_mixedL hF hconj hax (by rw [hU']; exact hU₀) hLt
    refine hvM (hsmul ?_)
    have hdiff : f x₀ • v = hF.projL (t x₀) - hF.projL x₀ := by
      rw [hL']
      abel
    rw [hdiff]
    exact (mixedL hF).sub_mem hmem hl₀
  have hinv : ∀ g ∈ H, ∀ y ∈ U ⊔ mixedL hF, g y ∈ U ⊔ mixedL hF :=
    invariant_of_trIn hgen fun x h hxh hx0 hh0 => Or.inl (hcentre x h hxh hx0 hh0)
  have hZ : U ⊔ mixedL hF = ⊤ := by
    rcases hirr _ hinv with hbot | htop
    · have hU : U = ⊥ := le_bot_iff.mp (hbot ▸ le_sup_left)
      have h2 := hF.2.1
      rw [hU, finrank_bot] at h2
      omega
    · exact htop
  intro l hl
  have hlZ : l ∈ U ⊔ mixedL hF := by
    rw [hZ]
    exact Submodule.mem_top
  obtain ⟨u, hu, m, hm, rfl⟩ := Submodule.mem_sup.mp hlZ
  have hu0 : u = 0 := by
    refine Submodule.disjoint_def.mp hF.1.disjoint u hu ?_
    have := L.sub_mem hl (mixedL_le_L hF hm)
    rwa [add_sub_cancel_right] at this
  rw [hu0, zero_add]
  exact hm

theorem HasUniqueAxes.exists_mixed_projL_notMem_span
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hua : HasUniqueAxes H) {U L : Submodule (ZMod p) V} (hF : IsFrame H U L) {l₁ : V}
    (_hl₁ : l₁ ∈ L) :
    ∃ (x : V) (h : Module.Dual (ZMod p) V), TrIn H x h ∧ h ≠ 0 ∧ hF.projU x ≠ 0 ∧
      hF.projL x ≠ 0 ∧ hF.projL x ∉ Submodule.span (ZMod p) {l₁} := by
  by_contra hcon
  push Not at hcon
  have hle : L ≤ Submodule.span (ZMod p) {l₁} :=
    (le_mixedL H hirr hgen hua hF).trans
      (mixedL_le_of hF fun x h hxh hh hU hL => hcon x h hxh hh hU hL)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {l₁}) ≤ 1 :=
    finrank_le_one ⟨l₁, Submodule.mem_span_singleton_self l₁⟩ fun w => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
      exact ⟨c, Subtype.ext hc⟩
  have h3 := hF.2.2.1
  omega

end CFSG.RankThree.PartOne.LIT
