module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ct_d4a_plane_regular
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {xV y : V}
    (hxx : Q xV = 0) (hxy : QuadraticMap.polar Q xV y ≠ 0) :
    (Q.restrict (Submodule.span (ZMod 3) ({xV, y} : Set V))).Nondegenerate := by
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  set W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) ({xV, y} : Set V)
  have hB : LinearMap.BilinForm.IsSymm (QuadraticMap.polarBilin Q) :=
    QuadraticMap.isSymm_polarBilin Q
  have hBx : QuadraticMap.polarBilin Q xV xV = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hxx]
    simp
  have hBxy : QuadraticMap.polarBilin Q xV y ≠ 0 := by
    rwa [QuadraticMap.polarBilin_apply_apply]
  have hByx : QuadraticMap.polarBilin Q y xV ≠ 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply]
    exact hBxy
  refine (QuadraticMap.nondegenerate_polar_iff (Q := Q.restrict W)).mp ?_
  rw [QuadraticMap.polarBilin_restrict]
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (B := (QuadraticMap.polarBilin Q).domRestrict₁₂ W W) ?_).mpr ?_
  · exact hB.isRefl.domRestrict W
  · intro w hw
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp w.2
    have hxW : xV ∈ W := Submodule.subset_span (by simp)
    have hyW : y ∈ W := Submodule.subset_span (by simp)
    have hwx : QuadraticMap.polarBilin Q (w : V) xV = 0 := by
      have := hw ⟨xV, hxW⟩
      simpa [LinearMap.domRestrict₁₂_apply] using this
    have hwy : QuadraticMap.polarBilin Q (w : V) y = 0 := by
      have := hw ⟨y, hyW⟩
      simpa [LinearMap.domRestrict₁₂_apply] using this
    have hb0 : b = 0 := by
      have h := hwx
      rw [← hab] at h
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hBx,
        smul_zero, zero_add] at h
      rcases smul_eq_zero.mp h with hb | hyx
      · exact hb
      · exact absurd hyx hByx
    have ha0 : a = 0 := by
      have h := hwy
      rw [← hab, hb0] at h
      simp only [zero_smul, add_zero, map_smul, LinearMap.smul_apply] at h
      rcases smul_eq_zero.mp h with ha | hxy'
      · exact ha
      · exact absurd hxy' hBxy
    refine Subtype.ext ?_
    simp [← hab, ha0, hb0]

private lemma ct_d4a_repr_regular
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (U : Submodule (ZMod 3) V)
    (hU : (Q.restrict U).Nondegenerate) (hd : 2 ≤ Module.finrank (ZMod 3) U)
    {c : ZMod 3} (hc : c ≠ 0) : ∃ u : U, Q (u : V) = c := by
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hU' : (QuadraticMap.polarBilin (Q.restrict U)).Nondegenerate :=
    (QuadraticMap.nondegenerate_polar_iff (Q := Q.restrict U)).mpr hU
  obtain ⟨g, hg⟩ := exists_orthReflOfNorm (Q := Q.restrict U) hU' hd hc
  obtain ⟨v, -, hv, -⟩ := hg
  exact ⟨v, by simpa [QuadraticMap.restrict_apply] using hv⟩

private lemma ct_d4a_perp_of_regular
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQnd : Q.Nondegenerate)
    {xV : V} {W : Submodule (ZMod 3) V} (hWreg : (Q.restrict W).Nondegenerate)
    (hxW : xV ∈ W) (hdim : Module.finrank (ZMod 3) W + 2 ≤ Module.finrank (ZMod 3) V)
    {c : ZMod 3} (hc : c ≠ 0) :
    ∃ w : V, QuadraticMap.polar Q xV w = 0 ∧ Q w = c := by
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  let B := QuadraticMap.polarBilin Q
  have hBnd : B.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff (Q := Q)).mpr hQnd
  let U : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal B W
  have hUreg : (Q.restrict U).Nondegenerate := by
    simpa only [U, B] using
      QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal (Q := Q) hQnd hWreg
  have hdU : 2 ≤ Module.finrank (ZMod 3) U := by
    have hfin : Module.finrank (ZMod 3) U =
        Module.finrank (ZMod 3) V - Module.finrank (ZMod 3) W :=
      LinearMap.BilinForm.finrank_orthogonal hBnd W
    omega
  obtain ⟨u, hu⟩ := ct_d4a_repr_regular U hUreg hdU hc
  refine ⟨(u : V), ?_, hu⟩
  have hmem : (u : V) ∈ LinearMap.BilinForm.orthogonal B W := u.2
  have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) xV hxW
  rwa [QuadraticMap.polarBilin_apply_apply] at this

private lemma ct_d4a_perp_vec
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : PolarNondeg3 Q)
    (hd : Module.finrank (ZMod 3) V = 5)
    {xV : V} (hxV : xV ≠ 0) {c : ZMod 3} (hc : c ≠ 0) :
    ∃ w : V, QuadraticMap.polar Q xV w = 0 ∧ Q w = c := by
  classical
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hQnd : Q.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff (Q := Q)).mp hQ
  have hB : LinearMap.BilinForm.IsSymm (QuadraticMap.polarBilin Q) :=
    QuadraticMap.isSymm_polarBilin Q
  by_cases hxx : Q xV = 0
  · obtain ⟨y, hy⟩ : ∃ y, QuadraticMap.polarBilin Q xV y ≠ 0 := by
      by_contra h
      push Not at h
      exact hxV (hQ.1 xV h)
    have hxy : QuadraticMap.polar Q xV y ≠ 0 := by
      rwa [QuadraticMap.polarBilin_apply_apply] at hy
    refine ct_d4a_perp_of_regular hQnd (ct_d4a_plane_regular hxx hxy)
      (Submodule.subset_span (by simp)) ?_ hc
    have hle : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) ({xV, y} : Set V)) ≤ 2 := by
      have h := finrank_span_finset_le_card (R := ZMod 3) ({xV, y} : Finset V)
      rw [Finset.coe_pair] at h
      exact h.trans (by simpa using Finset.card_le_two (a := xV) (b := y))
    omega
  · have hBxx : QuadraticMap.polarBilin Q xV xV ≠ 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul]
      exact mul_ne_zero (by decide) hxx
    refine ct_d4a_perp_of_regular hQnd ?_ (Submodule.mem_span_singleton_self xV) ?_ hc
    · refine (QuadraticMap.nondegenerate_polar_iff (Q := Q.restrict
        (Submodule.span (ZMod 3) ({xV} : Set V)))).mp ?_
      rw [QuadraticMap.polarBilin_restrict]
      exact (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
        (B := QuadraticMap.polarBilin Q) hB.isRefl).mpr
        (LinearMap.isCompl_span_singleton_orthogonal hBxx)
    · have hspan : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) ({xV} : Set V)) = 1 :=
        finrank_span_singleton hxV
      omega

private lemma ct_d4a_refl_fixing
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : PolarNondeg3 Q)
    (hd : Module.finrank (ZMod 3) V = 5)
    {xV : V} (hxV : xV ≠ 0) {c : ZMod 3} (hc : c ≠ 0) :
    ∃ g' : V ≃ₗ[ZMod 3] V, OrthReflOfNorm Q c g' ∧ g' xV = xV := by
  obtain ⟨w, hwx, hw⟩ := ct_d4a_perp_vec hQ hd hxV hc
  have : Invertible (Q w) := invertibleOfNonzero (by rw [hw]; exact hc)
  refine ⟨((QuadraticMap.reflectionOrthogonal Q w : QuadraticMap.orthogonalGroup Q) :
      V ≃ₗ[ZMod 3] V), ⟨w, inferInstance, hw, rfl⟩, ?_⟩
  rw [QuadraticMap.coe_reflectionOrthogonal]
  exact QuadraticMap.reflection_apply_of_polar_eq_zero Q w
    (by rw [QuadraticMap.polar_comm]; exact hwx)

theorem ggOrthD4_unreal
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hd : Module.finrank (ZMod 3) V = 5)
    {c₁ c₂ : ZMod 3} (hc₂ : c₂ ≠ 0) (hne : c₁ ≠ c₂)
    (hLcls : ∀ a ∈ ggAutomizer L Bs, GGIsReflection 3 a → OrthReflOfNorm Q c₁ (ggLin (p := 3) ι a))
    {s : MulAut ↥Bs} (hsr : GGIsReflection 3 s)
    (hsc : OrthReflOfNorm Q c₂ (ggLin (p := 3) ι s)) : ¬ GGRealized 3 Bs s := by
  intro hsR
  have hconf : GGConfig 3 B Bs x L D J := S.cfg.1.1
  obtain ⟨hp, -, hxBs, -, -⟩ := hconf.tableB_facts
  have hx1 : x ≠ 1 := hconf.1.2.2.2.2.2.2.1.2.2.1
  let xV : V := ι (Additive.ofMul ⟨x, hxBs⟩)
  have hxV : xV ≠ 0 := by
    intro h
    apply hx1
    have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      apply ι.injective
      simpa [xV] using h
    exact congrArg Subtype.val h1
  have hd2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by omega)
  obtain ⟨g', hg'refl, hg'fix⟩ := ct_d4a_refl_fixing (Q := Q) S.nondeg hd hxV hc₂
  obtain ⟨e, he, heq⟩ :=
    orthReflOfNorm_conjugate (Q := Q) S.nondeg hd2 hsc hg'refl
  obtain ⟨a, ha, hae⟩ :=
    (S.orth e).mpr (QuadraticMap.mem_orthogonalGroup_iff.mp he)
  have hAinf_le : ggAInf 3 B Bs x L D J ≤ ggAutomizer ⊤ Bs := by
    rw [ggAInf]
    refine sup_le (ggAutomizer_mono Bs le_top) ?_
    refine iSup_le fun y => iSup_le fun K => iSup_le fun _ =>
      ggAutomizer_mono Bs le_top
  obtain ⟨g0, -, hg0N, ha_eq⟩ := eq_ggConjAut_of_mem_ggAutomizer (hAinf_le ha)
  let ψ : MulAut ↥Bs := ggConjAut Bs hg0N
  let s' : MulAut ↥Bs := ψ * s * ψ⁻¹
  have hψa : ψ = a := ha_eq.symm
  have hs'R : GGRealized 3 Bs s' := GGRealized.conj hp hsR hg0N
  have hs'r : GGIsReflection 3 s' := hsr.conj' ψ
  have hs'Lin : ggLin (p := 3) ι s' = g' := by
    simp only [s', map_mul, map_inv, hψa, hae]
    exact heq.symm
  have hb : s' ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    have h := hg'fix
    rw [← hs'Lin] at h
    have h2 : ι (Additive.ofMul (s' ⟨x, hxBs⟩)) = ι (Additive.ofMul ⟨x, hxBs⟩) := by
      simpa [xV, ggLin_apply_ofMul] using h
    exact Additive.ofMul.injective (ι.injective h2)
  have hs'fix : x ∈ ggFixG Bs s' :=
    Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩, hb, rfl⟩
  have hs'ind : s' ∈ ggInduced ⊤ Bs := hs'R.mem_ggInduced_top
  have hP3 : GGFixedRealizedInL 3 Bs L x :=
    ggFixedRealizedInL_of_config hL hP hconf S.cfg.1.2.2.1.1
  have hs'L : s' ∈ ggAutomizer L Bs := hP3 s' hs'r hs'ind hs'fix hs'R
  have hc1 : OrthReflOfNorm Q c₁ (ggLin (p := 3) ι s') := hLcls s' hs'L hs'r
  rw [hs'Lin] at hc1
  exact hne (orthReflOfNorm_unique hc1 hg'refl)

end CFSG.StandardType.OrthF3

end
