module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFinal
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldRad
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthMinusLayer

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth

section Radical

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {a : V ≃ₗ[K] V}

theorem exists_special_radical_elt (hx : OddOrderIsometry Q p a) (hp2 : Odd p) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors a.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) {Y : Submodule K V} (hYa : ∀ y ∈ Y, a y ∈ Y)
    (hY0 : Y ≠ ⊥) (hYh : Y ≤ primaryComponent a.toLinearMap h) (hYQ : ∀ y ∈ Y, Q y = 0) :
    ∃ g ∈ specialBlock Q a h, g ≠ 1 ∧ (∀ y ∈ Y, g y = y) ∧ ∀ v, g v - v ∈ Y := by
  classical
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  set σ : AdjoinRoot h →+* AdjoinRoot h :=
    ((frobPow K (AdjoinRoot h) d : AdjoinRoot h ≃ₐ[K] AdjoinRoot h) :
      AdjoinRoot h →+* AdjoinRoot h) with hσ
  have hsm₁' : ∀ (c : AdjoinRoot h) u w, H (c • u) w = σ c * H u w := fun c u w => by rw [hsm₁]; rfl
  have hsymm' : ∀ u w, H w u = σ (H u w) := fun u w => by rw [hsymm]; rfl
  have hYp : ∀ y ∈ Y, ∀ y' ∈ Y, QuadraticMap.polar Q y y' = 0 := fun y hy y' hy' => by
    have h1 := hYQ (y + y') (Y.add_mem hy hy')
    rw [QuadraticMap.polar, h1, hYQ y hy, hYQ y' hy']
    simp
  have hHY : ∀ w w' : primaryComponent a.toLinearMap h, (w : V) ∈ Y → (w' : V) ∈ Y →
      H w w' = 0 := by
    intro w w' hw hw'
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot h) fun c => ?_
    rw [htr w w' c]
    exact hYp _ hw _ (smul_mem_of_stable hYa c w' hw')
  obtain ⟨e, heY, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  set u : primaryComponent a.toLinearMap h := ⟨e, hYh heY⟩ with hu
  have he : H u u = 0 := hHY u u heY heY
  have h2 : (2 : AdjoinRoot h) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot h)) 2, CharTwo.two_eq_zero, map_zero]
  have ha : σ 1 = -1 := by
    rw [map_one]
    exact (neg_eq_of_add_eq_zero_left (by rw [one_add_one_eq_two, h2])).symm
  set tv := unitaryTransvection H hadd₂ hsm₂ he (1 : AdjoinRoot h) with htv
  have hpres : ∀ y y' : primaryComponent a.toLinearMap h,
      H ((tv : Module.End (AdjoinRoot h) (primaryComponent a.toLinearMap h)) y)
        ((tv : Module.End (AdjoinRoot h) (primaryComponent a.toLinearMap h)) y') = H y y' := by
    intro y y'
    rw [htv, unitaryTransvection_apply, unitaryTransvection_apply]
    exact hermitian_transvection_preserves σ H hadd₁ hadd₂ hsm₁' hsm₂ hsymm' he ha y y'
  obtain ⟨g, hg⟩ := (hx.mem_range_blockGL_selfDual_iff hh hne1 hself H htr tv).mpr hpres
  have hgV : ∀ y : primaryComponent a.toLinearMap h, g.1 (y : V) =
      (y : V) + (((H u y) • u : primaryComponent a.toLinearMap h) : V) := by
    intro y
    rw [← coe_blockGL h g y, hg, htv, unitaryTransvection_apply, one_mul]
    rfl
  have hUeq : orbitSpace a.toLinearMap h = primaryComponent a.toLinearMap h := by
    rw [orbitSpace, ← hself, sup_idem]
  have hR := (mem_supportedBlock.mp g.2).2
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, ?_, ?_, ?_⟩
  · rw [blockDet_apply, hg, htv]
    exact det_unitaryTransvection H hadd₂ hsm₂ he 1
  ·
    have hu0 : u ≠ 0 := fun h0 => he0 (congrArg Subtype.val h0)
    obtain ⟨w, hw, hw0⟩ : ∃ w ∈ primaryComponent a.toLinearMap h,
        QuadraticMap.polar Q e w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu0 (Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself (hYh heY) hall))
    set y : primaryComponent a.toLinearMap h := ⟨w, hw⟩ with hy
    have hHy : H u y ≠ 0 := by
      intro h0
      have := htr u y 1
      rw [h0, zero_mul, map_zero, one_smul] at this
      exact hw0 this.symm
    intro hg1
    have := hgV y
    rw [hg1] at this
    have h3 : (((H u y) • u : primaryComponent a.toLinearMap h) : V) = 0 := by
      have h4 : ((1 : V ≃ₗ[K] V) (y : V)) = (y : V) := rfl
      rw [h4] at this
      exact (add_eq_left.mp this.symm)
    exact smul_ne_zero hHy hu0 (Subtype.ext h3)
  · intro y hy
    have h0 : H u ⟨y, hYh hy⟩ = 0 := hHY u ⟨y, hYh hy⟩ heY hy
    have := hgV ⟨y, hYh hy⟩
    rw [h0, zero_smul] at this
    simpa using this
  · intro v
    obtain ⟨u', hu', r, hr, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
    rw [hUeq] at hu'
    have h1 := hgV ⟨u', hu'⟩
    rw [map_add, hR r hr, h1]
    have : (u' : V) + (((H u ⟨u', hu'⟩) • u : primaryComponent a.toLinearMap h) : V) + r -
        (u' + r) = (((H u ⟨u', hu'⟩) • u : primaryComponent a.toLinearMap h) : V) := by abel
    rw [this]
    exact smul_mem_of_stable hYa _ u heY

theorem exists_twoSubgroup_special (hx : OddOrderIsometry Q p a) (hp2 : Odd p) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors a.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) {A : Subgroup (V ≃ₗ[K] V)}
    (hAM : ∀ g ∈ A, g ∈ isometryCentralizer Q a) (haA : a ∈ A) {Y : Submodule K V}
    (hYinv : ∀ g ∈ A, ∀ y ∈ Y, g y ∈ Y) (hY0 : Y ≠ ⊥)
    (hYh : Y ≤ primaryComponent a.toLinearMap h) (hYQ : ∀ y ∈ Y, Q y = 0) :
    ∃ U : Subgroup (V ≃ₗ[K] V), U ≤ specialBlock Q a h ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
  classical
  have hYp : ∀ y ∈ Y, ∀ y' ∈ Y, QuadraticMap.polar Q y y' = 0 := fun y hy y' hy' => by
    have h1 := hYQ (y + y') (Y.add_mem hy hy')
    rw [QuadraticMap.polar, h1, hYQ y hy, hYQ y' hy']
    simp
  obtain ⟨g, hgF, hg1, hgY, hgv⟩ := exists_special_radical_elt hx hp2 hh hne1 hself
    (fun y hy => hYinv a haA y hy) hY0 hYh hYQ
  refine ⟨LIDTwDF.radSub Q Y hYp (specialBlock Q a h), fun g hg => hg.1, ?_,
    LIDTwDF.isPGroup_radSub, ?_⟩
  · intro hbot
    have hmem : g ∈ LIDTwDF.radSub Q Y hYp (specialBlock Q a h) :=
      ⟨hgF, hgY, fun v _ => hgv v, fun v => LIDTwDF.subset_perp hYp (hgv v)⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hg1 hmem
  · intro s hs u hu
    exact LIDTwDF.conj_mem_radSub (fun v => (mem_isometryCentralizer.mp (hAM s hs)).1 v)
      (fun y hy => hYinv s hs y hy) (fun y hy => hYinv s⁻¹ (A.inv_mem hs) y hy)
      (fun h' hh' => conj_mem_specialBlock (hAM s hs) hh') hu

theorem exists_twoSubgroup_fixed (hx : OddOrderIsometry Q p a) {A : Subgroup (V ≃ₗ[K] V)}
    (hAM : ∀ g ∈ A, g ∈ isometryCentralizer Q a) (h6 : 6 ≤ finrank K (fixedSpace a))
    {Y' : Submodule K V} (hY'0 : Y' ≠ ⊥) (hY'Q : ∀ y ∈ Y', Q y = 0) (hY'W : Y' ≤ fixedSpace a)
    (hY'inv : ∀ g ∈ A, ∀ y ∈ Y', g y ∈ Y') :
    ∃ U : Subgroup (V ≃ₗ[K] V), U ≤ supportedFixedDerived Q a ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
  classical
  set W : Submodule K V := fixedSpace a with hW
  set QW : QuadraticForm K W := Q.comp W.subtype with hQW
  have hQWnd := hx.polarBilin_fixed_nondegenerate
  set YW : Submodule K W := Y'.comap W.subtype with hYW
  have hmemYW : ∀ y : W, y ∈ YW ↔ (y : V) ∈ Y' := fun y => Iff.rfl
  have hYW0 : YW ≠ ⊥ := by
    intro h
    obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY'0
    have hmem : (⟨y, hY'W hyY⟩ : W) ∈ YW := hyY
    rw [h, Submodule.mem_bot] at hmem
    exact hy0 (congrArg Subtype.val hmem)
  have hYWQ : ∀ y ∈ YW, QW y = 0 := fun y hy => hY'Q (y : V) hy
  have hYWp : ∀ y ∈ YW, ∀ y' ∈ YW, QuadraticMap.polar QW y y' = 0 := by
    intro y hy y' hy'
    have h1 := hYWQ (y + y') (YW.add_mem hy hy')
    rw [QuadraticMap.polar, hYWQ y hy, hYWQ y' hy', h1]
    simp
  set H : Subgroup (W ≃ₗ[K] W) := orthDerived QW with hH
  set UW := LIDTwDF.radSub QW YW hYWp H with hUW
  obtain ⟨x₁, hx₁Y, w₁, hw₁P, hsing, hind⟩ := LIDTwDF.exists_siegel_pair hQWnd
    (by omega : 5 ≤ finrank K W) hYW0 hYWQ
  have hσH : OrthBstarOdd.siegEquiv hsing ∈ H := by
    by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ u ∈ T, QW u = 0
    · exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQWnd hT
        (OrthBstarOdd.siegEquiv_mem_omegaGroup hQWnd hsing)
    · push Not at hT
      obtain ⟨k, hk⟩ := even_finrank_of_regular QW hQWnd
      have h6' : finrank K W = 6 := by
        by_contra h6'
        obtain ⟨T, hT3, hT0⟩ := exists_totallySingular_three QW hQWnd (by omega)
        obtain ⟨u, hu, hu0⟩ := hT T hT3
        exact hu0 (hT0 u hu)
      exact CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_six hQWnd h6' hT
        (OrthBstarOdd.siegEquiv_mem_omegaGroup hQWnd hsing)
  have hσU : OrthBstarOdd.siegEquiv hsing ∈ UW :=
    LIDTwDF.siegEquiv_mem_radSub hsing hx₁Y hw₁P hσH
  have hσ1 : OrthBstarOdd.siegEquiv hsing ≠ 1 := OrthBstarOdd.siegEquiv_ne_one hQWnd hsing hind
  have hσO : OrthBstarOdd.siegEquiv hsing ∈ TauCeti.QuadraticMap.orthogonalGroup QW :=
    OrthBstarOdd.siegEquiv_mem_orthogonalGroup hsing
  set Ũ : Subgroup (V ≃ₗ[K] V) :=
    (UW.comap (restrictFixed Q a)).map (supportedBlock Q a (X - 1)).subtype with hŨ
  have hŨD : Ũ ≤ supportedFixedDerived Q a := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : restrictFixed Q a g ∈ UW := hg
    exact ⟨g, hg'.1, rfl⟩
  refine ⟨Ũ, hŨD, ?_, ?_, ?_⟩
  · intro hbot
    obtain ⟨g, hg⟩ := restrictFixed_surjective hx _ hσO
    have hgU : (g : V ≃ₗ[K] V) ∈ Ũ := ⟨g, by simpa [hg] using hσU, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hgU
    have hg1 : g = 1 := Subtype.ext hgU
    rw [hg1, map_one] at hg
    exact hσ1 hg.symm
  · have h1 : IsPGroup 2 UW := LIDTwDF.isPGroup_radSub
    have h2 : IsPGroup 2 (UW.comap (restrictFixed Q a)) :=
      h1.comap_of_injective _ (restrictFixed_injective hx)
    exact h2.map _
  · intro s hs u hu
    have hat := hAM s hs
    have hacent : s ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hat).2
    have hW1 : ∀ w ∈ W, s w ∈ W := fun w hw => mem_fixedSpace_of_apply hacent hw
    have hW2 : ∀ w ∈ W, s.symm w ∈ W := fun w hw =>
      mem_fixedSpace_of_apply (symm_mem_centralizer a hacent) hw
    set φ : W ≃ₗ[K] W := restrictEquiv W s hW1 hW2 with hφ
    have hφapp : ∀ w : W, ((φ w : W) : V) = s (w : V) := fun w => rfl
    have hφsymm : ∀ w : W, (((φ⁻¹) w : W) : V) = s.symm (w : V) := fun w => rfl
    have hφQ : ∀ w, QW (φ w) = QW w := fun w => by
      have := (mem_isometryCentralizer.mp hat).1 (w : V)
      simpa [hQW, QuadraticMap.comp_apply, hφapp] using this
    have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup QW :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hφQ
    have hφY : ∀ y ∈ YW, φ y ∈ YW := fun y hy => hY'inv s hs (y : V) hy
    have hφYi : ∀ y ∈ YW, φ⁻¹ y ∈ YW := by
      intro y hy
      have : s.symm (y : V) = ((s⁻¹ : V ≃ₗ[K] V)) (y : V) := rfl
      rw [hmemYW, hφsymm, this]
      exact hY'inv s⁻¹ (A.inv_mem hs) (y : V) hy
    obtain ⟨g, hg, hgu⟩ := hu
    have hconj : s * g.1 * s⁻¹ ∈ supportedBlock Q a (X - 1) :=
      conj_mem_supportedBlock hat g.2
    have hrf : restrictFixed Q a ⟨s * g.1 * s⁻¹, hconj⟩ = φ * restrictFixed Q a g * φ⁻¹ := by
      refine LinearEquiv.ext fun w => Subtype.ext ?_
      rw [coe_restrictFixed]
      simp only [LinearEquiv.mul_apply, hφapp, hφsymm, coe_restrictFixed]
      rfl
    have hmemU : φ * restrictFixed Q a g * φ⁻¹ ∈ UW :=
      LIDTwDF.conj_mem_radSub hφQ hφY hφYi
        (fun h' hh' => IOneOrthEnd.conj_mem_orthDerived' hφO hh') hg
    have : (⟨s * g.1 * s⁻¹, hconj⟩ : ↥(supportedBlock Q a (X - 1))) ∈
        UW.comap (restrictFixed Q a) := by
      show restrictFixed Q a _ ∈ UW
      rw [hrf]
      exact hmemU
    have hgu' : u = g.1 := hgu.symm
    rw [hgu']
    exact ⟨_, this, rfl⟩

end Radical

end SmallOrthUn

end CFSG.StandardType

end
