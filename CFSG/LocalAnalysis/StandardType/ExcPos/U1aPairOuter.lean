module

public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleRankOne
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.LocalAnalysis.StandardType.ExcPos.U1aPairOuterTwo
public import CFSG.LocalAnalysis.StandardType.GGJ4dKernel24
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel


private theorem u1aO1_ratOrbit_eq_of_image_eq {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ) :
    LieCore.ratOrbit ρ Ψ = Ψ := by
  have hiter : ∀ k : ℕ, (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ = Ψ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ', Set.image_comp, ih, h]
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    rw [← hiter k]
    exact Set.mem_image_of_mem _ hδ
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

private theorem u1aO1_curve_map_eq {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {σ : L ≃+* L} {z : ModGL τ L} {α : Fin τ.rank → ℤ}
    (hstep : ∀ c : L, D.step (z * pinnedX τ L α c * z⁻¹) =
      z * pinnedX τ L α (σ c) * z⁻¹) :
    (excCurve α z).map D.step = excCurve α z := by
  have hmem : ∀ x : ModGL τ L, x ∈ excCurve α z ↔
      ∃ c : L, z * pinnedX τ L α c * z⁻¹ = x := by
    intro x
    rw [excCurve, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_rootSubgroup] at hy
      obtain ⟨c, rfl⟩ := hy
      exact ⟨c, by
        change MulAut.conj z (pinnedX τ L α c) = z * pinnedX τ L α c * z⁻¹
        rw [MulAut.conj_apply]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨pinnedX τ L α c, by rw [mem_rootSubgroup]; exact ⟨c, rfl⟩, by
        change MulAut.conj z (pinnedX τ L α c) = z * pinnedX τ L α c * z⁻¹
        rw [MulAut.conj_apply]⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hx
    obtain ⟨c, rfl⟩ := (hmem y).1 hy
    rw [← hxy, hstep c]
    exact (hmem _).2 ⟨σ c, rfl⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    obtain ⟨d, rfl⟩ := σ.surjective c
    exact Subgroup.mem_map.2 ⟨z * pinnedX τ L α d * z⁻¹, (hmem _).2 ⟨d, rfl⟩, hstep d⟩

theorem exists_untwist_root_chi {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {s : ℕ} (hs : 0 < s)
    (hker : ∀ γ ∈ kernelRoots χ, (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ ∈ kernelRoots χ)
    (i : KernelComponent χ) {θ : Fin τ.rank → ℤ} (hθ : θ ∈ componentRoots χ i)
    {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure
      {u : WeylGroup τ | ∃ γ ∈ componentRoots χ i, u = rootReflection γ})
    (hwθ : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] θ = w • θ) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) ∧
      (∀ j : KernelComponent χ, ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots χ j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j)) ∧
      ∀ A : SL2 L, iterHom S.D.step s (z * rootSL2 τ L θ A * z⁻¹) =
        z * rootSL2 τ L θ (Matrix.SpecialLinearGroup.map σ.toRingHom A) * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ s) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * s) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  have hθr : IsRoot τ θ := isRoot_of_mem_componentRoots hθ
  obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s hθr
  obtain ⟨μ', -, hμ'⟩ := iter_step_pinnedX S s (IsRoot.neg hθr)
  have hφθ : ∀ c, iterHom S.D.step s (pinnedX τ L θ c) = pinnedX τ L (w • θ) (μ * σ c) := by
    intro c
    rw [iterHom_eq_iterate, hμ, hwθ, hσc]
  have hφθ' : ∀ c, iterHom S.D.step s (pinnedX τ L (-θ) c) =
      pinnedX τ L (w • -θ) (μ' * σ c) := by
    intro c
    rw [iterHom_eq_iterate, hμ', rho_iterate_neg S, hwθ, smul_neg, hσc]
  obtain ⟨gw, hgwS, hgwM, hgwmaps⟩ := exists_lift_mem_closure_reflections (L := L) i hw
  have hhM : gw⁻¹ ∈ monomialSubgroup τ L := inv_mem hgwM
  have hπ : weylQuotientHom τ L ⟨gw⁻¹, hhM⟩ = w⁻¹ := weylQuotientHom_eq hgwmaps.inv
  obtain ⟨cT, hpin⟩ := outer_exists_pin_root σ (iterHom S.D.step s) hθr hhM hπ hμ0 hφθ hφθ'
  have hy₁ : rootDiagUnit τ cT * gw⁻¹ ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) :=
    mul_mem (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup cT))
      (Subgroup.mem_sup_right (inv_mem ((rootSpan_mono fun γ hγ => hγ.1) hgwS)))
  obtain ⟨z, hzZ, hφz⟩ := exists_lang_torus_sup_kernelRoots S hs hker hy₁
  refine ⟨σ, z, hσc, hzZ, mem_componentRootSpan_iff_conj_of_mem hzZ, fun A => ?_⟩
  rw [map_mul, map_mul, map_inv, hφz, ← hpin A]
  group

theorem exists_stable_pair_outer {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) (Δ : LangDatum τ GGL) (hq : Δ.q = 2 ^ f) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap Δ ρ) (hfin : Finite Δ.model) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a₁ a₂ : Fin τ.rank → GGLˣ} (ha₁ : rootDiagUnit τ a₁ ∈ Δ.torus)
    (ha₂ : rootDiagUnit τ a₂ ∈ Δ.torus) (hap₁ : ∀ j, a₁ j ^ p = 1)
    (hap₂ : ∀ j, a₂ j ^ p = 1) (hne : rootDiagUnit τ a₁ ≠ 1 ∨ rootDiagUnit τ a₂ ≠ 1)
    (iJ : KernelComponent (LieCore.jointChar a₁ a₂))
    (hb : componentOrbitLength ρ (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 1)
    (houter : ¬ twistInner (componentRoots (LieCore.jointChar a₁ a₂) iJ) ρ)
    (hqs : CFSG.Assembly.IsQuasisimple
      ↥(LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ))) :
    ∃ (α : Fin τ.rank → ℤ) (w : ModGL τ GGL),
      α ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ ∧
      w ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (LieCore.jointChar a₁ a₂)) ∧
      (excCurve α w).map Δ.step = excCurve α w ∧
      (excCurve (-α) w).map Δ.step = excCurve (-α) w ∧
      excCurve α w ⊓ Δ.model ≤
        LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) ∧
      excCurve (-α) w ⊓ Δ.model ≤
        LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by
  classical
  obtain ⟨S, hSD, hSρ⟩ := LieCore.exists_langSetup_of_datum Δ ρ hρ hfin hf hq
  let χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ × GGLˣ := LieCore.jointChar a₁ a₂
  let Ψ : Set (Fin τ.rank → ℤ) := componentRoots χ iJ
  have himg : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ :=
    CFSG.StandardType.LangRat.j4d_image_eq_of_componentOrbitLength_eq_one hb
  have hrat : LieCore.ratOrbit ρ Ψ = Ψ := u1aO1_ratOrbit_eq_of_image_eq himg
  have hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ := by
    intro γ hγ
    rw [kernelRoots] at hγ ⊢
    refine ⟨(hρ.isRoot_iff γ).2 hγ.1, ?_⟩
    have h1 : rootChar a₁ (ρ γ) = 1 := by
      rw [hρ.rootChar_eq a₁ ha₁ γ hγ.1]
      have h := congrArg Prod.fst hγ.2
      change rootChar a₁ γ = 1 at h
      rw [h, one_pow]
    have h2 : rootChar a₂ (ρ γ) = 1 := by
      rw [hρ.rootChar_eq a₂ ha₂ γ hγ.1]
      have h := congrArg Prod.snd hγ.2
      change rootChar a₂ γ = 1 at h
      rw [h, one_pow]
    show (rootChar a₁ (ρ γ), rootChar a₂ (ρ γ)) = 1
    rw [h1, h2]
    rfl
  obtain ⟨⟨θ, hθk⟩, hθi⟩ := Quotient.exists_rep iJ
  have hθ : θ ∈ Ψ := ⟨hθk, hθi⟩
  have hθr : IsRoot τ θ := isRoot_of_mem_componentRoots hθ
  have hρθ : ρ θ ∈ Ψ := by
    have h := Set.mem_image_of_mem (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) hθ
    rwa [himg] at h
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots iJ
  obtain ⟨w₀, hw₀, hw₀θ⟩ := outer_exists_smul_eq hΨ hθ hρθ (hρ.iform_eq θ θ).symm
  obtain ⟨σ, z, hσ, hzZ, hnorm, hzuntw⟩ :=
    exists_untwist_root_chi (χ := χ) (s := 1) S one_pos
      (by simpa [Function.iterate_one, hSρ] using hker) iJ hθ hw₀
      (by rw [Function.iterate_one, hSρ]; exact hw₀θ.symm)
  have hσq : ∀ c, σ c = c ^ (2 ^ f) := by
    intro c
    rw [hσ c, pow_one, hSD, hq]
  have hstepΔ : ∀ A : SL2 GGL, Δ.step (z * rootSL2 τ GGL θ A * z⁻¹) =
      z * rootSL2 τ GGL θ (Matrix.SpecialLinearGroup.map σ.toRingHom A) * z⁻¹ := by
    intro A
    have h := hzuntw A
    rwa [iterHom_eq_iterate, Function.iterate_one, hSD] at h
  set ε : ℤ := (pinnedData τ θ).2.2 with hεdef
  have hε2 : ε * ε = 1 := by
    rcases pinnedSign_eq τ θ with h | h <;> rw [hεdef, h] <;> norm_num
  have hεc : ∀ x : GGL, ε • (ε • x) = x := by
    intro x
    rw [← mul_smul, hε2, one_smul]
  have hstepX : ∀ c : GGL, Δ.step (z * pinnedX τ GGL θ c * z⁻¹) =
      z * pinnedX τ GGL θ (σ c) * z⁻¹ := by
    intro c
    have h1 : rootSL2 τ GGL θ (uSL (ε • c)) = pinnedX τ GGL θ c := by
      rw [rootSL2_uSL_eq, ← hεdef, hεc]
    have h2 : Matrix.SpecialLinearGroup.map σ.toRingHom (uSL (ε • c)) =
        uSL (σ (ε • c)) := map_uSL σ.toRingHom (ε • c)
    have h3 : σ (ε • c) = ε • σ c := map_zsmul σ.toRingHom ε c
    have hA := hstepΔ (uSL (ε • c))
    rw [h1, h2, h3, rootSL2_uSL_eq, ← hεdef, hεc] at hA
    exact hA
  obtain ⟨η, hη2, hη⟩ := exists_rootSL2_vSL_eq (K := GGL) (β := θ) hθr
  have hση : σ η = η := sq_eq_one_fixed σ hη2
  have hηc : ∀ x : GGL, η * (η * x) = x := by
    intro x
    rw [← mul_assoc, hη2, one_mul]
  have hstepXneg : ∀ c : GGL, Δ.step (z * pinnedX τ GGL (-θ) c * z⁻¹) =
      z * pinnedX τ GGL (-θ) (σ c) * z⁻¹ := by
    intro c
    have h1 : rootSL2 τ GGL θ (vSL (η * c)) = pinnedX τ GGL (-θ) c := by
      rw [hη, hηc]
    have h2 : Matrix.SpecialLinearGroup.map σ.toRingHom (vSL (η * c)) = vSL (σ (η * c)) :=
      map_vSL σ.toRingHom (η * c)
    have h3 : σ (η * c) = η * σ c := by
      rw [map_mul, hση]
    have hA := hstepΔ (vSL (η * c))
    rw [h1, h2, h3, hη, hηc] at hA
    exact hA
  have hcurve : (excCurve θ z).map Δ.step = excCurve θ z := u1aO1_curve_map_eq hstepX
  have hcurveneg : (excCurve (-θ) z).map Δ.step = excCurve (-θ) z :=
    u1aO1_curve_map_eq hstepXneg
  have hZle : torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots χ) ≤ adjointGroup τ GGL :=
    sup_le CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
      (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup GGL _)
  have hzAdj : z ∈ adjointGroup τ GGL := hZle hzZ
  have hratComp : LieCore.ratComp ρ Δ.Γ Ψ =
      ⁅rootSpan τ GGL Ψ ⊓ Δ.Γ, rootSpan τ GGL Ψ ⊓ Δ.Γ⁆ := by
    show ⁅rootSpan τ GGL (LieCore.ratOrbit ρ Ψ) ⊓ Δ.Γ,
      rootSpan τ GGL (LieCore.ratOrbit ρ Ψ) ⊓ Δ.Γ⁆ = _
    rw [hrat]
  have hmodel_of_pinned : ∀ {β : Fin τ.rank → ℤ}
      (hstep : ∀ c : GGL, Δ.step (z * pinnedX τ GGL β c * z⁻¹) =
        z * pinnedX τ GGL β (σ c) * z⁻¹) (hβ : β ∈ Ψ) (c : GGL), σ c = c →
      z * pinnedX τ GGL β c * z⁻¹ ∈ Δ.model := by
    intro β hstep hβ c hc
    refine Δ.mem_model.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hzAdj
        (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup GGL Ψ
          (pinnedX_mem_rootSpan hβ c))) (inv_mem hzAdj)
    · have h := hstep c
      rw [hc] at h
      rw [← MulAut.conj_apply]
      exact h
  have hinv_gen : ∀ {β : Fin τ.rank → ℤ} (c : GGL),
      (z * pinnedX τ GGL β c * z⁻¹) * (z * pinnedX τ GGL β c * z⁻¹) = 1 := by
    intro β c
    have h2 : (2 : GGL) = 0 := CharP.cast_eq_zero GGL 2
    have hp1 : pinnedX τ GGL β c * pinnedX τ GGL β c = 1 :=
      CFSG.StandardType.RootCentExc.pinnedX_mul_self h2 β c
    calc (z * pinnedX τ GGL β c * z⁻¹) * (z * pinnedX τ GGL β c * z⁻¹)
        = z * (pinnedX τ GGL β c * pinnedX τ GGL β c) * z⁻¹ := by group
      _ = 1 := by rw [hp1]; group
  have hmem_of_pinned : ∀ {β : Fin τ.rank → ℤ}
      (hstep : ∀ c : GGL, Δ.step (z * pinnedX τ GGL β c * z⁻¹) =
        z * pinnedX τ GGL β (σ c) * z⁻¹)
      (hgen : ∀ c : GGL, σ c = c →
        z * pinnedX τ GGL β c * z⁻¹ ∈ LieCore.ratComp ρ Δ.Γ Ψ),
      excCurve β z ⊓ Δ.model ≤ LieCore.ratComp ρ Δ.Γ Ψ := by
    intro β hstep hgen x hx
    obtain ⟨hxcurve, hxmodel⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, hyU, hyx⟩ := Subgroup.mem_map.1 hxcurve
    rw [mem_rootSubgroup] at hyU
    obtain ⟨c, rfl⟩ := hyU
    change MulAut.conj z (pinnedX τ GGL β c) = x at hyx
    rw [MulAut.conj_apply] at hyx
    have hxeq : x = z * pinnedX τ GGL β c * z⁻¹ := hyx.symm
    have hxstep : Δ.step x = x := by
      change (MulAut.conj Δ.n) (Δ.Φ x) = x
      rw [MulAut.conj_apply]
      exact (Δ.mem_model.1 hxmodel).2
    have hstepfix : Δ.step (z * pinnedX τ GGL β c * z⁻¹) =
        z * pinnedX τ GGL β c * z⁻¹ := by
      rw [← hxeq]
      exact hxstep
    rw [hstep c] at hstepfix
    have hpc : pinnedX τ GGL β (σ c) = pinnedX τ GGL β c :=
      mul_left_cancel (mul_right_cancel hstepfix)
    have hfix : σ c = c := pinnedX_injective τ GGL β hpc
    rw [hxeq]
    exact hgen c hfix
  obtain ⟨hcurve_theta, hcurve_neg⟩ : excCurve θ z ⊓ Δ.model ≤
        LieCore.ratComp ρ Δ.Γ Ψ ∧
      excCurve (-θ) z ⊓ Δ.model ≤ LieCore.ratComp ρ Δ.Γ Ψ := by
    by_cases hf1 : f = 1
    · have hq2 : Δ.q = 2 := by rw [hq, hf1]; norm_num
      have hgen_two : ∀ {β : Fin τ.rank → ℤ}, β ∈ Ψ →
          (∀ c : GGL, Δ.step (z * pinnedX τ GGL β c * z⁻¹) =
            z * pinnedX τ GGL β (σ c) * z⁻¹) → ∀ c : GGL, σ c = c →
          z * pinnedX τ GGL β c * z⁻¹ ∈ LieCore.ratComp ρ Δ.Γ Ψ := by
        intro β hβ hstep c hc
        have hspan : z * pinnedX τ GGL β c * z⁻¹ ∈ rootSpan τ GGL Ψ :=
          (hnorm iJ _).1 (pinnedX_mem_rootSpan hβ c)
        have hmod : z * pinnedX τ GGL β c * z⁻¹ ∈ Δ.model :=
          hmodel_of_pinned hstep hβ c hc
        exact outerTwo_mem_ratComp hτ Δ hq2 hρ hfin hp hp2 ha₁ ha₂ hap₁ hap₂ hne iJ hb houter
          hqs ⟨hspan, hmod⟩ (hinv_gen c)
      exact ⟨hmem_of_pinned hstepX (hgen_two hθ hstepX),
        hmem_of_pinned hstepXneg (hgen_two (hΨ.neg_mem θ hθ) hstepXneg)⟩
    · have hf2 : 2 ≤ f := by omega
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨hfinK, hcard⟩ := outer_fixSubfield_card (L := GGL) (r := 2) (n := f)
        (by omega) σ hσq
      have hperf : Group.IsPerfect (SL2 (fixSubfield σ)) := by
        refine CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card (fixSubfield σ) ?_
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      let ι : SL2 (fixSubfield σ) →* ModGL τ GGL :=
        (MulAut.conj z).toMonoidHom.comp ((rootSL2 τ GGL θ).comp
          (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype))
      have hσfix : ∀ A : SL2 (fixSubfield σ),
          Matrix.SpecialLinearGroup.map σ.toRingHom
            (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A) =
            Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A := by
        intro A
        ext i j
        exact ((A : Matrix (Fin 2) (Fin 2) (fixSubfield σ)) i j).2
      have hsub : ({θ, -θ} : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
        intro γ hγ
        rcases hγ with rfl | rfl
        · exact hθ
        · exact hΨ.neg_mem θ hθ
      have hspan_all : ∀ A : SL2 (fixSubfield σ), ι A ∈ rootSpan τ GGL Ψ := by
        intro A
        show z * rootSL2 τ GGL θ (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A) *
          z⁻¹ ∈ rootSpan τ GGL Ψ
        exact (hnorm iJ _).1 (rootSpan_mono hsub
          (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair hθr _))
      have hYmodel : ∀ A : SL2 (fixSubfield σ), ι A ∈ Δ.model := by
        intro A
        have hstepA := hstepΔ (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype A)
        rw [hσfix A] at hstepA
        refine Δ.mem_model.2 ⟨?_, ?_⟩
        · exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup GGL Ψ (hspan_all A)
        · rw [← MulAut.conj_apply]
          exact hstepA
      have hYle : ∀ A : SL2 (fixSubfield σ),
          ι A ∈ ⁅rootSpan τ GGL Ψ ⊓ Δ.Γ, rootSpan τ GGL Ψ ⊓ Δ.Γ⁆ := by
        intro A
        exact map_mem_commutator_of_perfect hperf ι (rootSpan τ GGL Ψ ⊓ Δ.Γ)
          (fun B => ⟨hspan_all B, by
            show ι B ∈ Δ.Γ
            exact map_mem_commutator_of_perfect hperf ι Δ.model hYmodel B⟩) A
      have hgenθ : ∀ c : GGL, σ c = c →
          z * pinnedX τ GGL θ c * z⁻¹ ∈ LieCore.ratComp ρ Δ.Γ Ψ := by
        intro c hc
        rw [hratComp]
        let x0 : fixSubfield σ := ⟨c, (mem_fixSubfield (σ := σ)).2 hc⟩
        have hAeq : ι (uSL (ε • x0)) = z * pinnedX τ GGL θ c * z⁻¹ := by
          show z * rootSL2 τ GGL θ
            (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype (uSL (ε • x0))) * z⁻¹
            = z * pinnedX τ GGL θ c * z⁻¹
          rw [map_uSL, map_zsmul, rootSL2_uSL_eq, ← hεdef, Subfield.coe_subtype]
          have harg : ε • (ε • (x0 : GGL)) = c := by
            rw [show (x0 : GGL) = c from rfl]
            exact hεc c
          rw [harg]
        rw [← hAeq]
        exact hYle _
      have hgenneg : ∀ c : GGL, σ c = c →
          z * pinnedX τ GGL (-θ) c * z⁻¹ ∈ LieCore.ratComp ρ Δ.Γ Ψ := by
        intro c hc
        rw [hratComp]
        let x0 : fixSubfield σ := ⟨c, (mem_fixSubfield (σ := σ)).2 hc⟩
        let η0 : fixSubfield σ := ⟨η, (mem_fixSubfield (σ := σ)).2 hση⟩
        have hAeq : ι (vSL (η0 * x0)) = z * pinnedX τ GGL (-θ) c * z⁻¹ := by
          show z * rootSL2 τ GGL θ
            (Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype (vSL (η0 * x0))) * z⁻¹
            = z * pinnedX τ GGL (-θ) c * z⁻¹
          rw [map_vSL, hη, Subfield.coe_subtype]
          have harg : ((η0 * x0 : fixSubfield σ) : GGL) = η * c := by
            push_cast
            rfl
          rw [harg, hηc]
        rw [← hAeq]
        exact hYle _
      exact ⟨hmem_of_pinned hstepX hgenθ, hmem_of_pinned hstepXneg hgenneg⟩
  exact ⟨θ, z, hθ, hzZ, hcurve, hcurveneg, hcurve_theta, hcurve_neg⟩

end CFSG.StandardType.LieKnownR2.ExcPos
