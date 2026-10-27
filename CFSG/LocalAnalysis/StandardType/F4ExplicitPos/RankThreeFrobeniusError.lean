module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FactorCentralizer
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeModelsPart2

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.SeitzReduction.F4Pilot
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.StandardType.F4ExplicitPos.RankThreeModels


variable {Ω : Type} [Field Ω] [CharP Ω 2]
  {M : Type*} [CommGroup M]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem frobenius_error_mem_centralizer_of_untwist {f : ℕ}
    (D : LangDatum .F4 Ω)
    (hΦ : D.Φ = Units.map (entrywiseHom (iterateFrobenius Ω 2 f)))
    (hq : D.q = 2 ^ f) (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ D.q)
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) (i : KernelComponent χ)
    (z : ModGL .F4 Ω) (hz : z ∈ NativePinFinal.Zsub χ)
    (hstep : ∀ g ∈ rootSpan .F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    (D.g0 * z)⁻¹ * D.Φ (D.g0 * z) ∈ adjointGroup .F4 Ω ⊓
      Subgroup.centralizer (rootSpan .F4 Ω (componentRoots χ i) : Set (ModGL .F4 Ω)) := by
  have hFr : iterateFrobenius Ω 2 f = σ.toRingHom := by
    ext c
    change iterateFrobenius Ω 2 f c = σ c
    rw [iterateFrobenius_def, hσ, hq]
  have hΦσ : D.Φ = frobGL (τ := .F4) σ := by
    rw [hΦ, hFr]
  have hσσ : σ.toRingHom.comp σ.symm.toRingHom = RingHom.id Ω := by
    ext c
    exact σ.apply_symm_apply c
  have hcancel (g : ModGL .F4 Ω) : frobGL σ (frobGL σ.symm g) = g := by
    rw [frobGL_eq_bcGL (Ω := Ω) σ, frobGL_eq_bcGL (Ω := Ω) σ.symm,
      bcGL_comp, hσσ]
    have h := DFunLike.congr_fun (frobGL_eq_bcGL (Ω := Ω) (RingEquiv.refl Ω)) g
    change frobGL (τ := .F4) (RingEquiv.refl Ω) g = bcGL (RingHom.id Ω) g at h
    rw [← h]
    exact Units.ext (entrywise_id _)
  have hb : D.g0 * z ∈ adjointGroup .F4 Ω :=
    mul_mem D.g0_mem (NativePinFinal.Zsub_le_adjointGroup χ hz)
  have hFb : D.Φ (D.g0 * z) ∈ adjointGroup .F4 Ω := by
    rw [hΦ]
    exact LangPosition.entrywiseFrobGL_mem_adjointGroup_no117 2 f hb
  refine ⟨(adjointGroup .F4 Ω).mul_mem ((adjointGroup .F4 Ω).inv_mem hb) hFb,
    Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have h := hstep (frobGL σ.symm x) (frobGL_mem_rootSpan σ.symm hx)
  change D.n * D.Φ (z * frobGL σ.symm x * z⁻¹) * D.n⁻¹ =
    z * frobGL σ (frobGL σ.symm x) * z⁻¹ at h
  have h' : D.n * (frobGL σ z * x * (frobGL σ z)⁻¹) * D.n⁻¹ = z * x * z⁻¹ := by
    simpa only [hΦσ, map_mul, map_inv, hcancel] using h
  have hc := congrArg (fun y : ModGL .F4 Ω => z⁻¹ * y * D.n * frobGL σ z) h'
  have he : (D.g0 * z)⁻¹ * D.Φ (D.g0 * z) = z⁻¹ * D.n * frobGL σ z := by
    rw [map_mul, D.lang, hΦσ]
    group
  rw [he]
  convert hc.symm using 1 <;> group

variable [IsAlgClosed Ω] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem frobenius_error_mem_rootSL2R_of_c3 {f : ℕ}
    (D : LangDatum .F4 Ω)
    (hΦ : D.Φ = Units.map (entrywiseHom (iterateFrobenius Ω 2 f)))
    (hq : D.q = 2 ^ f) (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ D.q)
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) (i : KernelComponent χ)
    (z : ModGL .F4 Ω) (hz : z ∈ NativePinFinal.Zsub χ)
    (hstep : ∀ g ∈ rootSpan .F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (v : WeylGroup .F4)
    (hshape : componentRoots χ i = (fun α => v • α) '' C3Range.c3RootSet) :
    (D.g0 * z * canonicalRep (coxeterSystem .F4) Ω v)⁻¹ *
      D.Φ (D.g0 * z * canonicalRep (coxeterSystem .F4) Ω v) ∈ rootSL2R Ω := by
  let nv := canonicalRep (coxeterSystem .F4) Ω v
  have hspan : rootSpan .F4 Ω (componentRoots χ i) = (RationalC3.conjIM Ω nv).range := by
    rw [RationalC3.range_conjIM_canonicalRep, hshape]
  have hc := frobenius_error_mem_centralizer_of_untwist D hΦ hq σ hσ χ i z hz hstep
  have hm : (D.g0 * z)⁻¹ * D.Φ (D.g0 * z) ∈
      (rootSL2R Ω).map (MulAut.conj nv).toMonoidHom := by
    rw [← centralizer_conjIM_canonicalRep_eq (Ω := Ω) v]
    simpa only [hspan] using hc
  have hnv : D.Φ nv = nv := by
    rw [hΦ]
    exact CFSG.RankThree.PartOne.KE.frobenius_canonicalRep (iterateFrobenius Ω 2 f) v
  have he : (D.g0 * z * nv)⁻¹ * D.Φ (D.g0 * z * nv) =
      nv⁻¹ * ((D.g0 * z)⁻¹ * D.Φ (D.g0 * z)) * nv := by
    rw [map_mul, hnv]
    group
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hm
  change (D.g0 * z * nv)⁻¹ * D.Φ (D.g0 * z * nv) ∈ rootSL2R Ω
  rw [he, ← hxe]
  simpa [MulAut.conj_apply, mul_assoc] using hx

theorem frobenius_error_mem_rootPairS_of_b3 {f : ℕ}
    (D : LangDatum .F4 Ω)
    (hΦ : D.Φ = Units.map (entrywiseHom (iterateFrobenius Ω 2 f)))
    (hq : D.q = 2 ^ f) (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ D.q)
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) (i : KernelComponent χ)
    (z : ModGL .F4 Ω) (hz : z ∈ NativePinFinal.Zsub χ)
    (hstep : ∀ g ∈ rootSpan .F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (v : WeylGroup .F4)
    (hshape : componentRoots χ i = (fun α => v • α) '' b3LeviRoots) :
    (D.g0 * z * canonicalRep (coxeterSystem .F4) Ω v)⁻¹ *
      D.Φ (D.g0 * z * canonicalRep (coxeterSystem .F4) Ω v) ∈
        rootSubgroup .F4 Ω rootS ⊔ rootSubgroup .F4 Ω (-rootS) := by
  let nv := canonicalRep (coxeterSystem .F4) Ω v
  have hspan : rootSpan .F4 Ω (componentRoots χ i) = (RationalB3.conjBM Ω nv).range := by
    rw [RationalB3.range_conjBM_canonicalRep, hshape]
  have hc := frobenius_error_mem_centralizer_of_untwist D hΦ hq σ hσ χ i z hz hstep
  have hm : (D.g0 * z)⁻¹ * D.Φ (D.g0 * z) ∈
      (rootSubgroup .F4 Ω rootS ⊔ rootSubgroup .F4 Ω (-rootS)).map
        (MulAut.conj nv).toMonoidHom := by
    rw [← centralizer_conjBM_canonicalRep_eq (Ω := Ω) v]
    simpa only [hspan] using hc
  have hnv : D.Φ nv = nv := by
    rw [hΦ]
    exact CFSG.RankThree.PartOne.KE.frobenius_canonicalRep (iterateFrobenius Ω 2 f) v
  have he : (D.g0 * z * nv)⁻¹ * D.Φ (D.g0 * z * nv) =
      nv⁻¹ * ((D.g0 * z)⁻¹ * D.Φ (D.g0 * z)) * nv := by
    rw [map_mul, hnv]
    group
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hm
  change (D.g0 * z * nv)⁻¹ * D.Φ (D.g0 * z * nv) ∈
    rootSubgroup .F4 Ω rootS ⊔ rootSubgroup .F4 Ω (-rootS)
  rw [he, ← hxe]
  simpa [MulAut.conj_apply, mul_assoc] using hx

theorem frobenius_error_rootSL2_data_of_c3 {f : ℕ}
    (D : LangDatum .F4 Ω)
    (hΦ : D.Φ = Units.map (entrywiseHom (iterateFrobenius Ω 2 f)))
    (hq : D.q = 2 ^ f) (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ D.q)
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) (i : KernelComponent χ)
    (z : ModGL .F4 Ω) (hz : z ∈ NativePinFinal.Zsub χ)
    (hstep : ∀ g ∈ rootSpan .F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (v : WeylGroup .F4)
    (hshape : componentRoots χ i = (fun α => v • α) '' C3Range.c3RootSet) :
    IsRoot .F4 rootR ∧ Function.Injective (rootSL2 .F4 Ω rootR) ∧
      ((D.g0 * z * canonicalRep (coxeterSystem .F4) Ω v)⁻¹ *
        D.Φ (D.g0 * z * canonicalRep (coxeterSystem .F4) Ω v)) ∈
          (rootSL2 .F4 Ω rootR).range ∧
      (rootSL2 .F4 Ω rootR).range ≤
        Subgroup.centralizer ((RationalC3.conjIM Ω 1).range : Set (ModGL .F4 Ω)) := by
  have hcenter : adjointGroup .F4 Ω ⊓
      Subgroup.centralizer ((RationalC3.conjIM Ω 1).range : Set (ModGL .F4 Ω)) =
        rootSL2R Ω := by
    have hid : (MulAut.conj (1 : ModGL .F4 Ω)).toMonoidHom = MonoidHom.id _ := by
      ext g
      simp [MulAut.conj_apply]
    simpa only [hid, Subgroup.map_id] using
      centralizer_conjIM_eq (Ω := Ω) 1 (Subgroup.one_mem _)
  refine ⟨isRoot_rootR, rootSL2_rootR_injective, ?_, ?_⟩
  · rw [range_rootSL2_rootR]
    exact frobenius_error_mem_rootSL2R_of_c3 D hΦ hq σ hσ χ i z hz hstep v hshape
  · rw [range_rootSL2_rootR, ← hcenter]
    exact inf_le_right

theorem frobenius_error_rootSL2_data_of_b3 {f : ℕ}
    (D : LangDatum .F4 Ω)
    (hΦ : D.Φ = Units.map (entrywiseHom (iterateFrobenius Ω 2 f)))
    (hq : D.q = 2 ^ f) (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ D.q)
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) (i : KernelComponent χ)
    (z : ModGL .F4 Ω) (hz : z ∈ NativePinFinal.Zsub χ)
    (hstep : ∀ g ∈ rootSpan .F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (v : WeylGroup .F4)
    (hshape : componentRoots χ i = (fun α => v • α) '' b3LeviRoots) :
    IsRoot .F4 rootS ∧ Function.Injective (rootSL2 .F4 Ω rootS) ∧
      ((D.g0 * z * canonicalRep (coxeterSystem .F4) Ω v)⁻¹ *
        D.Φ (D.g0 * z * canonicalRep (coxeterSystem .F4) Ω v)) ∈
          (rootSL2 .F4 Ω rootS).range ∧
      (rootSL2 .F4 Ω rootS).range ≤
        Subgroup.centralizer ((RationalB3.conjBM Ω 1).range : Set (ModGL .F4 Ω)) := by
  have hcenter : adjointGroup .F4 Ω ⊓
      Subgroup.centralizer ((RationalB3.conjBM Ω 1).range : Set (ModGL .F4 Ω)) =
        rootSubgroup .F4 Ω rootS ⊔ rootSubgroup .F4 Ω (-rootS) := by
    have hid : (MulAut.conj (1 : ModGL .F4 Ω)).toMonoidHom = MonoidHom.id _ := by
      ext g
      simp [MulAut.conj_apply]
    simpa only [hid, Subgroup.map_id] using
      centralizer_conjBM_eq (Ω := Ω) 1 (Subgroup.one_mem _)
  have hroot := CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .F4 Ω isRoot_rootS
  refine ⟨isRoot_rootS, hroot.1, ?_, ?_⟩
  · rw [hroot.2.1]
    exact frobenius_error_mem_rootPairS_of_b3 D hΦ hq σ hσ χ i z hz hstep v hshape
  · rw [hroot.2.1, ← hcenter]
    exact inf_le_right

end CFSG.StandardType.F4ExplicitPos
