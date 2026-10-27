module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.LocalAnalysis.StandardType.GGLangRatCompTorusLift
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.GGFinModel
  CFSG.StandardType.F4ExplicitPos.CommonFactor

private theorem rckFix_pinnedX_mem_rootSpan {τ : Tag} {R : Type} [CommRing R]
    {S : Set (Fin τ.rank → ℤ)} {γ : Fin τ.rank → ℤ} (hγ : γ ∈ S) (c : R) :
    pinnedX τ R γ c ∈ rootSpan τ R S := by
  rw [rootSpan]
  exact Subgroup.mem_iSup_of_mem γ
    (Subgroup.mem_iSup_of_mem hγ (mem_rootSubgroup.mpr ⟨c, rfl⟩))

private theorem rckFix_conj_apply {G : Type} [Group G] (z x : G) :
    (MulAut.conj z).toMonoidHom x = z * x * z⁻¹ := rfl

private theorem rckFix_mem_conj_rootSubgroup {τ : Tag} {R : Type} [Field R]
    (z : ModGL τ R) (γ : Fin τ.rank → ℤ) (x : ModGL τ R) :
    x ∈ (rootSubgroup τ R γ).map (MulAut.conj z).toMonoidHom ↔
      ∃ c : R, z * pinnedX τ R γ c * z⁻¹ = x := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_rootSubgroup] at hu
    obtain ⟨c, rfl⟩ := hu
    exact ⟨c, by rw [rckFix_conj_apply]⟩
  · rintro ⟨c, hc⟩
    exact ⟨pinnedX τ R γ c, mem_rootSubgroup.mpr ⟨c, rfl⟩,
      by rw [rckFix_conj_apply]; exact hc⟩

private theorem rckFix_mem_conj_baseChange {τ : Tag} (σ : GGL ≃+* GGL)
    (z : ModGL τ GGL) (γ : Fin τ.rank → ℤ) (x : ModGL τ GGL) :
    x ∈ ((rootSubgroup τ ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj z).toMonoidHom ↔
      ∃ c : ↥(fixSubfield σ), z * pinnedX τ GGL γ (c : GGL) * z⁻¹ = x := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Subgroup.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [mem_rootSubgroup] at hv
    obtain ⟨c, rfl⟩ := hv
    exact ⟨c, by rw [baseChangeGL_pinnedX, rckFix_conj_apply, Subfield.subtype_apply]⟩
  · rintro ⟨c, hc⟩
    refine ⟨baseChangeGL (fixSubfield σ).subtype (pinnedX τ ↥(fixSubfield σ) γ c), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨pinnedX τ ↥(fixSubfield σ) γ c,
        mem_rootSubgroup.mpr ⟨c, rfl⟩, rfl⟩
    · rw [rckFix_conj_apply, baseChangeGL_pinnedX, Subfield.subtype_apply]; exact hc

private theorem rckFix_step_conj
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (σ : GGL ≃+* GGL)
    (z : ModGL τ GGL) {Ψ : Set (Fin τ.rank → ℤ)}
    (hz : ∀ g ∈ rootSpan τ GGL Ψ, S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {γ : Fin τ.rank → ℤ} (hγΨ : γ ∈ Ψ) (c : GGL) :
    S.D.step (z * pinnedX τ GGL γ c * z⁻¹) = z * pinnedX τ GGL γ (σ c) * z⁻¹ := by
  rw [hz _ (rckFix_pinnedX_mem_rootSpan hγΨ c), frobGL_pinnedX]

private theorem rckFix_conj_stable
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (σ : GGL ≃+* GGL)
    (z : ModGL τ GGL) {Ψ : Set (Fin τ.rank → ℤ)}
    (hz : ∀ g ∈ rootSpan τ GGL Ψ, S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {γ : Fin τ.rank → ℤ} (hγΨ : γ ∈ Ψ) :
    ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom := by
  apply le_antisymm
  · rintro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [rckFix_mem_conj_rootSubgroup] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨σ c, (rckFix_step_conj S σ z hz hγΨ c).symm⟩
  · rintro y hy
    rw [rckFix_mem_conj_rootSubgroup] at hy
    obtain ⟨c, rfl⟩ := hy
    refine Subgroup.mem_map.mpr ⟨z * pinnedX τ GGL γ (σ.symm c) * z⁻¹, ?_, ?_⟩
    · exact (rckFix_mem_conj_rootSubgroup z γ _).mpr ⟨σ.symm c, rfl⟩
    · rw [rckFix_step_conj S σ z hz hγΨ (σ.symm c), σ.apply_symm_apply]

private theorem rckFix_fixed_eq_baseChange
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (σ : GGL ≃+* GGL)
    (z : ModGL τ GGL) {Ψ : Set (Fin τ.rank → ℤ)}
    (hz : ∀ g ∈ rootSpan τ GGL Ψ, S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {γ : Fin τ.rank → ℤ} (hγΨ : γ ∈ Ψ) :
    ((rootSubgroup τ ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
        (MulAut.conj z).toMonoidHom =
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
  apply le_antisymm
  · intro y hy
    rw [rckFix_mem_conj_baseChange] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact (rckFix_mem_conj_rootSubgroup z γ _).mpr ⟨(c : GGL), rfl⟩
    · show S.D.step (z * pinnedX τ GGL γ (c : GGL) * z⁻¹) =
          z * pinnedX τ GGL γ (c : GGL) * z⁻¹
      rw [rckFix_step_conj S σ z hz hγΨ (c : GGL), (mem_fixSubfield σ).1 c.2]
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyZ, hyFix⟩ := hy
    rw [rckFix_mem_conj_baseChange]
    rw [rckFix_mem_conj_rootSubgroup] at hyZ
    obtain ⟨c, rfl⟩ := hyZ
    have hc : σ c = c := by
      have h1 : S.D.step (z * pinnedX τ GGL γ c * z⁻¹) =
          z * pinnedX τ GGL γ c * z⁻¹ := hyFix
      rw [rckFix_step_conj S σ z hz hγΨ c] at h1
      exact pinnedX_injective τ GGL γ (mul_left_cancel (mul_right_cancel h1))
    exact ⟨⟨c, hc⟩, rfl⟩

private theorem rckFix_map_conj_mul {G : Type} [Group G] (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, rckFix_conj_apply]
  group

private theorem rckFix_step_conj_eq
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {r : ModGL τ L} (hr : D.step r = r) :
    D.step.comp (MulAut.conj r).toMonoidHom =
      (MulAut.conj r).toMonoidHom.comp D.step := by
  ext x
  simp only [MonoidHom.comp_apply, rckFix_conj_apply]
  rw [map_mul, map_mul, map_inv, hr]

private theorem rckFix_step_conj_apply
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {r : ModGL τ L} (hr : D.step r = r) (v : ModGL τ L) :
    D.step (r * v * r⁻¹) = r * D.step v * r⁻¹ := by
  rw [map_mul, map_mul, map_inv, hr]

private theorem rckFix_stable_map_conj
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {r : ModGL τ L} (hr : D.step r = r) (V : Subgroup (ModGL τ L))
    (hV : V.map D.step = V) :
    (V.map (MulAut.conj r).toMonoidHom).map D.step = V.map (MulAut.conj r).toMonoidHom := by
  calc (V.map (MulAut.conj r).toMonoidHom).map D.step
      = V.map (D.step.comp (MulAut.conj r).toMonoidHom) :=
        Subgroup.map_map V D.step (MulAut.conj r).toMonoidHom
    _ = V.map ((MulAut.conj r).toMonoidHom.comp D.step) := by rw [rckFix_step_conj_eq D hr]
    _ = (V.map D.step).map (MulAut.conj r).toMonoidHom :=
        (Subgroup.map_map V (MulAut.conj r).toMonoidHom D.step).symm
    _ = V.map (MulAut.conj r).toMonoidHom := by rw [hV]

private theorem rckFix_inf_fix_map_conj
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {r : ModGL τ L} (hr : D.step r = r) (V : Subgroup (ModGL τ L)) :
    (V ⊓ D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj r).toMonoidHom =
      (V.map (MulAut.conj r).toMonoidHom) ⊓ D.step.eqLocus (MonoidHom.id _) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [Subgroup.mem_inf] at hv
    rw [Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map.mpr ⟨v, hv.1, rfl⟩, ?_⟩
    have hvfix : D.step v = v := hv.2
    show D.step ((MulAut.conj r) v) = (MulAut.conj r) v
    rw [MulAut.conj_apply, rckFix_step_conj_apply D hr v, hvfix]
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxV, hxfix⟩ := hx
    rw [Subgroup.mem_map] at hxV
    obtain ⟨v, hv, rfl⟩ := hxV
    refine Subgroup.mem_map.mpr ⟨v, ?_, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨hv, ?_⟩
    have hxfix' : D.step (r * v * r⁻¹) = r * v * r⁻¹ := by
      have h : D.step ((MulAut.conj r).toMonoidHom v) = (MulAut.conj r).toMonoidHom v := hxfix
      rw [rckFix_conj_apply] at h
      exact h
    have h1 : r * D.step v * r⁻¹ = r * v * r⁻¹ := by
      rw [← rckFix_step_conj_apply D hr v]
      exact hxfix'
    exact mul_left_cancel (mul_right_cancel h1)


theorem rckPair_stable_fixed
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (σ : GGL ≃+* GGL)
    (z : ModGL τ GGL) {Ψ : Set (Fin τ.rank → ℤ)}
    (hz : ∀ g ∈ rootSpan τ GGL Ψ, S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγΨ : γ ∈ Ψ) :
    ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ∧
      ((rootSubgroup τ ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
          (MulAut.conj z).toMonoidHom =
        (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ⊓
          S.D.step.eqLocus (MonoidHom.id _) :=
  ⟨rckFix_conj_stable S σ z hz hγΨ, rckFix_fixed_eq_baseChange S σ z hz hγΨ⟩

theorem rationalComponent_le_torusGroup_sup_rootSpan_kernelRoots
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {a : Fin τ.rank → GGLˣ} (i : KernelComponent (rootCharHom a))
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) := by
  refine (CFSG.StandardType.LangRat.rationalComponent_le_rootSpan_rationalRoots
    S.ρ S.Γ (rootCharHom a) i).trans ?_
  refine (rootSpan_mono ?_).trans le_sup_right
  intro γ hγ
  rw [rationalRoots_eq_componentRoots_of_orbitLength_one i hs] at hγ
  exact hγ.1

theorem rckPair_assemble
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (σ : GGL ≃+* GGL)
    {H : Subgroup (ModGL τ GGL)} (z : ModGL τ GGL) (hz0 : z ∈ H)
    {Ψ : Set (Fin τ.rank → ℤ)}
    (hz : ∀ g ∈ rootSpan τ GGL Ψ, S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    {G : Type} [Group G] {n : ℕ} (X : (Fin n → ℤ) → Subgroup G) (φ : G →* ModGL τ GGL)
    (hφ : φ.range ≤ S.D.model) (hφH : φ.range ≤ H) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγΨ : γ ∈ Ψ)
    (hγΨ' : -γ ∈ Ψ) {α β : Fin n → ℤ}
    (hX : (X α).map φ =
      ((rootSubgroup τ ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
        (MulAut.conj z).toMonoidHom)
    (hX' : (X (-α)).map φ =
      ((rootSubgroup τ ↥(fixSubfield σ) (-γ)).map (baseChangeGL (fixSubfield σ).subtype)).map
        (MulAut.conj z).toMonoidHom)
    (u : G) (hu : (X α).map (MulAut.conj u).toMonoidHom = X β)
    (hu' : (X (-α)).map (MulAut.conj u).toMonoidHom = X (-β)) :
    ∃ z' ∈ H,
      ((rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom).map S.D.step =
          (rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom ∧
      ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom).map S.D.step =
          (rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom ∧
      (X β).map φ = (rootSubgroup τ GGL γ).map (MulAut.conj z').toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) ∧
      (X (-β)).map φ = (rootSubgroup τ GGL (-γ)).map (MulAut.conj z').toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) := by
  have hφu_mem : φ u ∈ S.D.model := hφ (MonoidHom.mem_range.mpr ⟨u, rfl⟩)
  have hφu_fix : S.D.step (φ u) = φ u := ((S.D.mem_model).1 hφu_mem).2
  have hstabγ := (rckPair_stable_fixed (γ := γ) S σ z hz hγ hγΨ).1
  have hfixγ := (rckPair_stable_fixed (γ := γ) S σ z hz hγ hγΨ).2
  have hstabγ' := rckFix_conj_stable (γ := -γ) S σ z hz hγΨ'
  have hfixγ' := rckFix_fixed_eq_baseChange (γ := -γ) S σ z hz hγΨ'
  have hconjφ : φ.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (φ u)).toMonoidHom.comp φ := by
    ext x
    simp only [MonoidHom.comp_apply, rckFix_conj_apply, map_mul, map_inv]
  refine ⟨φ u * z, mul_mem (hφH (MonoidHom.mem_range.mpr ⟨u, rfl⟩)) hz0, ?_, ?_, ?_, ?_⟩
  · rw [rckFix_map_conj_mul (rootSubgroup τ GGL γ) (φ u) z]
    exact rckFix_stable_map_conj (r := φ u) S.D hφu_fix _ hstabγ
  · rw [rckFix_map_conj_mul (rootSubgroup τ GGL (-γ)) (φ u) z]
    exact rckFix_stable_map_conj (r := φ u) S.D hφu_fix _ hstabγ'
  · rw [rckFix_map_conj_mul (rootSubgroup τ GGL γ) (φ u) z]
    calc (X β).map φ
        = ((X α).map (MulAut.conj u).toMonoidHom).map φ := by rw [← hu]
      _ = (X α).map (φ.comp (MulAut.conj u).toMonoidHom) :=
            Subgroup.map_map (X α) φ (MulAut.conj u).toMonoidHom
      _ = (X α).map ((MulAut.conj (φ u)).toMonoidHom.comp φ) := by rw [hconjφ]
      _ = ((X α).map φ).map (MulAut.conj (φ u)).toMonoidHom :=
            (Subgroup.map_map (X α) (MulAut.conj (φ u)).toMonoidHom φ).symm
      _ = (((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom) ⊓
              S.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj (φ u)).toMonoidHom := by
            rw [hX, hfixγ]
      _ = (((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map
              (MulAut.conj (φ u)).toMonoidHom) ⊓ S.D.step.eqLocus (MonoidHom.id _) :=
            rckFix_inf_fix_map_conj (r := φ u) S.D hφu_fix _
  · rw [rckFix_map_conj_mul (rootSubgroup τ GGL (-γ)) (φ u) z]
    calc (X (-β)).map φ
        = ((X (-α)).map (MulAut.conj u).toMonoidHom).map φ := by rw [← hu']
      _ = (X (-α)).map (φ.comp (MulAut.conj u).toMonoidHom) :=
            Subgroup.map_map (X (-α)) φ (MulAut.conj u).toMonoidHom
      _ = (X (-α)).map ((MulAut.conj (φ u)).toMonoidHom.comp φ) := by rw [hconjφ]
      _ = ((X (-α)).map φ).map (MulAut.conj (φ u)).toMonoidHom :=
            (Subgroup.map_map (X (-α)) (MulAut.conj (φ u)).toMonoidHom φ).symm
      _ = (((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom) ⊓
              S.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj (φ u)).toMonoidHom := by
            rw [hX', hfixγ']
      _ = (((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map
              (MulAut.conj (φ u)).toMonoidHom) ⊓ S.D.step.eqLocus (MonoidHom.id _) :=
            rckFix_inf_fix_map_conj (r := φ u) S.D hφu_fix _

end CFSG.StandardType.RCKRP

end
