module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcPlacementDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import CFSG.LocalAnalysis.StandardType.GGAutomizerMap

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType

private noncomputable def mfm_coord {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) (H E : Subgroup M') {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) : Additive ↥E ≃+ R.V :=
  (MulEquiv.toAdditive (Subgroup.equivMapOfInjective E φ hφ)).trans mf.coord

private theorem mfm_coord_ofMul {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) (H E : Subgroup M') {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) (a : ↥E) :
    mfm_coord hφ H E mf (Additive.ofMul a) =
      mf.coord (Additive.ofMul ((Subgroup.equivMapOfInjective E φ hφ) a)) := rfl

private theorem mfm_ggLin_coord {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) (H E : Subgroup M') {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) (σ : MulAut ↥E) :
    ggLin (p := 3) (mfm_coord hφ H E mf) σ =
      ggLin (p := 3) mf.coord
        (MulAut.congr (Subgroup.equivMapOfInjective E φ hφ) σ) := by
  have h := ggLin_mulEquiv_congr (p := 3) (Subgroup.equivMapOfInjective E φ hφ).symm mf.coord
    (MulAut.congr (Subgroup.equivMapOfInjective E φ hφ) σ)
  rw [MulEquiv.symm_symm] at h
  rw [show MulAut.congr (Subgroup.equivMapOfInjective E φ hφ).symm
      (MulAut.congr (Subgroup.equivMapOfInjective E φ hφ) σ) = σ from by
    ext a
    rw [MulAut.congr_apply, MulAut.congr_apply]
    simp] at h
  exact h

private theorem mfm_ggLin_coord_comp {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) (H E : Subgroup M') {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) :
    ggLin (p := 3) (mfm_coord hφ H E mf) =
      (ggLin (p := 3) mf.coord).comp
        (MulAut.congr (Subgroup.equivMapOfInjective E φ hφ)).toMonoidHom :=
  MonoidHom.ext fun σ => mfm_ggLin_coord hφ H E mf σ

private theorem mfm_component_le_range {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    {H E : Subgroup M'} {R : RawFrameData} (mf : ModelFrame (H.map φ) (E.map φ) R)
    (c : R.Code) (hc : R.admissible c) : mf.component c ≤ φ.range :=
  (mf.component_le c hc).trans (Subgroup.map_le_range φ H)

private theorem mfm_component_le {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {H E : Subgroup M'} {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) (c : R.Code) (hc : R.admissible c) :
    (mf.component c).comap φ ≤ H :=
  calc (mf.component c).comap φ ≤ (H.map φ).comap φ := Subgroup.comap_mono (mf.component_le c hc)
    _ = H := Subgroup.comap_map_eq_self_of_injective hφ H

private noncomputable def mfm_equiv_comap {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {Y : Subgroup M} (hY : Y ≤ φ.range) :
    ↥(Y.comap φ) ≃* ↥Y :=
  (Subgroup.equivMapOfInjective (Y.comap φ) φ hφ).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hY))

private theorem mfm_marked {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {H E : Subgroup M'} {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) (c : R.Code) (hc : R.admissible c) :
    LargeEvenMarking ↥((mf.component c).comap φ) (fun lab _ _ _ _ _ => lab = R.label c) :=
  largeEvenMarking_congr (mfm_equiv_comap hφ (mfm_component_le_range mf c hc))
    (fun _ _ _ _ _ _ h => h) (mf.marked c hc)

private theorem mfm_ggLinImage_eq {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {H E : Subgroup M'} {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) {P : Subgroup M'} {P' : Subgroup M}
    (hP : ∀ e ∈ E, φ e ∈ P' ↔ e ∈ P) :
    ggLinImage (p := 3) (mfm_coord hφ H E mf) P = ggLinImage (p := 3) mf.coord P' := by
  ext v
  obtain ⟨a, rfl⟩ : ∃ a : ↥E, mfm_coord hφ H E mf (Additive.ofMul a) = v :=
    ⟨Additive.toMul ((mfm_coord hφ H E mf).symm v), by simp⟩
  rw [ofMul_mem_ggLinImage, mfm_coord_ofMul, ofMul_mem_ggLinImage,
    Subgroup.coe_equivMapOfInjective_apply]
  exact (hP a a.2).symm

private theorem mfm_mem_centralizer_comap_iff {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {Y : Subgroup M} (hY : Y ≤ φ.range) (a : M') :
    φ a ∈ Subgroup.centralizer (Y : Set M) ↔
      a ∈ Subgroup.centralizer (((Y.comap φ : Subgroup M')) : Set M') := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    exact hφ (by rw [map_mul, map_mul]; exact h (φ x) hx)
  · intro h y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hY hy)
    rw [← map_mul, ← map_mul, h x hy]

private theorem mfm_comap_centralizer {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) (A : Subgroup M') :
    (Subgroup.centralizer (((A.map φ : Subgroup M)) : Set M)).comap φ =
      Subgroup.centralizer (A : Set M') := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    exact hφ (by rw [map_mul, map_mul]; exact h (φ a) (Subgroup.mem_map_of_mem φ ha))
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_mul, ← map_mul, h a ha]

private theorem mfm_map_inf_centralizer {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) (H A : Subgroup M') :
    (H ⊓ Subgroup.centralizer (A : Set M')).map φ =
      H.map φ ⊓ Subgroup.centralizer (((A.map φ : Subgroup M)) : Set M) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyC' : ∀ a ∈ (A : Set M'), a * y = y * a :=
      (Subgroup.mem_centralizer_iff (s := (A : Set M'))).mp hyC
    refine ⟨Subgroup.mem_map_of_mem φ hyH, ?_⟩
    refine (Subgroup.mem_centralizer_iff (s := ((A.map φ : Subgroup M) : Set M))).mpr ?_
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_mul, ← map_mul, hyC' a ha]
  · rintro ⟨hxH, hxC⟩
    obtain ⟨y, hyH, rfl⟩ := Subgroup.mem_map.mp hxH
    have hxC' : ∀ a ∈ ((A.map φ : Subgroup M) : Set M), a * φ y = φ y * a :=
      (Subgroup.mem_centralizer_iff (s := ((A.map φ : Subgroup M) : Set M))).mp hxC
    refine Subgroup.mem_map.mpr ⟨y, ⟨hyH, ?_⟩, rfl⟩
    exact (Subgroup.mem_centralizer_iff (s := (A : Set M'))).mpr fun a ha =>
      hφ (by rw [map_mul, map_mul]; exact hxC' (φ a) (Subgroup.mem_map_of_mem φ ha))

private theorem mfm_comap_inf_centralizer {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) (H A : Subgroup M') :
    (H.map φ ⊓ Subgroup.centralizer (((A.map φ : Subgroup M)) : Set M)).comap φ =
      H ⊓ Subgroup.centralizer (A : Set M') := by
  rw [Subgroup.comap_inf, Subgroup.comap_map_eq_self_of_injective hφ,
    mfm_comap_centralizer hφ A]

private theorem mfm_cent_eq {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {H E : Subgroup M'} {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) (c : R.Code) (hc : R.admissible c) :
    ggLinImage (p := 3) (mfm_coord hφ H E mf)
        (Subgroup.centralizer (((mf.component c).comap φ : Subgroup M') : Set M')) = R.cent c := by
  rw [mfm_ggLinImage_eq hφ mf
    (P := Subgroup.centralizer (((mf.component c).comap φ : Subgroup M') : Set M'))
    (P' := Subgroup.centralizer ((mf.component c : Subgroup M) : Set M))
    (fun e _ => mfm_mem_centralizer_comap_iff hφ (mfm_component_le_range mf c hc) e)]
  exact mf.cent_eq c hc

private theorem mfm_inside_eq {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {H E : Subgroup M'} {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) (c : R.Code) (hc : R.admissible c) :
    ggLinImage (p := 3) (mfm_coord hφ H E mf) ((mf.component c).comap φ) = R.inside c := by
  rw [mfm_ggLinImage_eq hφ mf (P := (mf.component c).comap φ) (P' := mf.component c)
    (fun e _ => (Subgroup.mem_comap).symm)]
  exact mf.inside_eq c hc

private theorem mfm_isComponentOf_map {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {X K : Subgroup M'} (h : Assembly.IsComponentOf X K) :
    Assembly.IsComponentOf (X.map φ) (K.map φ) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map φ,
    (Assembly.IsQuasisimple.congr (Subgroup.equivMapOfInjective X φ hφ)).mp h.2.2⟩

private theorem mfm_isComponentOf_comap {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {Y : Subgroup M} (hY : Y ≤ φ.range) {K' : Subgroup M}
    (h : Assembly.IsComponentOf Y K') :
    Assembly.IsComponentOf (Y.comap φ) (K'.comap φ) :=
  ⟨Subgroup.comap_mono h.1, h.2.1.comap φ,
    (Assembly.IsQuasisimple.congr (mfm_equiv_comap hφ hY)).mpr h.2.2⟩

private theorem mfm_occurs_iff {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {H E : Subgroup M'} {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R)
    (A : Subgroup M') (hA : A ≤ E) (X : Subgroup M') :
    Assembly.IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set M')) ↔
      ∃ c : R.Code, R.admissible c ∧
        R.occurs (ggLinImage (p := 3) (mfm_coord hφ H E mf) A) c ∧
        X = (mf.component c).comap φ := by
  have hA' : A.map φ ≤ E.map φ := Subgroup.map_mono hA
  have himg : ggLinImage (p := 3) (mfm_coord hφ H E mf) A =
      ggLinImage (p := 3) mf.coord (A.map φ) :=
    mfm_ggLinImage_eq hφ mf (P := A) (P' := A.map φ)
      (fun e _ => Subgroup.mem_map_iff_mem hφ)
  constructor
  · intro h
    have hmap : Assembly.IsComponentOf (X.map φ)
        (H.map φ ⊓ Subgroup.centralizer (((A.map φ : Subgroup M)) : Set M)) := by
      rw [← mfm_map_inf_centralizer hφ H A]
      exact mfm_isComponentOf_map hφ h
    obtain ⟨c, hc, hocc, hY⟩ := (mf.occurs_iff (A.map φ) hA' (X.map φ)).mp hmap
    refine ⟨c, hc, ?_, ?_⟩
    · rwa [← himg] at hocc
    · rw [← hY, Subgroup.comap_map_eq_self_of_injective hφ]
  · rintro ⟨c, hc, hocc, rfl⟩
    have hY : mf.component c ≤ φ.range := mfm_component_le_range mf c hc
    have hocc' : R.occurs (ggLinImage (p := 3) mf.coord (A.map φ)) c := by
      rwa [himg] at hocc
    have hcomp : Assembly.IsComponentOf (mf.component c)
        (H.map φ ⊓ Subgroup.centralizer (((A.map φ : Subgroup M)) : Set M)) :=
      (mf.occurs_iff (A.map φ) hA' (mf.component c)).mpr ⟨c, hc, hocc', rfl⟩
    have hcomap := mfm_isComponentOf_comap hφ (Y := mf.component c)
      (K' := H.map φ ⊓ Subgroup.centralizer (((A.map φ : Subgroup M)) : Set M)) hY hcomp
    rwa [mfm_comap_inf_centralizer hφ H A] at hcomap

private theorem mfm_automizer_map {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) (H' E' : Subgroup M') :
    ggAutomizer (H'.map φ) (E'.map φ) =
      (ggAutomizer H' E').map
        (MulAut.congr (Subgroup.equivMapOfInjective E' φ hφ)).toMonoidHom := by
  have h := F4AutWeyl.ggAutomizer_map_eq hφ H' E' (rfl : E'.map φ = E'.map φ)
  rwa [show (Subgroup.equivMapOfInjective E' φ hφ).trans
      (MulEquiv.subgroupCongr (rfl : E'.map φ = E'.map φ))
        = Subgroup.equivMapOfInjective E' φ hφ from by ext x; rfl] at h

private theorem mfm_normalizer_eq {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {H E : Subgroup M'} {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) (c : R.Code) (hc : R.admissible c) :
    (ggAutomizer ((mf.component c).comap φ) E).map
        (ggLin (p := 3) (mfm_coord hφ H E mf)) = R.normalizerGroup c := by
  have hY : mf.component c ≤ φ.range := mfm_component_le_range mf c hc
  calc
    (ggAutomizer ((mf.component c).comap φ) E).map (ggLin (p := 3) (mfm_coord hφ H E mf))
        = (ggAutomizer ((mf.component c).comap φ) E).map
            ((ggLin (p := 3) mf.coord).comp
              (MulAut.congr (Subgroup.equivMapOfInjective E φ hφ)).toMonoidHom) := by
          rw [mfm_ggLin_coord_comp hφ H E mf]
    _ = ((ggAutomizer ((mf.component c).comap φ) E).map
            (MulAut.congr (Subgroup.equivMapOfInjective E φ hφ)).toMonoidHom).map
              (ggLin (p := 3) mf.coord) := by
          rw [Subgroup.map_map]
    _ = (ggAutomizer (mf.component c) (E.map φ)).map (ggLin (p := 3) mf.coord) := by
          rw [← mfm_automizer_map hφ ((mf.component c).comap φ) E,
            Subgroup.map_comap_eq_self hY]
    _ = R.normalizerGroup c := mf.normalizer_eq c hc

private theorem mfm_ambient_normalizer_eq {M M' : Type} [Group M] [Group M'] {φ : M' →* M}
    (hφ : Function.Injective φ) {H E : Subgroup M'} {R : RawFrameData}
    (mf : ModelFrame (H.map φ) (E.map φ) R) :
    (ggAutomizer H E).map (ggLin (p := 3) (mfm_coord hφ H E mf)) = R.ambientNormalizer := by
  rw [mfm_ggLin_coord_comp hφ H E mf, ← Subgroup.map_map, ← mfm_automizer_map hφ H E]
  exact mf.ambientNormalizer_eq

private noncomputable def mfm_frame {M M' : Type} [Group M] [Group M'] {H E : Subgroup M'}
    {R : RawFrameData} {φ : M' →* M} (hφ : Function.Injective φ)
    (mf : ModelFrame (H.map φ) (E.map φ) R) : ModelFrame H E R :=
  { coord := mfm_coord hφ H E mf
    component := fun c => (mf.component c).comap φ
    component_le := fun c hc => mfm_component_le hφ mf c hc
    marked := fun c hc => mfm_marked hφ mf c hc
    occurs_iff := fun A hA X => mfm_occurs_iff hφ mf A hA X
    cent_eq := fun c hc => mfm_cent_eq hφ mf c hc
    inside_eq := fun c hc => mfm_inside_eq hφ mf c hc
    normalizer_eq := fun c hc => mfm_normalizer_eq hφ mf c hc
    ambientNormalizer_eq := mfm_ambient_normalizer_eq hφ mf }

theorem nonempty_modelFrame_of_map {M M' : Type} [Group M] [Group M'] {H E : Subgroup M'}
    {R : RawFrameData} {φ : M' →* M} (hφ : Function.Injective φ)
    (mf : ModelFrame (H.map φ) (E.map φ) R) : Nonempty (ModelFrame H E R) :=
  ⟨mfm_frame hφ mf⟩

theorem exists_compNormal_modelFrame_of_map {M M' : Type} [Group M] [Group M']
    {H E : Subgroup M'} {R : RawFrameData} {φ : M' →* M} (hφ : Function.Injective φ)
    (mf : ModelFrame (H.map φ) (E.map φ) R) (hmf : mf.CompNormal) :
    ∃ mf' : ModelFrame H E R, mf'.CompNormal := by
  refine ⟨mfm_frame hφ mf, ?_⟩
  intro c hc x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  change y ∈ (mf.component c).comap φ ↔ x * y * x⁻¹ ∈ (mf.component c).comap φ
  rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp (hmf c hc (Subgroup.mem_map_of_mem φ hx)) (φ y)

end CFSG.StandardType.GGQ2Frame

end
