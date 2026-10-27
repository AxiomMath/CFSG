module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialitySpin
public import CFSG.LieType.Universal.Spin.Datum

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.StandardType.GGRootNorm
open CFSG.StandardType.Triality CFSG.LieType.Universal.Spin

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

theorem ggTrivialOnNormalizer_conj {K : Type*} [Group K] (R : Subgroup K) (y τ : MulAut K)
    (h : GGTrivialOnNormalizer R y) :
    GGTrivialOnNormalizer (R.map τ.toMonoidHom) (τ * y * τ⁻¹) := by
  obtain ⟨hR, hmod⟩ := h
  constructor
  ·
    have hmap : (R.map τ.toMonoidHom).map (τ * y * τ⁻¹).toMonoidHom =
        (R.map y.toMonoidHom).map τ.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.mul_apply, mul_assoc]
    rw [hmap, hR]
  ·
    intro n hn
    have hn' : n ∈ (Subgroup.normalizer (R : Set K)).map τ.toMonoidHom := by
      rw [← normalizer_map_mulEquiv τ R]
      exact hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn'
    change (τ * y * τ⁻¹) (τ m) * (τ m)⁻¹ ∈
      pCoreOf 2 (Subgroup.normalizer (Subgroup.map τ.toMonoidHom R))
    have h1 : (τ * y * τ⁻¹) (τ m) * (τ m)⁻¹ = τ (y m * m⁻¹) := by
      rw [show (τ * y * τ⁻¹) (τ m) = τ (y m) by simp [MulAut.mul_apply]]
      rw [map_mul, map_inv]
    rw [h1]
    have h2 := hmod m hm
    have h3 : τ (y m * m⁻¹) ∈
        (pCoreOf 2 (Subgroup.normalizer (R : Set K))).map τ.toMonoidHom :=
      ⟨y m * m⁻¹, h2, rfl⟩
    rw [normalizer_map_mulEquiv τ R, pCoreOf_map_mulEquiv τ (Subgroup.normalizer (R : Set K))]
    exact h3

private theorem irtrans_map_rootGroup_triSpinAut {F : Type} [Field F] [Finite F] [CharP F 2]
    {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) :
    (plusRootGroup 4 F three_le_four γ).map
        (triSpinAut : MulAut ↥(spinGroup (quadPlus 4 F))).toMonoidHom =
      plusRootGroup 4 F three_le_four (tri γ) := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨c, rfl⟩ :=
      ((CFSG.LieType.Steinberg.SpinPlus.isParametrization three_le_four γ hγ).1 w).1 hw
    change triSpinAut (xr γ c) ∈ plusRootGroup 4 F three_le_four (tri γ)
    rw [triSpinAut_xr hγ c]
    exact ((CFSG.LieType.Steinberg.SpinPlus.isParametrization three_le_four (tri γ)
      (tri_mem_roots hγ)).1 (xr (tri γ) c)).2 ⟨c, rfl⟩
  · rintro hz
    obtain ⟨c, rfl⟩ :=
      ((CFSG.LieType.Steinberg.SpinPlus.isParametrization three_le_four (tri γ)
        (tri_mem_roots hγ)).1 z).1 hz
    exact Subgroup.mem_map.mpr
      ⟨xr γ c, ((CFSG.LieType.Steinberg.SpinPlus.isParametrization three_le_four γ hγ).1
        (xr γ c)).2 ⟨c, rfl⟩, triSpinAut_xr hγ c⟩

private theorem irtrans_map_triSpinAut_pow {F : Type} [Field F] [Finite F] [CharP F 2]
    {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (j : ℕ) :
    (plusRootGroup 4 F three_le_four γ).map
        ((triSpinAut : MulAut ↥(spinGroup (quadPlus 4 F))) ^ j).toMonoidHom =
      plusRootGroup 4 F three_le_four ((tri^[j]) γ) := by
  have hmem : ∀ k : ℕ, (tri^[k]) γ ∈ rootsD4 := by
    intro k
    induction k with
    | zero => simpa using hγ
    | succ k ihk =>
      rw [Function.iterate_succ_apply']
      exact tri_mem_roots ihk
  induction j with
  | zero =>
    rw [pow_zero, Function.iterate_zero]
    show Subgroup.map (MonoidHom.id ↥(spinGroup (quadPlus 4 F)))
      (plusRootGroup 4 F three_le_four γ) = plusRootGroup 4 F three_le_four γ
    rw [Subgroup.map_id]
  | succ j ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    have hmul : (((triSpinAut : MulAut ↥(spinGroup (quadPlus 4 F))) *
        (triSpinAut : MulAut ↥(spinGroup (quadPlus 4 F))) ^ j).toMonoidHom) =
        (triSpinAut : MulAut ↥(spinGroup (quadPlus 4 F))).toMonoidHom.comp
          ((triSpinAut : MulAut ↥(spinGroup (quadPlus 4 F))) ^ j).toMonoidHom := by
      ext x
      rfl
    rw [hmul, ← Subgroup.map_map, ih]
    exact irtrans_map_rootGroup_triSpinAut (hmem j)

private theorem irtrans_map_conj_map {G : Type*} [Group G] (S : Subgroup G) (g : G)
    (e : MulAut G) :
    (S.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (S.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem map_triSpinAut_conj_rootGroup {F : Type} [Field F] [Finite F] [CharP F 2]
    {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (u : ↥(spinGroup (Spin.quadPlus 4 F))) (j : ℕ) :
    (((Spin.plusDatum 4 F (by norm_num)).rootGroup γ).map
        (MulAut.conj u).toMonoidHom).map
        ((triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j).toMonoidHom =
      (((Spin.plusDatum 4 F (by norm_num)).rootGroup ((tri^[j]) γ)).map
        (MulAut.conj
          (((triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j) u)).toMonoidHom) := by
  change ((plusRootGroup 4 F three_le_four γ).map (MulAut.conj u).toMonoidHom).map
        ((triSpinAut : MulAut ↥(spinGroup (quadPlus 4 F))) ^ j).toMonoidHom =
      (plusRootGroup 4 F three_le_four ((tri^[j]) γ)).map
        (MulAut.conj (((triSpinAut : MulAut ↥(spinGroup (quadPlus 4 F))) ^ j) u)).toMonoidHom
  rw [irtrans_map_conj_map, irtrans_map_triSpinAut_pow hγ j]

theorem tri_iterate_mem_roots {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (j : ℕ) :
    (tri^[j]) γ ∈ rootsD4 := by
  induction j with
  | zero => simpa using hγ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact tri_mem_roots ih

end CFSG.StandardType.LieKnownR2.POmega.Inner
