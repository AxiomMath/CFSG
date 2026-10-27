module

public import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Defs
import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.TwoGroup
import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Generators
import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Centralizer
import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Witness
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.SylowIndex

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Orth6Minus

private lemma isPGroup_comap_map_closure_gens {F : Type*} [Field F] {Y : Type*} [Group Y]
    (f : Y →* Matrix.ProjGenLinGroup Six F) (hf : Function.Injective f) :
    IsPGroup 2 (((Subgroup.closure (gens F)).map Matrix.ProjGenLinGroup.mk).comap f) :=
  ((isPGroup_closure_gens F).map Matrix.ProjGenLinGroup.mk).comap_of_injective f hf

private lemma orderOf_conj_inv_mul {Y : Type*} [Group Y] {d : Y} (x : Y)
    (hd : orderOf d = 2) : orderOf (x⁻¹ * d * x) = 2 := by
  have h : (MulAut.conj x⁻¹) d = x⁻¹ * d * x := by simp [MulAut.conj_apply]
  rw [← h, MulEquiv.orderOf_eq, hd]

private lemma eq_mk_tGL_of_orderOf_eq_two {F : Type*} [Field F] (h3 : (3 : F) = 0)
    {Y : Type*} [Group Y] (f : Y →* Matrix.ProjGenLinGroup Six F)
    (hf : Function.Injective f) {d₁ : Y} (hd₁ : orderOf d₁ = 2)
    (himg : f d₁ ∈ (orthSix F).map Matrix.ProjGenLinGroup.mk)
    (hc : ∀ s ∈ gens F,
      f d₁ * Matrix.ProjGenLinGroup.mk s = Matrix.ProjGenLinGroup.mk s * f d₁) :
    f d₁ = Matrix.ProjGenLinGroup.mk (tGL F) := by
  obtain ⟨g, hg, hfg⟩ := Subgroup.mem_map.mp himg
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h1 : (1 : F) = 0 := by
      have h31 : (3 : F) = 2 + 1 := by norm_num
      rw [h31, h, zero_add] at h3
      exact h3
    exact one_ne_zero h1
  have hkey := mk_eq_one_or_eq_mk_tGL h2 hg (fun s hs => by rw [hfg]; exact hc s hs)
  rcases hkey with h | h
  · exfalso
    have h1 : f d₁ = 1 := hfg ▸ h
    have hd1 : d₁ = 1 := hf (by rw [h1, map_one])
    rw [hd1, orderOf_one] at hd₁
    omega
  · exact hfg ▸ h

private lemma commute_mk_gens {F : Type*} [Field F] {Y : Type*} [Group Y]
    (f : Y →* Matrix.ProjGenLinGroup Six F)
    (hlo : CFSG.PGLModel.projImage ⁅orthSix F, orthSix F⁆ ≤ f.range) {d₁ : Y}
    (hcen : ∀ e ∈ ((Subgroup.closure (gens F)).map
      Matrix.ProjGenLinGroup.mk).comap f, Commute e d₁) :
    ∀ s ∈ gens F, f d₁ * Matrix.ProjGenLinGroup.mk s =
      Matrix.ProjGenLinGroup.mk s * f d₁ := by
  intro s hs
  have hgen : s ∈ Subgroup.closure (gens F) := Subgroup.subset_closure hs
  have hsmem : Matrix.ProjGenLinGroup.mk s ∈
      (Subgroup.closure (gens F)).map Matrix.ProjGenLinGroup.mk :=
    Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk hgen
  have hsmem' : Matrix.ProjGenLinGroup.mk s ∈
      CFSG.PGLModel.projImage ⁅orthSix F, orthSix F⁆ := by
    rw [CFSG.PGLModel.projImage]
    exact Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk
      (closure_gens_le_commutator F hgen)
  obtain ⟨e, hfe⟩ := MonoidHom.mem_range.mp (hlo hsmem')
  have he : e ∈ ((Subgroup.closure (gens F)).map
      Matrix.ProjGenLinGroup.mk).comap f := by
    rw [Subgroup.mem_comap, hfe]
    exact hsmem
  have h2 : f e * f d₁ = f d₁ * f e := by
    rw [← map_mul, ← map_mul, (hcen e he).eq]
  rw [← hfe]
  exact h2.symm

private lemma exists_isConj_orderOf_mul_eq_four {F : Type*} [Field F] (h3 : (3 : F) = 0)
    {Y : Type*} [Group Y] (f : Y →* Matrix.ProjGenLinGroup Six F)
    (hf : Function.Injective f)
    (hlo : CFSG.PGLModel.projImage ⁅orthSix F, orthSix F⁆ ≤ f.range) {d₁ : Y}
    (hfd₁ : f d₁ = Matrix.ProjGenLinGroup.mk (tGL F)) :
    ∃ d₂ : Y, IsConj d₁ d₂ ∧ orderOf (d₁ * d₂) = 4 := by
  obtain ⟨w, hw, hword⟩ := exists_mem_commutator_orderOf_eq_four h3
  have hwmem : Matrix.ProjGenLinGroup.mk w ∈
      CFSG.PGLModel.projImage ⁅orthSix F, orthSix F⁆ := by
    rw [CFSG.PGLModel.projImage]
    exact Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk hw
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp (hlo hwmem)
  refine ⟨y₀ * d₁ * y₀⁻¹, isConj_iff.mpr ⟨y₀, rfl⟩, ?_⟩
  have hfprod : f (d₁ * (y₀ * d₁ * y₀⁻¹)) = Matrix.ProjGenLinGroup.mk (tGL F) *
      (Matrix.ProjGenLinGroup.mk w * Matrix.ProjGenLinGroup.mk (tGL F) *
        (Matrix.ProjGenLinGroup.mk w)⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, hy₀, hfd₁]
  rw [← orderOf_injective f hf (d₁ * (y₀ * d₁ * y₀⁻¹)), hfprod, hword]

theorem even_index_centralizer_of_isOddTransp {F : Type*} [Field F] (h3 : (3 : F) = 0)
    {Y : Type*} [Group Y] [Finite Y] (f : Y →* Matrix.ProjGenLinGroup Six F)
    (hf : Function.Injective f)
    (hlo : CFSG.PGLModel.projImage ⁅orthSix F, orthSix F⁆ ≤ f.range)
    (hhi : f.range ≤ (orthSix F).map Matrix.ProjGenLinGroup.mk) (d : Y)
    (hd : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {y : Y | IsConj d y}) :
    Even (Subgroup.centralizer ({d} : Set Y)).index := by
  by_contra hne
  have hnot2 : ¬ 2 ∣ (Subgroup.centralizer ({d} : Set Y)).index := by
    rwa [even_iff_two_dvd] at hne
  let E : Subgroup Y :=
    ((Subgroup.closure (gens F)).map Matrix.ProjGenLinGroup.mk).comap f
  have hE : IsPGroup 2 E := isPGroup_comap_map_closure_gens f hf
  obtain ⟨x, hx⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.exists_conj_le_of_not_dvd_index
      Nat.prime_two (Subgroup.centralizer ({d} : Set Y)) hnot2 E hE
  let d₁ : Y := x⁻¹ * d * x
  have hd₁D : d₁ ∈ {y : Y | IsConj d y} := isConj_iff.mpr ⟨x⁻¹, by simp [d₁]⟩
  have hd₁ord : orderOf d₁ = 2 := orderOf_conj_inv_mul x (hd.1 d (IsConj.refl d))
  have hcen : ∀ e ∈ E, Commute e d₁ := by
    intro e he
    have h1 : Commute (x * e * x⁻¹) d :=
      Subgroup.mem_centralizer_singleton_iff.mp (hx e he)
    have h2 := h1.conj x⁻¹
    have he' : x⁻¹ * (x * e * x⁻¹) * (x⁻¹)⁻¹ = e := by group
    have hd' : x⁻¹ * d * (x⁻¹)⁻¹ = d₁ := by simp [d₁]
    rwa [he', hd'] at h2
  have hc : ∀ s ∈ gens F, f d₁ * Matrix.ProjGenLinGroup.mk s =
      Matrix.ProjGenLinGroup.mk s * f d₁ := commute_mk_gens f hlo hcen
  have hfd₁ : f d₁ = Matrix.ProjGenLinGroup.mk (tGL F) :=
    eq_mk_tGL_of_orderOf_eq_two h3 f hf hd₁ord (hhi (MonoidHom.mem_range.mpr ⟨d₁, rfl⟩)) hc
  obtain ⟨d₂, hd₂conj, hd₂ord⟩ := exists_isConj_orderOf_mul_eq_four h3 f hf hlo hfd₁
  have hd₂D : d₂ ∈ {y : Y | IsConj d y} := hd₁D.trans hd₂conj
  have hbad := hd.2 d₁ hd₁D d₂ hd₂D
  rw [hd₂ord] at hbad
  rcases hbad with hbad | hbad
  · exact absurd hbad (by norm_num)
  · obtain ⟨k, hk⟩ := hbad
    omega

end CFSG.LocalAnalysis.WeakClosure81.Orth6Minus
