module

public import CFSG.LocalAnalysis.StandardType.GGStdPosTorus
public import CFSG.LieType.Steinberg.Bridge
public import CFSG.LieType.Steinberg.Collection
public import CFSG.LieType.TitsSimplicity.Unipotent
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg
open scoped commutatorElement

theorem ggStdPos_posUnipotent_inf_le {K G : Type*} [Group K] [Group G]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (htr : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, ∀ x' ∈ D.rootGroup γ, x ≠ 1 → x' ≠ 1 →
      ∃ t ∈ ggTorus D, t * x * t⁻¹ = x')
    (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) (S : Set G)
    (hS : ∀ s ∈ S, ∀ γ ∈ D.roots, ∃ h ∈ ggTorus D, ∀ z ∈ D.rootGroup γ,
      s * ψ z * s⁻¹ = ψ (h * z * h⁻¹)) :
    posUnipotent D ⊓ (Subgroup.centralizer S).comap ψ ≤
      ⨆ β ∈ {β | β ∈ D.roots ∧ D.rootGroup β ≤ (Subgroup.centralizer S).comap ψ},
        D.rootGroup β := by
  rintro v ⟨hv, hvC⟩
  obtain ⟨L, hnd, hL, hs, hinj⟩ := (isSteinberg_of hct hext).exists_posList
  have hr : ∀ γ ∈ L, γ ∈ D.roots := fun γ hγ => ((hL γ).1 hγ).1.1
  have hpos : ∀ γ ∈ L, 0 < ht γ := fun γ hγ => ((hL γ).1 hγ).1.2
  have hle : posUnipotent D ≤ ⨆ v ∈ L, D.rootGroup v := by
    refine iSup₂_le fun γ hγ => ?_
    by_cases hind : (RootSystem.ofCartan D.isFiniteType D.divisible).IsIndiv γ
    · exact le_iSup₂_of_le γ ((hL γ).2 ⟨hγ, hind⟩) le_rfl
    · obtain ⟨δ, hδ, hδ', rfl⟩ :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).exists_eq_two_smul hγ.1 hind
      exact (hext.two_smul_le δ hδ hγ.1).trans (le_iSup₂_of_le δ ((hL δ).2 ⟨
        (RootSystem.ofCartan D.isFiniteType D.divisible).mem_pos_of_two_smul_mem_pos hγ hδ,
        hδ'⟩) le_rfl)
  have hc : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ D.rootGroup a, ∀ y ∈ D.rootGroup b,
      ⁅x, y⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (ht a) (ht b) < ht c), D.rootGroup c := by
    intro a ha b hb hab x hx y hy
    have hxy := hext.commutator_mem a (hr a ha) b (hr b hb)
      ((RootSystem.ofCartan D.isFiniteType D.divisible).linIndepPair_of_mem_pos ((hL a).1 ha).1
        ((hL a).1 ha).2 ((hL b).1 hb).1 ((hL b).1 hb).2 hab) x hx y hy
    have hle' : (⨆ ε ∈ openCone D.roots a b, D.rootGroup ε) ≤
        ⨆ c ∈ L, ⨆ (_ : min (ht a) (ht b) < ht c), D.rootGroup c := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨c, hc, hlt, hcε⟩ :=
        (RootSystem.ofCartan D.isFiniteType D.divisible).exists_of_mem_openCone_pos
          ((hL a).1 ha).1 ((hL a).1 ha).2 ((hL b).1 hb).1 ((hL b).1 hb).2 hab hε
      have hcL : c ∈ L := (hL c).2 hc
      have hle : D.rootGroup ε ≤ D.rootGroup c := by
        rcases hcε with rfl | rfl
        · exact le_rfl
        · exact hext.two_smul_le c (hr c hcL) hε.1
      exact hle.trans (le_iSup₂_of_le c hcL (le_iSup_of_le hlt le_rfl))
    exact hle' hxy
  obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem D.rootGroup (fun γ => ht γ) hnd hs hc
    v (hle hv)
  have hTeq := ggStdPos_ggTorus_eq hct hext hBU
  have hcomm : ∀ a ∈ ggTorus D, ∀ b ∈ ggTorus D, a * b = b * a := by
    intro a ha b hb
    rw [hTeq] at ha hb
    exact LieType.TitsSimplicity.iSup_le_centralizer_iSup hext hb a ha
  have hZT : Subgroup.center K ≤ ⨆ i, H i :=
    (LieType.TitsSimplicity.center_eq_normalCore_borel hct hext hBU).le.trans
      (LieType.TitsSimplicity.normalCore_borel_le_iSup hct hBU)
  have hsc : ∀ γ ∈ D.roots, ∀ h ∈ ggTorus D, ∀ x ∈ D.rootGroup γ, x ≠ 1 → h * x * h⁻¹ = x →
      ∀ z ∈ D.rootGroup γ, h * z * h⁻¹ = z := by
    intro γ hγ h hh x hx hx1 hfix z hz
    by_cases hz1 : z = 1
    · rw [hz1, mul_one, mul_inv_cancel]
    obtain ⟨t, ht, rfl⟩ := htr γ hγ x hx z hz hx1 hz1
    calc h * (t * x * t⁻¹) * h⁻¹ = (h * t) * x * (h * t)⁻¹ := by group
      _ = (t * h) * x * (t * h)⁻¹ := by rw [hcomm h hh t ht]
      _ = t * (h * x * h⁻¹) * t⁻¹ := by group
      _ = t * x * t⁻¹ := by rw [hfix]
  have hfix : ∀ s ∈ S, ∀ γ ∈ L, ∃ h ∈ ggTorus D, h * f γ * h⁻¹ = f γ ∧
      ∀ z ∈ D.rootGroup γ, s * ψ z * s⁻¹ = ψ (h * z * h⁻¹) := by
    intro s hsS
    choose! h hh he using hS s hsS
    set g : (Fin D.rank → ℤ) → K := fun γ => h γ * f γ * (h γ)⁻¹
    have hgX : ∀ γ ∈ L, g γ ∈ D.rootGroup γ := fun γ hγ =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_iInf.mp
        (Subgroup.mem_iInf.mp (hh γ (hr γ hγ)) γ) (hr γ hγ)) (f γ)).mp (hf γ hγ)
    have hψ : ψ (L.map g).prod = ψ (L.map f).prod := by
      have h1 : ψ (L.map g).prod = s * ψ (L.map f).prod * s⁻¹ := by
        rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
        have h2 := map_list_prod (MulAut.conj s).toMonoidHom (L.map (ψ ∘ f))
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
          List.map_map] at h2
        rw [h2]
        exact congrArg List.prod
          (List.map_congr_left fun γ hγ => (he γ (hr γ hγ) _ (hf γ hγ)).symm)
      rw [h1]
      have hc' := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hvC) s hsS
      rw [hc', mul_inv_cancel_right]
    have hU : ∀ F : (Fin D.rank → ℤ) → K, (∀ γ ∈ L, F γ ∈ D.rootGroup γ) →
        (L.map F).prod ∈ posUnipotent D := fun F hF =>
      Subgroup.list_prod_mem _ fun y hy => by
        obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hy
        exact rootGroup_le_posUnipotent (hr γ hγ) (hpos γ hγ) (hF γ hγ)
    have heq : (L.map g).prod = (L.map f).prod := by
      have hk : ((L.map f).prod)⁻¹ * (L.map g).prod ∈ (⨆ i, H i) ⊓ posUnipotent D :=
        Subgroup.mem_inf.mpr
          ⟨hZT (hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψ, inv_mul_cancel])),
            mul_mem (inv_mem (hU f hf)) (hU g hgX)⟩
      rw [show posUnipotent D = ⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ from rfl,
        hext.torus_inf_posPart, Subgroup.mem_bot] at hk
      exact (inv_mul_eq_one.mp hk).symm
    intro γ hγ
    exact ⟨h γ, hh γ (hr γ hγ), hinj g f hgX hf heq γ hγ, he γ (hr γ hγ)⟩
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hy
  by_cases hf1 : f γ = 1
  · rw [hf1]
    exact one_mem _
  have hXC : D.rootGroup γ ≤ (Subgroup.centralizer S).comap ψ := by
    intro z hz
    refine Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_iff.mpr fun s hsS => ?_)
    obtain ⟨h, hh, hfx, he⟩ := hfix s hsS γ hγ
    have h1 := he z hz
    rw [hsc γ (hr γ hγ) h hh (f γ) (hf γ hγ) hf1 hfx z hz] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  exact le_iSup₂_of_le (f := fun β (_ : β ∈ {β | β ∈ D.roots ∧
    D.rootGroup β ≤ (Subgroup.centralizer S).comap ψ}) => D.rootGroup β) γ ⟨hr γ hγ, hXC⟩
    le_rfl (hf γ hγ)

end CFSG.StandardType

end
