module

public import CFSG.LocalAnalysis.StandardType.PhanEFixedTorus

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀) (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

include hext hw₀ in
theorem stdδ_one_flip :
    stdδ hct ((1 : K) : K ⧸ borel D H) (stdFlip F (nrep hct w₀) ((1 : K) : K ⧸ borel D H)) =
      w₀ := by
  apply (stdδ_flip_mk_eq_iff hct F hext hw₀ (nrep hct w₀) (1 : K) w₀).2
  have h1 : (1 : K)⁻¹ * (nrep hct w₀ * F.φ (1 : K)) = nrep hct w₀ := by
    rw [map_one, mul_one, inv_one, one_mul]
  rw [h1]
  exact nrep_mem_bruhatCell hct w₀

include hext hw₀ hsq in
theorem exists_stdFix_mk_eq (hBU : BruhatExtras D H) (L : StdLevi F (nrep hct w₀))
    (x : K ⧸ borel D H) (hx : stdδ hct x (stdFlip F (nrep hct w₀) x) = w₀) :
    ∃ g ∈ stdFix F (nrep hct w₀), ((g : K) : K ⧸ borel D H) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hcell : g⁻¹ * (nrep hct w₀ * F.φ g) ∈ bruhatCell hct w₀ :=
    (stdδ_flip_mk_eq_iff hct F hext hw₀ (nrep hct w₀) g w₀).1 hx
  obtain ⟨b₁, hb₁, b₂, hb₂, heq⟩ := hcell
  have hb₂φ : F.φ b₂ ∈ borel D H := (F.mem_borel_iff b₂).2 hb₂
  have hγ : nrep hct w₀ * b₂ * (nrep hct w₀)⁻¹ ∈
      (borel D H).map (stdTau F (nrep hct w₀)) := by
    refine Subgroup.mem_map.2 ⟨F.φ b₂, hb₂φ, ?_⟩
    rw [stdTau_apply, F.invol]
  have hh : g⁻¹ * stdTau F (nrep hct w₀) g
      = b₁ * (nrep hct w₀ * b₂ * (nrep hct w₀)⁻¹) := by
    rw [stdTau_apply]
    calc g⁻¹ * (nrep hct w₀ * F.φ g * (nrep hct w₀)⁻¹)
        = (g⁻¹ * (nrep hct w₀ * F.φ g)) * (nrep hct w₀)⁻¹ := by group
      _ = (b₁ * nrep hct w₀ * b₂) * (nrep hct w₀)⁻¹ := by rw [heq]
      _ = b₁ * (nrep hct w₀ * b₂ * (nrep hct w₀)⁻¹) := by group
  obtain ⟨b, hbB, hbfix⟩ :=
    exists_mul_mem_fix (stdTau F (nrep hct w₀)) (stdTau_stdTau hct F hext hw₀ hsq)
      (borel_inf_map_stdTau hct F hext hw₀ hsq hBU)
      (fun s hs hτs => torus_lang F hext L hs hτs) hb₁ hγ hh
  refine ⟨g * b, (mem_stdFix_iff F (nrep hct w₀) (g * b)).2 hbfix, ?_⟩
  rw [QuotientGroup.eq]
  rw [show (g * b)⁻¹ * g = b⁻¹ by group]
  exact (borel D H).inv_mem hbB

end CFSG.ClassicalInvolution.Phan.PhanE
