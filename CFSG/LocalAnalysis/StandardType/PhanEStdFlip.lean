module

public import CFSG.LocalAnalysis.StandardType.PhanEStdFrob

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
open scoped Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀)

@[expose] noncomputable def stdφ : K ⧸ borel D H → K ⧸ borel D H :=
  Quotient.map' F.φ fun _ _ h =>
    QuotientGroup.leftRel_apply.2 (F.phi_rel (QuotientGroup.leftRel_apply.1 h))

theorem stdφ_mk (g : K) : stdφ F (g : K ⧸ borel D H) = ((F.φ g : K) : K ⧸ borel D H) := rfl

@[expose] noncomputable def stdFlip (n₀ : K) (x : K ⧸ borel D H) : K ⧸ borel D H :=
  n₀ • stdφ F x

theorem stdFlip_mk (n₀ g : K) :
    stdFlip F n₀ (g : K ⧸ borel D H) = ((n₀ * F.φ g : K) : K ⧸ borel D H) := rfl

private theorem q2nPE_nrep_inv (hsq : ∀ i, n i * n i = 1) (w : W) :
    nrep hct w⁻¹ = (nrep hct w)⁻¹ := by
  obtain ⟨ω, hred, rfl⟩ := (cs).exists_isReduced w
  rw [← (cs).wordProd_reverse ω, nrep_wordProd hct hred.reverse, nrep_wordProd hct hred,
    List.map_reverse, List.prod_reverse_noncomm]
  congr 1
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => inv_eq_of_mul_eq_one_right (hsq i)

variable (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
include hext hw₀

theorem stdφ_δ (x y : K ⧸ borel D H) :
    stdδ hct (stdφ F x) (stdφ F y) = w₀ * stdδ hct x y * w₀ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [stdφ_mk, stdφ_mk]
  rw [stdδ_mk_eq_iff hct hext (F.φ g) (F.φ h)
    (w₀ * stdδ hct (g : K ⧸ borel D H) (h : K ⧸ borel D H) * w₀)]
  have hrel : g⁻¹ * h ∈ bruhatCell hct
      (stdδ hct (g : K ⧸ borel D H) (h : K ⧸ borel D H)) :=
    (stdδ_mk_eq_iff hct hext g h _).mp rfl
  have hcell := (F.mem_cell_iff hct hw₀
    (stdδ hct (g : K ⧸ borel D H) (h : K ⧸ borel D H)) (g⁻¹ * h)).2 hrel
  simpa [map_mul, map_inv] using hcell

theorem stdFlip_δ (n₀ : K) (x y : K ⧸ borel D H) :
    stdδ hct (stdFlip F n₀ x) (stdFlip F n₀ y) = w₀ * stdδ hct x y * w₀ := by
  simp only [stdFlip]
  rw [stdδ_smul hct hext n₀ (stdφ F x) (stdφ F y)]
  exact stdφ_δ hct F hext hw₀ x y

theorem stdδ_flip_mk_eq_iff (n₀ g : K) (w : W) :
    stdδ hct (g : K ⧸ borel D H) (stdFlip F n₀ (g : K ⧸ borel D H)) = w ↔
      g⁻¹ * (n₀ * F.φ g) ∈ bruhatCell hct w := by
  rw [stdFlip_mk]
  exact stdδ_mk_eq_iff hct hext g (n₀ * F.φ g) w

theorem stdFlip_smul (n₀ a : K) (x : K ⧸ borel D H) :
    stdFlip F n₀ (a • x) = (n₀ * F.φ a * n₀⁻¹) • stdFlip F n₀ x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : a • (g : K ⧸ borel D H) = ((a * g : K) : K ⧸ borel D H) := by
    rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  rw [ha, stdFlip_mk F n₀ (a * g), stdFlip_mk F n₀ g]
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  have h : n₀ * F.φ (a * g) = (n₀ * F.φ a * n₀⁻¹) * (n₀ * F.φ g) := by
    rw [map_mul]; group
  rw [h]

theorem stdFlip_invol (n₀ : K) (h : ∀ g : K, g⁻¹ * (n₀ * F.φ n₀) * g ∈ borel D H)
    (x : K ⧸ borel D H) : stdFlip F n₀ (stdFlip F n₀ x) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [stdFlip_mk, stdFlip_mk]
  simp only [map_mul, F.invol]
  rw [QuotientGroup.eq]
  have key : (n₀ * (F.φ n₀ * g))⁻¹ * g = (g⁻¹ * (n₀ * F.φ n₀) * g)⁻¹ := by group
  rw [key]
  exact (borel D H).inv_mem (h g)

theorem nrep_mul_phi_self (hsq : ∀ i, n i * n i = 1) :
    nrep hct w₀ * F.φ (nrep hct w₀) = 1 := by
  have hφ : F.φ (nrep hct w₀) = nrep hct w₀ := by
    rw [F.nrep_map hct hw₀ w₀,
      show w₀ * w₀ * w₀ = w₀ by rw [hw₀.mul_self, one_mul]]
  rw [hφ]
  exact (mul_eq_one_iff_eq_inv).2
    (show nrep hct w₀ = (nrep hct w₀)⁻¹ by
      rw [← q2nPE_nrep_inv hct hsq w₀, hw₀.inv_eq])

end CFSG.ClassicalInvolution.Phan.PhanE
