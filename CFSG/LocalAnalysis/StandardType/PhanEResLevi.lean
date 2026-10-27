module

public import CFSG.LocalAnalysis.StandardType.PhanEResPanel
public import CFSG.Monster.B.Geometry.InitialIsometryProduct

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.AGLEmbeddingD2.ParabLevi
open scoped Pointwise

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem exists_borel_levi (I : Set (Fin D.rank)) {b : K} (hb : b ∈ borel D H) :
    ∃ t ∈ ⨆ k, H k, ∃ m ∈ leviM D I, ∀ l ∈ leviM D I,
      ((b * l : K) : K ⧸ borel D H) = ((t * m * l : K) : K ⧸ borel D H) := by
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb
  have hnorm : leviM D I ≤ Subgroup.normalizer (leviRad D I : Set K) :=
    iSup₂_le fun i hi => rankOne_le_normalizer_leviRad hext hi
  have hu' : u ∈ (leviM D I : Set K) * (leviRad D I : Set K) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (leviM D I) (leviRad D I) hnorm,
      sup_comm]
    exact posUnipotent_le_leviRad_sup_leviM hct hu
  obtain ⟨m, hm, r, hr, rfl⟩ := hu'
  refine ⟨t, ht, m, hm, fun l hl => ?_⟩
  have hrB : l⁻¹ * r * l ∈ borel D H := by
    show l⁻¹ * r * l ∈ (⨆ k, H k) ⊔ posUnipotent D
    exact Subgroup.mem_sup_right (leviRad_le_posUnipotent
      ((Subgroup.mem_normalizer_iff''.mp (hnorm hl) r).mp hr))
  refine (QuotientGroup.eq.mpr ?_).symm
  have he : (t * m * l)⁻¹ * (t * (m * r) * l) = l⁻¹ * r * l := by group
  rw [he]
  exact hrB

include hext in
theorem exists_parabolic_levi (I : Set (Fin D.rank)) {p : K}
    (hp : ((p : K) : K ⧸ borel D H) ∈ residue (cs) (stdδ hct) I ((1 : K) : K ⧸ borel D H)) :
    ∃ t ∈ ⨆ k, H k, ∃ m ∈ leviM D I, ∀ l ∈ leviM D I,
      ((p * l : K) : K ⧸ borel D H) = ((t * m * l : K) : K ⧸ borel D H) := by
  rw [residue_eq_image_leviM hct hext I (1 : K)] at hp
  obtain ⟨l', hl', hp'⟩ := hp
  have hp'l : (p : K ⧸ borel D H) = (l' : K ⧸ borel D H) := by simpa using hp'.symm
  have hb : l'⁻¹ * p ∈ borel D H := QuotientGroup.eq.mp hp'l.symm
  obtain ⟨t, ht, m, hm, hml⟩ := exists_borel_levi hct hext I hb
  have hmm : t⁻¹ * l' * t ∈ leviM D I := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (torus_le_normalizer_leviM hct (inv_mem ht)) l').mp hl'
    simpa only [inv_inv] using h
  refine ⟨t, ht, (t⁻¹ * l' * t) * m, mul_mem hmm hm, fun l hl => ?_⟩
  have hpK : p = l' * (l'⁻¹ * p) := by group
  have h1 : (((l'⁻¹ * p) * l : K) : K ⧸ borel D H) =
      ((t * m * l : K) : K ⧸ borel D H) := hml l hl
  calc ((p * l : K) : K ⧸ borel D H)
      = p • (l : K ⧸ borel D H) := by
          simpa only [smul_eq_mul] using
            (MulAction.Quotient.smul_coe (borel D H) p l).symm
    _ = (l' * (l'⁻¹ * p)) • (l : K ⧸ borel D H) := by
          nth_rewrite 1 [hpK]
          rfl
    _ = l' • ((l'⁻¹ * p) • (l : K ⧸ borel D H)) := by rw [mul_smul]
    _ = l' • (((l'⁻¹ * p) * l : K) : K ⧸ borel D H) := rfl
    _ = l' • ((t * m * l : K) : K ⧸ borel D H) := by rw [h1]
    _ = ((l' * (t * m * l) : K) : K ⧸ borel D H) := by
          simpa only [smul_eq_mul] using
            MulAction.Quotient.smul_coe (borel D H) l' (t * m * l)
    _ = ((t * ((t⁻¹ * l' * t) * m) * l : K) : K ⧸ borel D H) := by
          congr 1; group

theorem nrep_conj_mem_leviM {I I' : Set (Fin D.rank)} {v : W}
    (hv : ∀ i ∈ I', ∃ j ∈ I, weylAction D.isFiniteType v (Pi.single i 1) = Pi.single j 1)
    {l : K} (hl : l ∈ leviM D I') : nrep hct v * l * (nrep hct v)⁻¹ ∈ leviM D I := by
  refine conj_mem_of_forall_mem (P := I') (X := fun i => rankOne D.rootGroup i)
    (M := leviM D I) (c := nrep hct v) ?_ hl
  intro i hi
  show D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤
    (leviM D I).comap (MulAut.conj (nrep hct v)).toMonoidHom
  refine sup_le ?_ ?_
  · intro y hy
    obtain ⟨j, hj, hvj⟩ := hv i hi
    have hmem : nrep hct v * y * (nrep hct v)⁻¹ ∈ D.rootGroup (Pi.single j 1) := by
      simpa only [hvj] using (actsAs_nrep hct v).conj_mem
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i) hy
    exact rankOne_le_leviM hj (Subgroup.mem_sup_left hmem)
  · intro y hy
    obtain ⟨j, hj, hvj⟩ := hv i hi
    have hγ : -Pi.single i 1 ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
    have hneg : weylAction D.isFiniteType v (-Pi.single i 1) = -Pi.single j 1 := by
      rw [map_neg, hvj]
    have hmem : nrep hct v * y * (nrep hct v)⁻¹ ∈ D.rootGroup (-Pi.single j 1) := by
      have h := (actsAs_nrep hct v).conj_mem hγ hy
      rwa [hneg] at h
    exact rankOne_le_leviM hj (Subgroup.mem_sup_right hmem)

include hext in
theorem resProj_smul (J : Set (Fin D.rank)) (k : K) (x y : K ⧸ borel D H) :
    resProj (cs) (stdδ hct) J (k • x) (k • y) = k • resProj (cs) (stdδ hct) J x y := by
  refine resProj_map (stdBuilding hct hext) (stdBuilding hct hext)
    (f := fun z => k • z) ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [mem_residue_iff_mem_parabolic (stdBuilding hct hext)] at hz ⊢
      rwa [stdδ_smul hct hext k x z]
    · intro a _ b _ hab
      have hab' : k • a = k • b := hab
      calc a = k⁻¹ • (k • a) := (inv_smul_smul k a).symm
        _ = k⁻¹ • (k • b) := by rw [hab']
        _ = b := inv_smul_smul k b
    · intro z hz
      refine ⟨k⁻¹ • z, ?_, smul_inv_smul k z⟩
      rw [mem_residue_iff_mem_parabolic (stdBuilding hct hext)] at hz ⊢
      have h := stdδ_smul hct hext k x (k⁻¹ • z)
      rw [smul_inv_smul] at h
      rwa [h] at hz
  · intro q _
    exact stdδ_smul hct hext k y q

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
