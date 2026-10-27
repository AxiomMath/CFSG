module

public import CFSG.LocalAnalysis.StandardType.PhanEStdFlip
public import CFSG.LocalAnalysis.StandardType.PhanEReduction
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

theorem q2nPE_mem_parabolic_univ (w : W) : w ∈ (cs).parabolic Set.univ := by
  rw [CoxeterSystem.parabolic_univ (coxeterMatrix D.isFiniteType).toCoxeterSystem]
  exact Subgroup.mem_top w

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀)

@[expose] def StdPanel (n₀ : K) : Prop :=
  ∀ (i : Fin D.rank) (x : K ⧸ borel D H),
    ∃ y ∈ residue (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) {i} x,
      ∃ u ∈ residue (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) {i} x,
        (cs).length (stdδ hct u (stdFlip F n₀ y)) < (cs).length (stdδ hct y (stdFlip F n₀ y))

variable (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)

include hext hw₀ in
theorem stdIsSphericalFlip (n₀ : K) (hn₀ : ∀ g : K, g⁻¹ * (n₀ * F.φ n₀) * g ∈ borel D H)
    (hpanel : StdPanel hct F n₀) :
    IsSphericalFlip (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) w₀
      (stdFlip F n₀) where
  invol x := stdFlip_invol F hext hw₀ n₀ hn₀ x
  dist x y := stdFlip_δ hct F hext hw₀ n₀ x y
  panel := hpanel

include hext hw₀ in
theorem stdIsSphericalFlip_one (hpanel : StdPanel hct F 1) :
    IsSphericalFlip (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) w₀
      (stdFlip F 1) :=
  stdIsSphericalFlip hct F hext hw₀ 1 (fun g => by simp [map_one]) hpanel

@[expose] noncomputable def stdBuildingData (hsq : ∀ i, n i * n i = 1)
    (hpanel : StdPanel hct F (nrep hct w₀)) :
    PhanEBuildingData (coxeterMatrix D.isFiniteType) where
  w₀ := w₀
  longest w := by
    simpa using hw₀.length_mul_left (q2nPE_mem_parabolic_univ w)
  C := K ⧸ borel D H
  δ := stdδ hct
  building := stdBuilding hct hext
  thick := std_thick hct hext
  t := stdFlip F (nrep hct w₀)
  flip := stdIsSphericalFlip hct F hext hw₀ (nrep hct w₀)
    (fun g => by
      rw [nrep_mul_phi_self hct F hext hw₀ hsq]
      simp [Subgroup.one_mem]) hpanel

end CFSG.ClassicalInvolution.Phan.PhanE
