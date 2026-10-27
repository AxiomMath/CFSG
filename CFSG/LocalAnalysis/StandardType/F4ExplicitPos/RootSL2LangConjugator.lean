module

public import CFSG.LieType.AlgebraicGroups.SL2LangConjugator
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairDescentPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientActionPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeFrobeniusError

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint


local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem exists_finite_conjugator_of_rootSL2_error
    {K Ω : Type} [Field K] [Finite K] [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    [Algebra K Ω] (f : ℕ) (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (β : Fin Tag.F4.rank → ℤ) (hβ : IsRoot .F4 β)
    (H : Subgroup (ModGL .F4 Ω)) (a : ModGL .F4 Ω)
    (ha : a ∈ adjointGroup .F4 Ω)
    (herror : a⁻¹ * Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) a ∈
      (rootSL2 .F4 Ω β).range)
    (hcentralizer : (rootSL2 .F4 Ω β).range ≤ Subgroup.centralizer (H : Set (ModGL .F4 Ω))) :
    ∃ u : adjointGroup .F4 K, ∀ g ∈ H,
      ((AmbientAction.jF4 (K := K) (L := Ω) u : adjointGroup .F4 Ω) : ModGL .F4 Ω) * g *
        ((AmbientAction.jF4 (K := K) (L := Ω) u : adjointGroup .F4 Ω) : ModGL .F4 Ω)⁻¹ =
          a * g * a⁻¹ := by
  let F : ModGL .F4 Ω →* ModGL .F4 Ω :=
    Units.map (entrywiseHom (iterateFrobenius Ω 2 f))
  have hρF (Y : Matrix.SpecialLinearGroup (Fin 2) Ω) :
      F (rootSL2 .F4 Ω β Y) =
        rootSL2 .F4 Ω β (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) Y) :=
    entrywiseFrobGL_rootSL2 2 f hβ Y
  obtain ⟨b, hbF, hbH, Y, hbY⟩ :=
    exists_fixed_conjugator_of_sl2_centralizer 2 f hf F (rootSL2 .F4 Ω β) hρF
      H hcentralizer a herror
  have hbA : b ∈ adjointGroup .F4 Ω := by
    rw [hbY]
    exact mul_mem ha (inv_mem ((exceptional_Lang_root_rank_one_data .F4 Ω β).2.2.2.2.1 Y))
  have hbmap := AmbientPairDescent.f4_fixed_frobenius_mem_map (K := K) (Ω := Ω)
    f hcard hbA hbF
  obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hbmap
  refine ⟨⟨u, hu⟩, ?_⟩
  intro g hg
  change BaseChange.bcGL (algebraMap K Ω) u * g *
    (BaseChange.bcGL (algebraMap K Ω) u)⁻¹ = a * g * a⁻¹
  rw [hueq]
  exact hbH g hg

end CFSG.StandardType.F4ExplicitPos
