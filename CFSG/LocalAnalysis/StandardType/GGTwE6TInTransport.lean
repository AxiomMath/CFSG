module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Classical2 CFSG.Open

theorem isToralE6_map_baseChange_of_algebraicClosure {f : ℕ} (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (A : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    (h : ∃ g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f))),
      ∀ x ∈ A, g⁻¹ * baseChangeGL (algebraMap (GaloisField 2 (2 * f))
        (AlgebraicClosure (GaloisField 2 (2 * f)))) x * g ∈
          torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 2 (2 * f)))) :
    IsToralE6 Ω (A.map (baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω))) := by
  let K := GaloisField 2 (2 * f)
  let Kb := AlgebraicClosure K
  let e : Kb ≃ₐ[K] Ω := IsAlgClosure.equiv K Kb Ω
  let ε : Kb →+* Ω := e.toAlgHom.toRingHom
  have hε : ε.comp (algebraMap K Kb) = algebraMap K Ω := by
    ext c
    exact e.commutes c
  change IsToralE6 Ω (A.map (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)))
  obtain ⟨g, hg, hgt⟩ := h
  refine ⟨baseChangeGL (τ := TwistTag.E6.tag) ε g,
    baseChangeGL_mem_adjointGroup (τ := TwistTag.E6.tag) ε hg, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have htor := baseChangeGL_mem_torusGroup (τ := TwistTag.E6.tag) ε (hgt x hx)
  rw [map_mul, map_mul, map_inv] at htor
  rwa [baseChangeGL_baseChangeGL, hε] at htor

end CFSG.StandardType.NoOffTwE6Three
