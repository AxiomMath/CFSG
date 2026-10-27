module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

open Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem orthDerived_le_orthogonalGroup (Q : QuadraticForm K V) :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

theorem mem_supportedBlock_of_orthDerived {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q)
    (hc : g * x = x * g) {h : K[X]} (hfix : ∀ v ∈ othersSpace x.toLinearMap h, g v = v) :
    g ∈ supportedBlock Q x h := by
  refine mem_supportedBlock.mpr
    ⟨mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩, hfix⟩
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup Q hg) v
  · simpa using congrArg (fun f : V ≃ₗ[K] V => f v) hc

theorem fixes_othersSpace_of_supported (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {U₁ U₂ : Submodule K V}
    (h₁ : U₁ ≤ orbitSpace x.toLinearMap h) (h₂ : U₂ ≤ orbitSpace x.toLinearMap h)
    {w : V ≃ₗ[K] V}
    (hw : ∀ v : V, (∀ u ∈ U₁, QuadraticMap.polar Q u v = 0) →
      (∀ u ∈ U₂, QuadraticMap.polar Q u v = 0) → w v = v) :
    ∀ v ∈ othersSpace x.toLinearMap h, w v = v := by
  intro v hv
  exact hw v (fun u hu => hx.polar_orbit_others hh (h₁ hu) hv)
    (fun u hu => hx.polar_orbit_others hh (h₂ hu) hv)

theorem commute_of_eq_pow_on_orbitSpace (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {z j : V ≃ₗ[K] V} (hz : z * x = x * z) {n : ℕ}
    (hzn : ∀ u ∈ orbitSpace x.toLinearMap h, z u = (x ^ n) u)
    (hj : j ∈ supportedBlock Q x h) : z * j = j * z := by
  have hjc : j ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hj).1).2
  have hzc : z ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    (mem_centralizer_iff x).mpr (fun v => congrArg (fun f : V ≃ₗ[K] V => f v) hz)
  have hfixj : ∀ r ∈ othersSpace x.toLinearMap h, j r = r := (mem_supportedBlock.mp hj).2
  have hjx : ∀ v, j ((x ^ n) v) = (x ^ n) (j v) := by
    have hcomm : Commute j x := Subgroup.mem_centralizer_singleton_iff.mp hjc
    intro v
    exact congrArg (fun f : V ≃ₗ[K] V => f v) (hcomm.pow_right n).eq
  ext v
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
  have hju : j u ∈ orbitSpace x.toLinearMap h := mem_orbitSpace_of_apply hjc hu
  have hzr : z r ∈ othersSpace x.toLinearMap h := mem_othersSpace_of_apply hzc hr
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hfixj r hr, hzn (j u) hju, hzn u hu, hjx u, hfixj (z r) hzr]

end OrthTorus

end CFSG.StandardType

end
