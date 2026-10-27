module

public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LieType.Chevalley.ExactNormalFormE
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6NormalForm
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6NormalFix
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Regular
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6EpsZero
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6EpsOne
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Count
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Cube
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

namespace KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

theorem eq_one_of_commute_famKernel_E6
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ)
    {F : Set (Fin Tag.E6.rank → Kˣ)} (hF : ∀ a ∈ F, ∀ i, a i ^ p = 1)
    (hne : (famKernel F).Nonempty) (hcyc : p = 3 → ∃ z ∈ F, famKernel F = famKernel {z})
    (hrank : p ≠ 3 → Set.ncard {b : Fin Tag.E6.rank → Kˣ | (∀ i, b i ^ p = 1) ∧
      ∀ β ∈ famKernel F, rootChar b β = 1} ≤ p)
    {α : MulAut (adjointGroup .E6 K)} (h2 : ∃ k : ℕ, α ^ 2 ^ k = 1)
    (hαF : ∀ a ∈ F, α * rootDiagAutHom .E6 K a = rootDiagAutHom .E6 K a * α)
    (hfix : ∀ β ∈ famKernel F, ∀ x : adjointGroup .E6 K,
      (x : ModGL .E6 K) ∈ rootSubgroup .E6 K β → α x = x) :
    α = 1 := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨F', hFF', hF'p, hF'0, hαF'⟩ :=
    exists_family_famKernel_eq_empty_E6 hp hp2 hpK hF hαF hfix
  obtain ⟨h, w, a, σ, ε, hh, hα, hw⟩ := exists_normalForm_mul_canonicalRep_E6 hf hK hF'0 hαF'
  obtain ⟨rfl, hθ⟩ := normalForm_fix_famKernel_E6 hne hh hα hfix
  rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega) with hε | hε
  · rw [hε] at hα hw
    exact eq_one_of_normalForm_zero_E6 hK4 hp hp2 hF'p hF'0 h2 hh hα hw
  · rw [hε] at hα hw hθ
    obtain ⟨hθθ, hχ⟩ := theta_involutive_of_normalForm_one_E6 hK4 hp hp2 hF'p hF'0 h2 hh hα hw
    exfalso
    by_cases hp3 : p = 3
    · obtain ⟨z, hzF, hzK⟩ := hcyc hp3
      refine false_of_cube_of_fix_wRho_E6 (fun i => ?_) hθθ (hχ z (hFF' hzF)) fun β hβ => ?_
      · rw [← hp3]
        exact hF z hzF i
      · exact hθ β (by rw [hzK]; exact hβ)
    · exact false_of_ncard_le_of_fix_wRho_E6 hp hpK hθθ hθ (hrank hp3)

end KGCentE6

end CFSG.StandardType

end
