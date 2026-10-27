module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Smith81.TiFusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Main

variable [Finite G] {M Q Z B X : Subgroup G} {x : G}

theorem exists_conj_of_inZClass (H : StrothHyp M Q Z) {u v : G} (hu : InZClass Z u)
    (hv : InZClass Z v) : ∃ g : G, g * u * g⁻¹ = v := by
  obtain ⟨a, z₁, hz₁, hz₁1, rfl⟩ := hu
  obtain ⟨b, z₂, hz₂, hz₂1, rfl⟩ := hv
  obtain ⟨m, -, hm⟩ := Z_isConj H hz₁ hz₁1 hz₂ hz₂1
  refine ⟨b * m * a⁻¹, ?_⟩
  calc b * m * a⁻¹ * (a * z₁ * a⁻¹) * (b * m * a⁻¹)⁻¹ = b * (m * z₁ * m⁻¹) * b⁻¹ := by group
    _ = b * z₂ * b⁻¹ := by rw [hm]

end Main

end CFSG.RankThree.GF2n.Smith81
