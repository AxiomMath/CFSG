module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem exists_isometry_of_mem_XbarPre (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    {s : G} (hs : s ∈ XbarPre M Q Z B) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π (s * x * s⁻¹) = T (M₀.π x)) ∧
      (∀ e, M₀.Qf (T e) = M₀.Qf e) ∧
      (∀ e f, M₀.B (T e) (T f) = M₀.B e f) := by
  have hH0 : s ∈ H0 M Z := XbarPre_le_H0 hc hs
  obtain ⟨hsM, hscen⟩ := Subgroup.mem_inf.mp hH0
  have hcen : ∀ z ∈ Z, s * z * s⁻¹ = z := by
    intro z hz
    have h := Subgroup.mem_centralizer_iff.mp hscen z hz
    rw [← h]
    group
  obtain ⟨T, hT1, hT2, hT3⟩ := hD.linear_of_centralizes hsM hcen
  exact ⟨T, hT1, hT2, hT3⟩

end CFSG.RankThree.GF2n.Stroth80
