module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecD557NatA
public import CFSG.Quasithin.Vol2.Ch11StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isSL3_four (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hSL3 : KindSL3 L (fsuV T I) n)
    (hn : n = 2) : IsSL3 4 (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨_, -, -, ⟨eL⟩, -⟩ := h1102 G T L I n h
  obtain ⟨F, _, _, hF, ⟨eS⟩⟩ := hSL3
  exact ⟨F, inferInstance, inferInstance, by rw [hF, hn]; norm_num,
    ⟨eL.trans (eS.trans (statedSLEquiv' 3 F).symm)⟩⟩

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ z ∈ U ⊓ Subgroup.centralizer (U : Set G),
      g * z * g⁻¹ ∈ U ⊓ Subgroup.centralizer (U : Set G) := by
    intro g hg z hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
    show g * z * g⁻¹ ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : g⁻¹ * u * g ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) u).mp hu
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hu'
    calc u * (g * z * g⁻¹) = g * ((g⁻¹ * u * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * u := by group
  intro z
  constructor
  · exact key g hg z
  · intro hz
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hz
    simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch11.SecD
