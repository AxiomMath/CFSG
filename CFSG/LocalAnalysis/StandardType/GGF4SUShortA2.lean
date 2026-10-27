module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6SU6
public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Model

public noncomputable section

namespace CFSG.StandardType.F4KGPosition

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem exists_linearBlockStandardPair_SU_short_nodes_map
    {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c)
    {G : Type} [Group G] (ψ : ↥(SU σ 6) →* G) (hψ : ψ.ker ≤ Subgroup.center _) :
    ∃ W : Subgroup G, LinearBlockStandardPair E W
      ((RouteD.nodeSU hσ 0).map ψ) ((RouteD.nodeSU hσ 1).map ψ) := by
  let φ := ψ.comp (RouteD.iota3 hσ)
  have hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) E) := by
    intro a ha
    have ha' : RouteD.iota3 hσ a ∈ ψ.ker := ha
    have hc := hψ ha'
    rw [Subgroup.mem_center_iff]
    intro b
    apply RouteD.iota3_injective hσ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hc (RouteD.iota3 hσ b)
  have h0 : (B12 E).map (RouteD.iota3 hσ) = RouteD.nodeSU hσ 0 :=
    le_antisymm (RouteD.iota3_B12_le hσ) (RouteD.iota3_B12_ge hσ)
  have h1 : (B23 E).map (RouteD.iota3 hσ) = RouteD.nodeSU hσ 1 :=
    le_antisymm (RouteD.iota3_B23_le hσ) (RouteD.iota3_B23_ge hσ)
  have h0' : (B12 E).map φ = (RouteD.nodeSU hσ 0).map ψ := by
    rw [show φ = ψ.comp (RouteD.iota3 hσ) from rfl, ← Subgroup.map_map, h0]
  have h1' : (B23 E).map φ = (RouteD.nodeSU hσ 1).map ψ := by
    rw [show φ = ψ.comp (RouteD.iota3 hσ) from rfl, ← Subgroup.map_map, h1]
  exact ⟨φ.range, Models.linearBlockStandardPair_of_normalized hker rfl h0' h1'⟩

theorem exists_linearBlockStandardPair_rootLevi_PSU6
    {E : Type} [Field E] [Finite E] [CharP E 2] {f : ℕ}
    (hE : Nat.card E = (2 ^ f) ^ 2) {G : Type} [Group G]
    (ψ : ↥(SU (unitaryInvolution E 2 f) 6) →* G) (hψ : ψ.ker ≤ Subgroup.center _) :
    ∃ W : Subgroup G, LinearBlockStandardPair E W
      ((ggRootLevi (rootDatum hE 6) (Pi.single (0 : Fin 3) 1)).map ψ)
      ((ggRootLevi (rootDatum hE 6) (Pi.single (1 : Fin 3) 1)).map ψ) := by
  exact exists_linearBlockStandardPair_SU_short_nodes_map (unitaryInvolution_involutive hE) ψ hψ

end CFSG.StandardType.F4KGPosition
