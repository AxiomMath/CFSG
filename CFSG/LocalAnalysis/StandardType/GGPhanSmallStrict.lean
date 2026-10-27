module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNbrWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import CFSG.LocalAnalysis.StandardType.GGWeylCasePrime
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggAutomizer_le_stabilizer_of_centralizes {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hx : x ∈ Bs) (hL : L ≤ Subgroup.centralizer ({x} : Set G)) :
    ggAutomizer L Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro φ ⟨g, hgL, -, hg⟩
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  have hc : x * g = g * x := Subgroup.mem_centralizer_iff.mp (hL hgL) x (Set.mem_singleton x)
  have h : φ ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext (by
    rw [hg]
    show g * x * g⁻¹ = x
    rw [← hc]
    group)
  exact h

theorem ggPhanSmall_card_lt_join (hW : GGNbrInnerWeylInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    Nat.card ↥(ggAutomizer L Bs) < Nat.card ↥(ggAutomizerJoin L Bs 𝒦) := by
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hS : LargeEvenSStar p B x L := hconf.1.2.2.2.2.2.2.1
  have hx : x ∈ Bs := hconf.2.1.1 hS.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨y, K, hN⟩ := exists_ggNbr hconf.1.2.2.2.2.2.2.2 hconf.2.2
  obtain ⟨φ, hφK, hφx⟩ :=
    FrameRoute.exists_automizer_moves_x_of_innerWeyl hW hconf hcfg.1.2.2.1 hN hx
  have hrefl : GGReflGenerated p (ggAutomizer K Bs) := hcfg.2.1 y K hN
  have hWey : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    hcfg.1.2.2.2.2.1 y K hN hrefl (Or.inr hcfg.2.1)
  have hjoin : ggAutomizerJoin L Bs {K} = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    simp [ggAutomizerJoin]
  have hmax : Nat.card ↥(ggAutomizerJoin L Bs {K}) ≤ Nat.card ↥(ggAutomizerJoin L Bs 𝒦) :=
    hcfg.2.2.2.2.2 {K} (ggNbrSet_singleton hN) (by rw [hjoin]; exact hWey)
  have hlt : ggAutomizer L Bs < ggAutomizerJoin L Bs {K} := by
    rw [hjoin]
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hmem : φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := Subgroup.mem_sup_right hφK
    rw [← h] at hmem
    exact hφx (MulAction.mem_stabilizer_iff.mp
      (ggAutomizer_le_stabilizer_of_centralizes hx hxL hmem))
  haveI : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun φ : MulAut ↥Bs => (φ : ↥Bs → ↥Bs)) DFunLike.coe_injective
  exact lt_of_lt_of_le (Subgroup.card_lt_of_lt hlt) hmax

end CFSG.StandardType

end
