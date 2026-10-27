module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeHL
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeOrbit
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseII
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2_caseII_orbit {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p = 3)
    (hLN : GGLNoncyclicInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) (hII : M.toLin.CaseII) : GGQ2Orbit p B Bs x D J := by
  have hxD : x ∈ D := hS.1.1.2.2.1.2.2.2.1
  have hxne : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hune : (⟨x, M.hx⟩ : ↥Bs) ≠ 1 := fun h => hxne (Subtype.ext_iff.mp h)
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hcard : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) M.V := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
      _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
      _ = p ^ Module.finrank (ZMod p) M.V :=
        (FiniteField.pow_finrank_eq_natCard p M.V).symm
  have h4 : 4 ≤ Fintype.card M.toLin.ι := by
    rw [hII.1]
    have hp4 : p ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    have hp1 : 1 < p := (hS.1.1.tableB_facts).1.one_lt
    rw [hcard] at hp4
    exact (Nat.pow_le_pow_iff_right hp1).mp hp4
  have hx := (ggQ2_fixed_lin M).1
  have hW := ggQ2_weyl_le_lin M
  have hTF : TransvectionFree M.linGroup := ggQ2_transvectionFree M hS.1.2.2.2.1
  have hHL := ggQ2_HL_lin (ggLineStabNormalizesInput_of_noncyclic hLN) hS M
  have hA := ggQ2_caseII_lin hp M.toLin hII h4 M.xV hx M.linGroup hW hTF hHL
  have hp2 : p ≠ 2 := by rw [hp]; decide
  refine Or.inl ⟨⟨x, M.hx⟩, hxD, hune, ?_⟩
  exact (ggQ2_orbit_iff M hp2 ⟨x, M.hx⟩).mpr hA

end CFSG.StandardType

end
