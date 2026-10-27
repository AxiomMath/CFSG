module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86OrbitTreeAct
public import CFSG.Quasithin.Recognition.GoldschmidtFan86OrbitTreeTree
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteDefs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

theorem orbitTree_tutte (hT : Tutte.TutteTree) {V G : Type} [Group G] [MulAction G V]
    {Γ : SimpleGraph V} (hΓ : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfin : ∀ v : V, Finite (MulAction.stabilizer G v)) {H : Subgroup G} {α : V}
    (hval : Nat.card (Γ.neighborSet α) = 3) (hloc : OrbitLoc Γ H (MulAction.orbit ↥H α))
    (hP : OrbitPartner Γ (MulAction.orbit ↥H α)) (hconn : OrbitConn Γ (MulAction.orbit ↥H α)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 5 ∧ ∀ (Q : Arc (orbitGraph Γ (MulAction.orbit ↥H α)) k) (h : ↥H),
      (∀ i, i ≤ k → h • Q.vert i = Q.vert i) →
        ∀ w : ↥(MulAction.orbit ↥H α), h • w = w :=
  hT ↥(MulAction.orbit ↥H α) (orbitGraph Γ (MulAction.orbit ↥H α))
    (orbitGraph_isTree hΓ hP hconn ⟨α, MulAction.mem_orbit_self α⟩)
    (fun w => (card_neighborSet_orbitGraph hΓ hP w).trans (card_neighborSet_orbit hadj hval w))
    ↥H (orbitGraph_adj_smul hadj) orbit_transitive (orbit_finite_stabilizer hfin)
    (orbitGraph_loc hadj hloc hP)

theorem orbitTree_fixes (hT : Tutte.TutteTree) {V G : Type} [Group G] [MulAction G V]
    {Γ : SimpleGraph V} (hΓ : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfin : ∀ v : V, Finite (MulAction.stabilizer G v)) {H : Subgroup G} {α : V}
    (hval : Nat.card (Γ.neighborSet α) = 3) (hloc : OrbitLoc Γ H (MulAction.orbit ↥H α))
    (hP : OrbitPartner Γ (MulAction.orbit ↥H α)) (hconn : OrbitConn Γ (MulAction.orbit ↥H α)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 5 ∧ ∀ P : Arc Γ (2 * k),
      (∀ i, i ≤ k → P.vert (2 * i) ∈ MulAction.orbit ↥H α) →
      ∀ g ∈ H, (∀ i, i ≤ k → g • P.vert (2 * i) = P.vert (2 * i)) →
        ∀ u ∈ MulAction.orbit ↥H α, g • u = u := by
  obtain ⟨k, hk1, hk5, hfix⟩ := orbitTree_tutte hT hΓ hadj hfin hval hloc hP hconn
  refine ⟨k, hk1, hk5, fun P hmem g hg hgP u hu => ?_⟩
  have h := hfix (Arc.toOrbit hΓ P hmem) ⟨g, hg⟩ (fun i hi => Subtype.ext (by
    show g • ((Arc.toOrbit hΓ P hmem).vert i).1 = ((Arc.toOrbit hΓ P hmem).vert i).1
    rw [Arc.toOrbit_vert hΓ P hmem hi]
    exact hgP i hi)) ⟨u, hu⟩
  exact congrArg Subtype.val h

end CFSG.Quasithin.Fan86
