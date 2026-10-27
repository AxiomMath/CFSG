module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Recognition.F4Rigidity
import CFSG.Geometry.GeneralizedPolygons.Geodesic

public section

namespace CFSG.Quasithin.Stroth

open SimpleGraph

universe u

variable {V : Type u} {Γ : SimpleGraph V}

theorem three_le_encard_of_isThick [Fintype V] [DecidableRel Γ.Adj]
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (v : V) :
    3 ≤ (Γ.neighborSet v).encard := by
  simpa using hT v

private theorem isCycle_periodic {a : V} {w : Γ.Walk a a} (hw : w.IsCycle) :
    (∀ i, Γ.Adj (w.getVert (i % w.length)) (w.getVert ((i + 1) % w.length))) ∧
      (∀ i, w.getVert (i % w.length) ≠ w.getVert ((i + 2) % w.length)) ∧
      (∀ i, w.getVert ((i + w.length) % w.length) = w.getVert (i % w.length)) := by
  have h3 : 3 ≤ w.length := hw.isCircuit.three_le_length
  have hpos : 0 < w.length := by omega
  have h1 : 1 < w.length := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hr : i % w.length < w.length := Nat.mod_lt _ hpos
    have e : (i + 1) % w.length = (i % w.length + 1) % w.length := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt h1]
    by_cases hlt : i % w.length + 1 < w.length
    · rw [e, Nat.mod_eq_of_lt hlt]
      exact w.adj_getVert_succ hr
    · have hlast : i % w.length = w.length - 1 := by omega
      have e0 : (i % w.length + 1) % w.length = 0 := by
        rw [show i % w.length + 1 = w.length by omega, Nat.mod_self]
      rw [e, e0, hlast]
      have h0 : w.getVert 0 = w.getVert w.length := by
        rw [Walk.getVert_zero, Walk.getVert_length]
      rw [h0]
      have h := w.adj_getVert_succ (i := w.length - 1) (by omega)
      rwa [show w.length - 1 + 1 = w.length by omega] at h
  · intro i h
    have hne : i % w.length ≠ (i + 2) % w.length := by
      intro him
      have hdvd : w.length ∣ 2 := by
        have := Nat.ModEq.dvd' him
        simpa using this
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hr : i % w.length ≤ w.length - 1 := by
      have := Nat.mod_lt i hpos
      omega
    have hs : (i + 2) % w.length ≤ w.length - 1 := by
      have := Nat.mod_lt (i + 2) hpos
      omega
    exact hne (hw.getVert_injOn' hr hs h)
  · intro i
    rw [Nat.add_mod_right]

private theorem exists_isPolygon_of_girth {m : ℕ} {c : V → Bool}
    (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) (hm : 2 ≤ m)
    (hU : CFSG.Quasithin.UniqueGeod Γ m) (hg : Γ.girth = 2 * m) :
    ∃ S : Set V, CFSG.Quasithin.IsPolygon Γ S (2 * m) := by
  have hnac : ¬ Γ.IsAcyclic := by
    intro h
    rw [SimpleGraph.girth_eq_zero.mpr h] at hg
    omega
  obtain ⟨a, w, hw, hwl⟩ := SimpleGraph.exists_girth_eq_length.mpr hnac
  have hlen : w.length = 2 * m := by rw [← hwl]; exact hg
  obtain ⟨hzadj, hznb, hzper⟩ := isCycle_periodic hw
  have hzper' : ∀ i, w.getVert ((i + 2 * m) % w.length) = w.getVert (i % w.length) := by
    intro i
    rw [← hlen]
    exact hzper i
  exact ⟨Set.range fun i => w.getVert (i % w.length),
    CFSG.Quasithin.GPath.isPolygon_of_periodic hΓ hc hm hU
      (fun i => w.getVert (i % w.length)) hzadj hznb hzper'⟩

theorem isGenPolygon_of_isGeneralizedPolygon [Fintype V] [DecidableRel Γ.Adj] {m : ℕ}
    (hm : 2 ≤ m) (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ m)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) : CFSG.Quasithin.IsGenPolygon Γ m := by
  haveI : Nonempty V := hP.connected.nonempty
  obtain ⟨c⟩ := hP.isBipartite
  let c' : Γ.Coloring Bool := Γ.recolorOfEquiv finTwoEquiv c
  have hcb : ∀ a b, Γ.Adj a b → c' a ≠ c' b := fun _ _ h => c'.valid h
  have hU : CFSG.Quasithin.UniqueGeod Γ m := hP.uniqueGeod
  refine ⟨hP.connected, ⟨fun v => c' v, hcb⟩, ?_, ?_, hU, ?_, ?_⟩
  · exact fun u v => hP.dist_le (by omega) u v
  · obtain ⟨u, v, huv⟩ := exists_dist_eq_diam (G := Γ)
    exact ⟨u, v, by rw [huv, hP.diam_eq]⟩
  · exact exists_isPolygon_of_girth hP.connected hcb hm hU hP.girth_eq
  · intro v
    have h := three_le_encard_of_isThick hT v
    have h2 : (2 : ℕ∞) ≤ 3 := by norm_num
    exact le_trans h2 h

theorem isGeneralizedPolygon_of_isGenPolygon {m : ℕ} (hm : 2 ≤ m)
    (hP : CFSG.Quasithin.IsGenPolygon Γ m) :
    CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ m := by
  obtain ⟨c, hc⟩ := hP.bipartite
  obtain ⟨S, ⟨φ⟩⟩ := hP.polygon
  have hcont : SimpleGraph.cycleGraph (2 * m) ⊑ Γ :=
    φ.isContained.trans (SimpleGraph.Copy.induce Γ S).isContained
  obtain ⟨a, w, hw, hwl⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega)).mp hcont
  have hge : Γ.girth ≤ 2 * m := by
    have := hw.girth_le_length
    omega
  have hac : ¬ Γ.IsAcyclic := fun h => h w hw
  have hgtop : Γ.egirth ≠ ⊤ := fun h => hac (SimpleGraph.egirth_eq_top.mp h)
  have hlow : ((2 * m : ℕ) : ℕ∞) ≤ Γ.egirth := by
    rw [SimpleGraph.le_egirth]
    intro b p hp
    obtain ⟨hpadj, hpnb, hpper⟩ := isCycle_periodic hp
    have h3 : 3 ≤ p.length := hp.isCircuit.three_le_length
    have hpos : 0 < p.length := by omega
    have h : 2 * m ≤ p.length :=
      CFSG.Quasithin.GPath.two_mul_le_of_periodic hP.connected hc hP.uniqueGeod
        (fun i => p.getVert (i % p.length)) hpadj hpnb hpos hpper
    exact ENat.natCast_le_natCast.mpr h
  have hglow : 2 * m ≤ Γ.girth := by
    have := ENat.toNat_le_toNat hlow hgtop
    simpa [SimpleGraph.girth] using this
  have he : Γ.ediam ≤ (m : ℕ∞) := by
    refine SimpleGraph.ediam_le_of_edist_le fun u v => ?_
    have hde : (Γ.dist u v : ℕ∞) = Γ.edist u v := (hP.connected u v).coe_dist_eq_edist
    rw [← hde]
    exact ENat.natCast_le_natCast.mpr (hP.diam_le u v)
  have hmle : (m : ℕ∞) ≤ Γ.ediam := by
    obtain ⟨u, v, huv⟩ := hP.diam_eq
    calc (m : ℕ∞) = (Γ.dist u v : ℕ∞) := by rw [huv]
      _ ≤ Γ.edist u v := SimpleGraph.natCast_dist_le_edist
      _ ≤ Γ.ediam := SimpleGraph.edist_le_ediam
  have hdiam : Γ.diam = m := by
    rw [SimpleGraph.diam, le_antisymm he hmle, ENat.toNat_natCast]
  refine ⟨hP.connected, ?_, hdiam, le_antisymm hge hglow⟩
  exact ⟨Γ.recolorOfEquiv finTwoEquiv.symm
    (SimpleGraph.Coloring.mk c (fun {x y} h => hc x y h))⟩

end CFSG.Quasithin.Stroth
