module

public import CFSG.Sporadic.Co1Patterson.Defs
public import CFSG.LargeExtraspecial.BridgeNat

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Open CFSG.Monster.GMS

variable {X : Type} [Group X]

theorem map_centralizer_singleton (e : X ≃* X) (x : X) :
    (centralizer ({x} : Set X)).map e.toMonoidHom = centralizer ({e x} : Set X) := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa using this
  · intro h
    have := congrArg e.symm h
    simpa using this

theorem qOf_map (e : X ≃* X) (x : X) : (qOf x).map e.toMonoidHom = qOf (e x) := by
  have hC := map_centralizer_singleton e x
  let e' : centralizer ({x} : Set X) ≃* centralizer ({e x} : Set X) :=
    (e.subgroupMap (centralizer ({x} : Set X))).trans (MulEquiv.subgroupCongr hC)
  have hF := CFSG.LargeExtraspecial.Bridge.timmesfeldFStar_map e'
  unfold qOf
  rw [← hF, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_qOf_conj (g x y : X) : y ∈ qOf (g * x * g⁻¹) ↔ g⁻¹ * y * g ∈ qOf x := by
  have h := qOf_map (MulAut.conj g) x
  rw [MulAut.conj_apply] at h
  rw [← h, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

@[expose] def a2Graph (t : X) : SimpleGraph (ConjVert t) where
  Adj x y := x ≠ y ∧ (x : X) * y = y * x ∧ IsConj t ((x : X) * y) ∧
    (y : X) ∉ qOf (x : X) ∧ (x : X) ∉ qOf (y : X)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.1 ▸ h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem a2Graph_adj_smul {t : X} (g : X) {x y : ConjVert t} (h : (a2Graph t).Adj x y) :
    (a2Graph t).Adj (g • x) (g • y) := by
  obtain ⟨hne, hc, hconj, hy, hx⟩ := h
  refine ⟨fun e => hne (smul_left_cancel g e), ?_, ?_, ?_, ?_⟩
  · simp only [coe_smul_conjVert]
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * ((x : X) * y) * g⁻¹ := by group
      _ = g * ((y : X) * x) * g⁻¹ := by rw [hc]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  · have e : (g * x * g⁻¹) * (g * y * g⁻¹) = g * ((x : X) * y) * g⁻¹ := by group
    simp only [coe_smul_conjVert, e]
    exact isConj_conj hconj g
  · simp only [coe_smul_conjVert, mem_qOf_conj]
    simpa [mul_assoc] using hy
  · simp only [coe_smul_conjVert, mem_qOf_conj]
    simpa [mul_assoc] using hx

theorem a2Graph_adj_smul_iff {t : X} (g : X) {x y : ConjVert t} :
    (a2Graph t).Adj (g • x) (g • y) ↔ (a2Graph t).Adj x y := by
  refine ⟨fun h => ?_, a2Graph_adj_smul g⟩
  simpa using a2Graph_adj_smul g⁻¹ h

@[expose] def conjIso {t : X} (g : X) : a2Graph t ≃g a2Graph t where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := a2Graph_adj_smul_iff g

theorem conjIso_apply {t : X} (g : X) (x : ConjVert t) : conjIso g x = g • x := rfl

theorem hom_dist_le {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    {u v : V} (h : G.Reachable u v) : H.dist (f u) (f v) ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  calc H.dist (f u) (f v) ≤ (p.map f).length := SimpleGraph.dist_le _
    _ = G.dist u v := by rw [SimpleGraph.Walk.length_map, hp]

theorem iso_dist_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (u v : V) : H.dist (φ u) (φ v) = G.dist u v := by
  by_cases h : G.Reachable u v
  · refine le_antisymm (hom_dist_le φ.toHom h) ?_
    have h' : H.Reachable (φ u) (φ v) := SimpleGraph.Iso.reachable_iff.2 h
    simpa using hom_dist_le φ.symm.toHom h'
  · have h' : ¬ H.Reachable (φ u) (φ v) := fun h' => h (SimpleGraph.Iso.reachable_iff.1 h')
    rw [SimpleGraph.dist_eq_zero_of_not_reachable h, SimpleGraph.dist_eq_zero_of_not_reachable h']

end CFSG.Sporadic.Co1Patterson
