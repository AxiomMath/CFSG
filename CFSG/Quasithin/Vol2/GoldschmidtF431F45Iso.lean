module

public import CFSG.Quasithin.Recognition.F4Basic

public section

namespace CFSG.Quasithin.H13.F431.F45

open CFSG.Quasithin

universe u v

section Iso

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}

theorem edist_map_le (f : G →g H) (a b : V) : H.edist (f a) (f b) ≤ G.edist a b := by
  by_cases h : G.edist a b = ⊤
  · rw [h]
    exact le_top
  · obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    have h1 := SimpleGraph.edist_le (w.map f)
    rw [SimpleGraph.Walk.length_map, hw] at h1
    exact h1

theorem iso_edist (φ : G ≃g H) (a b : V) : H.edist (φ a) (φ b) = G.edist a b := by
  refine le_antisymm (edist_map_le φ.toHom a b) ?_
  have := edist_map_le φ.symm.toHom (φ a) (φ b)
  simpa using this

theorem iso_dist (φ : G ≃g H) (a b : V) : H.dist (φ a) (φ b) = G.dist a b := by
  unfold SimpleGraph.dist
  rw [iso_edist]

theorem neighborSet_iso (φ : G ≃g H) (v : V) :
    H.neighborSet (φ v) = φ '' G.neighborSet v := by
  ext w
  constructor
  · intro hw
    refine ⟨φ.symm w, ?_, by simp⟩
    have : H.Adj (φ v) (φ (φ.symm w)) := by simpa using hw
    exact φ.map_adj_iff.mp this
  · rintro ⟨a, ha, rfl⟩
    exact φ.map_adj_iff.mpr ha

theorem _root_.CFSG.Quasithin.IsGenPolygon.of_iso {m : ℕ} (φ : G ≃g H) (h : IsGenPolygon H m) :
    IsGenPolygon G m where
  connected := φ.connected_iff.mpr h.connected
  bipartite := by
    obtain ⟨c, hc⟩ := h.bipartite
    exact ⟨fun a => c (φ a), fun a b hab => hc _ _ (φ.map_adj_iff.mpr hab)⟩
  diam_le u v := by
    rw [← iso_dist φ]
    exact h.diam_le _ _
  diam_eq := by
    obtain ⟨a, b, hab⟩ := h.diam_eq
    refine ⟨φ.symm a, φ.symm b, ?_⟩
    rw [← iso_dist φ]
    simpa using hab
  uniqueGeod := by
    intro n p q hp hq h0 hn hlt
    have hmap : ∀ a b : V, G.Adj a b → H.Adj (φ a) (φ b) := fun a b hab => φ.map_adj_iff.mpr hab
    have hgeo : ∀ r : GPath G n, r.IsGeodesic → (r.map φ hmap).IsGeodesic := by
      intro r hr
      show H.dist (r.map φ hmap 0) (r.map φ hmap n) = n
      simp only [GPath.map_apply]
      rw [iso_dist]
      exact hr
    have h := h.uniqueGeod n (p.map φ hmap) (q.map φ hmap) (hgeo p hp) (hgeo q hq)
      (by simp [h0]) (by simp [hn]) hlt
    refine GPath.ext' fun i hi => ?_
    have := congrArg (fun r : GPath H n => r i) h
    simp only [GPath.map_apply] at this
    exact φ.injective this
  polygon := by
    obtain ⟨S, hS⟩ := h.polygon
    refine ⟨φ ⁻¹' S, ?_⟩
    obtain ⟨ψ⟩ := hS
    let χ : (G.induce (φ ⁻¹' S)) ≃g (H.induce S) :=
      { toEquiv := φ.toEquiv.subtypeEquiv (fun a => Iff.rfl)
        map_rel_iff' := fun {a b} => by
          simp [φ.map_adj_iff] }
    exact ⟨χ.symm.comp ψ⟩
  valence v := by
    have := h.valence (φ v)
    rw [neighborSet_iso, φ.injective.encard_image] at this
    exact this

end Iso

end CFSG.Quasithin.H13.F431.F45
