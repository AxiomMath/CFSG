module

public import CFSG.Quasithin.MS93.Amalgam

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem treeGraph_connected : X.treeGraph.Connected := X.treeGraph_isTree.connected

theorem not_isMVtx_inr (q : X.Universal ⧸ X.ofB.range) : ¬ IsMVtx X (Sum.inr q) := by
  simp [IsMVtx]

theorem isMVtx_baseA : IsMVtx X (baseA X) := rfl

theorem not_isMVtx_baseB : ¬ IsMVtx X (baseB X) := not_isMVtx_inr X _

theorem isMVtx_smul (g : X.Universal) (δ : Vtx X) : IsMVtx X (g • δ) ↔ IsMVtx X δ := by
  rcases δ with q | q <;> rfl

theorem isMVtx_iff_of_adj {u w : Vtx X} (h : X.treeGraph.Adj u w) :
    IsMVtx X u ↔ ¬ IsMVtx X w := by
  rcases u with x | x <;> rcases w with y | y
  · simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel] at h
  · simp [IsMVtx]
  · simp [IsMVtx]
  · simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel] at h

private def smulHom (g : X.Universal) : X.treeGraph →g X.treeGraph where
  toFun := (g • ·)
  map_rel' h := (adj_smul X g _ _).2 h

private theorem dist_smul_le (g : X.Universal) (u w : Vtx X) :
    X.treeGraph.dist (g • u) (g • w) ≤ X.treeGraph.dist u w := by
  obtain ⟨p, hp⟩ := (treeGraph_connected X).exists_walk_length_eq_dist u w
  rw [← hp, ← Walk.length_map (smulHom X g) p]
  exact dist_le _

theorem dist_smul (g : X.Universal) (u w : Vtx X) :
    X.treeGraph.dist (g • u) (g • w) = X.treeGraph.dist u w := by
  refine le_antisymm (dist_smul_le X g u w) ?_
  have := dist_smul_le X g⁻¹ (g • u) (g • w)
  rwa [inv_smul_smul, inv_smul_smul] at this

private theorem even_length_iff {u w : Vtx X} (p : X.treeGraph.Walk u w) :
    Even p.length ↔ (IsMVtx X u ↔ IsMVtx X w) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons, Nat.even_add_one, ih, isMVtx_iff_of_adj X h]
    tauto

theorem even_dist_iff (u w : Vtx X) :
    Even (X.treeGraph.dist u w) ↔ (IsMVtx X u ↔ IsMVtx X w) := by
  obtain ⟨p, hp⟩ := (treeGraph_connected X).exists_walk_length_eq_dist u w
  rw [← hp]
  exact even_length_iff X p

theorem tdist_comm (u w : Vtx X) : X.treeGraph.dist u w = X.treeGraph.dist w u :=
  SimpleGraph.dist_comm

theorem dist_triangle (u x w : Vtx X) :
    X.treeGraph.dist u w ≤ X.treeGraph.dist u x + X.treeGraph.dist x w :=
  (treeGraph_connected X).dist_triangle

theorem dist_eq_one_of_adj {u w : Vtx X} (h : X.treeGraph.Adj u w) : X.treeGraph.dist u w = 1 :=
  dist_eq_one_iff_adj.mpr h

theorem dist_eq_zero_iff {u w : Vtx X} : X.treeGraph.dist u w = 0 ↔ u = w :=
  (treeGraph_connected X).dist_eq_zero_iff

theorem dist_eq_two_of_adj_adj {u x w : Vtx X} (hux : X.treeGraph.Adj u x)
    (hxw : X.treeGraph.Adj x w) (hne : u ≠ w) : X.treeGraph.dist u w = 2 := by
  have h1 := dist_triangle X u x w
  rw [dist_eq_one_of_adj X hux, dist_eq_one_of_adj X hxw] at h1
  have h2 : X.treeGraph.dist u w ≠ 0 := fun h => hne ((dist_eq_zero_iff X).mp h)
  have h3 : Even (X.treeGraph.dist u w) := by
    rw [even_dist_iff, isMVtx_iff_of_adj X hux, isMVtx_iff_of_adj X hxw]
    tauto
  have h4 : X.treeGraph.dist u w ≠ 1 := by
    rintro h
    rw [h] at h3
    exact Nat.not_even_one h3
  omega

theorem dist_adj_cases {x y : Vtx X} (h : X.treeGraph.Adj x y) (u : Vtx X) :
    X.treeGraph.dist u y = X.treeGraph.dist u x + 1 ∨
      X.treeGraph.dist u x = X.treeGraph.dist u y + 1 := by
  have h1 := dist_triangle X u x y
  have h2 := dist_triangle X u y x
  rw [dist_eq_one_of_adj X h] at h1
  rw [dist_eq_one_of_adj X h.symm] at h2
  have h3 : ¬ (Even (X.treeGraph.dist u x) ↔ Even (X.treeGraph.dist u y)) := by
    rw [even_dist_iff, even_dist_iff, isMVtx_iff_of_adj X h]
    tauto
  have h4 : X.treeGraph.dist u x ≠ X.treeGraph.dist u y := fun he => h3 (by rw [he])
  omega

private noncomputable def geoWalk (u w : Vtx X) : X.treeGraph.Walk u w :=
  ((treeGraph_connected X).exists_walk_length_eq_dist u w).choose

private theorem geoWalk_length (u w : Vtx X) :
    (geoWalk X u w).length = X.treeGraph.dist u w :=
  ((treeGraph_connected X).exists_walk_length_eq_dist u w).choose_spec

noncomputable def geo (u w : Vtx X) (i : ℕ) : Vtx X := (geoWalk X u w).getVert i

@[simp] theorem geo_zero (u w : Vtx X) : geo X u w 0 = u := Walk.getVert_zero _

theorem geo_of_le {u w : Vtx X} {i : ℕ} (h : X.treeGraph.dist u w ≤ i) : geo X u w i = w :=
  Walk.getVert_of_length_le _ (by rw [geoWalk_length]; exact h)

theorem geo_dist (u w : Vtx X) : geo X u w (X.treeGraph.dist u w) = w := geo_of_le X le_rfl

theorem adj_geo {u w : Vtx X} {i : ℕ} (h : i < X.treeGraph.dist u w) :
    X.treeGraph.Adj (geo X u w i) (geo X u w (i + 1)) :=
  Walk.adj_getVert_succ _ (by rw [geoWalk_length]; exact h)

theorem adj_geo_one {u w : Vtx X} (h : 0 < X.treeGraph.dist u w) :
    X.treeGraph.Adj u (geo X u w 1) := by
  simpa using adj_geo X h

private theorem dist_geo_le (u w : Vtx X) (i : ℕ) : X.treeGraph.dist u (geo X u w i) ≤ i := by
  have := dist_le ((geoWalk X u w).take i)
  rw [Walk.take_length] at this
  exact this.trans (min_le_left _ _)

private theorem dist_geo_right_le (u w : Vtx X) (i : ℕ) :
    X.treeGraph.dist (geo X u w i) w ≤ X.treeGraph.dist u w - i := by
  have := dist_le ((geoWalk X u w).drop i)
  rwa [Walk.drop_length, geoWalk_length] at this

theorem dist_geo {u w : Vtx X} {i : ℕ} (h : i ≤ X.treeGraph.dist u w) :
    X.treeGraph.dist u (geo X u w i) = i := by
  have h1 := dist_geo_le X u w i
  have h2 := dist_geo_right_le X u w i
  have h3 := dist_triangle X u (geo X u w i) w
  omega

theorem dist_geo_right {u w : Vtx X} {i : ℕ} (h : i ≤ X.treeGraph.dist u w) :
    X.treeGraph.dist (geo X u w i) w = X.treeGraph.dist u w - i := by
  have h1 := dist_geo_le X u w i
  have h2 := dist_geo_right_le X u w i
  have h3 := dist_triangle X u (geo X u w i) w
  omega

theorem dist_geo_add {u w : Vtx X} {i : ℕ} (h : i ≤ X.treeGraph.dist u w) :
    X.treeGraph.dist u (geo X u w i) + X.treeGraph.dist (geo X u w i) w =
      X.treeGraph.dist u w := by
  rw [dist_geo X h, dist_geo_right X h]
  omega

theorem eq_geo {u w x : Vtx X}
    (h : X.treeGraph.dist u x + X.treeGraph.dist x w = X.treeGraph.dist u w) :
    x = geo X u w (X.treeGraph.dist u x) := by
  obtain ⟨p₁, hp₁⟩ := (treeGraph_connected X).exists_walk_length_eq_dist u x
  obtain ⟨p₂, hp₂⟩ := (treeGraph_connected X).exists_walk_length_eq_dist x w
  have hq : (p₁.append p₂).length = X.treeGraph.dist u w := by
    rw [Walk.length_append, hp₁, hp₂, h]
  have hqp : (p₁.append p₂).IsPath := (p₁.append p₂).isPath_of_length_eq_dist hq
  have hgp : (geoWalk X u w).IsPath :=
    (geoWalk X u w).isPath_of_length_eq_dist (geoWalk_length X u w)
  have heq := (X.treeGraph_isTree.isAcyclic.subsingleton_path u w).elim ⟨_, hqp⟩ ⟨_, hgp⟩
  have heq' : p₁.append p₂ = geoWalk X u w := congrArg Subtype.val heq
  unfold geo
  rw [← heq', Walk.getVert_append', ← hp₁]
  simp

theorem eq_geo_of_dist {u w x : Vtx X} {i : ℕ} (hi : X.treeGraph.dist u x = i)
    (hw : X.treeGraph.dist u x + X.treeGraph.dist x w = X.treeGraph.dist u w) :
    x = geo X u w i := by
  rw [← hi]
  exact eq_geo X hw

theorem eq_geo_one {u w x : Vtx X} (hux : X.treeGraph.Adj u x)
    (h : X.treeGraph.dist x w + 1 = X.treeGraph.dist u w) : x = geo X u w 1 := by
  apply eq_geo_of_dist X (dist_eq_one_of_adj X hux)
  rw [dist_eq_one_of_adj X hux]
  omega

theorem geo_symm {u w : Vtx X} {i : ℕ} (h : i ≤ X.treeGraph.dist u w) :
    geo X w u (X.treeGraph.dist u w - i) = geo X u w i := by
  symm
  have h1 : X.treeGraph.dist w (geo X u w i) = X.treeGraph.dist u w - i := by
    rw [dist_comm, dist_geo_right X h]
  have h2 : X.treeGraph.dist (geo X u w i) u = i := by
    rw [dist_comm, dist_geo X h]
  have h3 : X.treeGraph.dist w u = X.treeGraph.dist u w := dist_comm
  apply eq_geo_of_dist X h1
  omega

theorem geo_smul (g : X.Universal) (u w : Vtx X) (i : ℕ) :
    geo X (g • u) (g • w) i = g • geo X u w i := by
  by_cases h : i ≤ X.treeGraph.dist u w
  · symm
    apply eq_geo_of_dist X
    · rw [dist_smul, dist_geo X h]
    · rw [dist_smul, dist_smul, dist_smul, dist_geo_add X h]
  · rw [geo_of_le X (by rw [dist_smul]; omega), geo_of_le X (by omega)]

theorem isMVtx_geo {u w : Vtx X} {i : ℕ} (h : i ≤ X.treeGraph.dist u w) :
    IsMVtx X (geo X u w i) ↔ (IsMVtx X u ↔ Even i) := by
  have := even_dist_iff X u (geo X u w i)
  rw [dist_geo X h] at this
  tauto

private theorem dist_geo_geo_le (u w : Vtx X) {i j : ℕ} (hij : i ≤ j) :
    X.treeGraph.dist (geo X u w i) (geo X u w j) ≤ j - i := by
  have := dist_le (((geoWalk X u w).drop i).take (j - i))
  rw [Walk.take_length, Walk.drop_getVert, Nat.add_sub_cancel' hij] at this
  exact this.trans (min_le_left _ _)

theorem dist_geo_geo {u w : Vtx X} {i j : ℕ} (hij : i ≤ j) (hj : j ≤ X.treeGraph.dist u w) :
    X.treeGraph.dist (geo X u w i) (geo X u w j) = j - i := by
  have h1 := dist_geo_geo_le X u w hij
  have h2 := dist_triangle X u (geo X u w i) (geo X u w j)
  rw [dist_geo X (hij.trans hj), dist_geo X hj] at h2
  omega

theorem geo_geo {u w : Vtx X} {i j : ℕ} (hij : i ≤ j) (hj : j ≤ X.treeGraph.dist u w) :
    geo X u (geo X u w j) i = geo X u w i := by
  symm
  apply eq_geo_of_dist X (dist_geo X (hij.trans hj))
  rw [dist_geo X (hij.trans hj), dist_geo_geo X hij hj, dist_geo X hj]
  omega

end CFSG.Quasithin.MS93
