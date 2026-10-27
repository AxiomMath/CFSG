module

public import CFSG.Quasithin.Recognition.F4Basic
public import CFSG.GH74.BNPair.Lemma309

public section

namespace CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V}

theorem exists_gPath_of_isGLSPath {l : List V}
    (hl : CFSG.GH74.BNPair.IsGLSPath Γ l) (hne : l ≠ []) :
    ∃ p : GPath Γ (l.length - 1), p.NoBack ∧ (List.range l.length).map p = l := by
  classical
  have hu : l.head? = some (l.head hne) := List.head?_eq_some_head hne
  have hv : l.getLast? = some (l.getLast hne) := List.getLast?_eq_getLast_of_ne_nil hne
  obtain ⟨f, k, hk, -, -, hadj, hnb, hget⟩ :=
    CFSG.GH74.BNPair.IsGLSPath.exists_fun (G := Γ) hl hu hv
  have hk' : k = l.length - 1 := by omega
  subst k
  let p : GPath Γ (l.length - 1) :=
    { toFun := fun i => f (min i (l.length - 1))
      adj := fun i hi => by
        have h1 : min i (l.length - 1) = i := min_eq_left (by omega)
        have h2 : min (i + 1) (l.length - 1) = i + 1 := min_eq_left (by omega)
        simp only [h1, h2]
        exact hadj i hi
      tail := fun i hi => by
        have h1 : min i (l.length - 1) = l.length - 1 := min_eq_right hi
        have h2 : min (l.length - 1) (l.length - 1) = l.length - 1 := min_self _
        simp [h1, h2] }
  refine ⟨p, ?_, ?_⟩
  · intro i hi heq
    have h1 : p i = f i := by
      simp [p, min_eq_left (show i ≤ l.length - 1 by omega)]
    have h2 : p (i + 2) = f (i + 2) := by
      simp [p, min_eq_left (show i + 2 ≤ l.length - 1 by omega)]
    rw [h1, h2] at heq
    exact hnb i hi heq
  · have hp_eq : (List.range l.length).map p = (List.range l.length).map f := by
      apply List.map_congr_left
      intro i hi
      have hi' : i < l.length := List.mem_range.mp hi
      simp [p, min_eq_left (show i ≤ l.length - 1 by omega)]
    have hmapf : (List.range l.length).map f = l := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < l.length
      · rw [List.getElem?_map, List.getElem?_range hi, Option.map_some]
        exact (hget i (by omega)).symm
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rw [hp_eq, hmapf]

namespace IsGenPolygon

theorem polyHyp {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    (hT : ∀ v, 3 ≤ (Γ.neighborSet v).encard) : CFSG.GH74.BNPair.PolyHyp Γ m := by
  obtain ⟨col, hcol⟩ := hP.bipartite
  refine ⟨hm, hP.connected.nonempty, ?_, ?_, ⟨col, hcol⟩, hT⟩
  · exact fun u v => ⟨hP.connected u v, hP.diam_le u v⟩
  · intro u v p q hp hq hpu hqu hpv hqv hplen hqlen
    have hpn : p ≠ [] := by
      intro h
      rw [h] at hpu
      simp at hpu
    have hqn : q ≠ [] := by
      intro h
      rw [h] at hqu
      simp at hqu
    obtain ⟨p', hp'nb, hp'map⟩ := exists_gPath_of_isGLSPath hp hpn
    obtain ⟨q', hq'nb, hq'map⟩ := exists_gPath_of_isGLSPath hq hqn
    have hp_pos : 0 < p.length := List.length_pos_iff.mpr hpn
    have hq_pos : 0 < q.length := List.length_pos_iff.mpr hqn
    have hp0 : p' 0 = u := by
      have h := congrArg (fun l : List V => l[0]?) hp'map
      rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some] at h
      rw [← List.head?_eq_getElem?, hpu] at h
      exact Option.some.inj h
    have hp_last : p' (p.length - 1) = v := by
      have hlast : p[p.length - 1]? = some v := by
        rw [← CFSG.GH74.BNPair.getLast?_eq_getElem?_of_length (l := p)
          (m := p.length - 1) (by omega)]
        exact hpv
      have h := congrArg (fun l : List V => l[p.length - 1]?) hp'map
      rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some] at h
      rw [hlast] at h
      exact Option.some.inj h
    have hq0 : q' 0 = u := by
      have h := congrArg (fun l : List V => l[0]?) hq'map
      rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some] at h
      rw [← List.head?_eq_getElem?, hqu] at h
      exact Option.some.inj h
    have hq_last : q' (q.length - 1) = v := by
      have hlast : q[q.length - 1]? = some v := by
        rw [← CFSG.GH74.BNPair.getLast?_eq_getElem?_of_length (l := q)
          (m := q.length - 1) (by omega)]
        exact hqv
      have h := congrArg (fun l : List V => l[q.length - 1]?) hq'map
      rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some] at h
      rw [hlast] at h
      exact Option.some.inj h
    have hp_geo : p'.IsGeodesic :=
      GPath.isGeodesic_of_noBack hP.connected hcol hP.uniqueGeod (p.length - 1)
        (by omega) p' hp'nb
    have hq_geo : q'.IsGeodesic :=
      GPath.isGeodesic_of_noBack hP.connected hcol hP.uniqueGeod (q.length - 1)
        (by omega) q' hq'nb
    have hp_dist : p.length - 1 = Γ.dist u v := by
      have := hp_geo
      rw [GPath.IsGeodesic, hp0, hp_last] at this
      exact this.symm
    have hq_dist : q.length - 1 = Γ.dist u v := by
      have := hq_geo
      rw [GPath.IsGeodesic, hq0, hq_last] at this
      exact this.symm
    have hlen : p.length = q.length := by omega
    let q'' : GPath Γ (p.length - 1) :=
      { toFun := q'.toFun
        adj := fun i hi => q'.adj i (by omega)
        tail := fun i hi => by
          rw [q'.tail i (by omega), q'.tail (p.length - 1) (by omega)] }
    have hq''0 : q'' 0 = u := by simpa [q''] using hq0
    have hq''v : q'' (p.length - 1) = v := by
      simpa [q'', hlen] using hq_last
    have hq''geo : q''.IsGeodesic := by
      rw [GPath.IsGeodesic, hq''0, hq''v]
      omega
    have heq : p' = q'' :=
      hP.uniqueGeod (p.length - 1) p' q'' hp_geo hq''geo (by rw [hp0, hq''0])
        (by rw [hp_last, hq''v]) (by omega)
    have hfun : ∀ i, p' i = q' i := fun i => by
      have := congrArg (fun r : GPath Γ (p.length - 1) => r i) heq
      simpa [q''] using this
    have hmap_eq : (List.range p.length).map p' = (List.range q.length).map q' := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < p.length
      · have hiq : i < q.length := by omega
        rw [List.getElem?_map, List.getElem?_range hi, Option.map_some,
          List.getElem?_map, List.getElem?_range hiq, Option.map_some, hfun i]
      · have hiq : ¬ i < q.length := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    calc p = (List.range p.length).map p' := hp'map.symm
      _ = (List.range q.length).map q' := hmap_eq
      _ = q := hq'map

end IsGenPolygon

theorem IsGenPolygon.eq_one_of_fix_gPath {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    (hT : ∀ v, 3 ≤ (Γ.neighborSet v).encard) (p : GPath Γ (m + 1)) (hp : p.NoBack)
    {g : Equiv.Perm V} (hg : ∀ v w, Γ.Adj (g v) (g w) ↔ Γ.Adj v w)
    (hfix : ∀ i, i ≤ m + 1 → g (p i) = p i)
    (hfixΓ : ∀ i, 1 ≤ i → i ≤ m - 1 → ∀ w, Γ.Adj (p i) w → g w = w) : g = 1 := by
  have hpoly := hP.polyHyp hm hT
  let π : List V := (List.range (m + 1)).map p
  let π' : List V := (List.range (m + 2)).map p
  have hπ' : CFSG.GH74.BNPair.IsGLSPath Γ π' := by
    have h := CFSG.GH74.BNPair.isGLSPath_map_range (G := Γ) p (m + 1) p.adj hp
    have e : m + 1 + 1 = m + 2 := by omega
    rw [e] at h
    simpa [π'] using h
  have hlen : π.length = m + 1 := by simp [π]
  have hlen' : π'.length = m + 2 := by simp [π']
  have hπ'eq : π' = π ++ [p (m + 1)] := by
    simp only [π, π']
    conv_lhs => rw [show m + 2 = (m + 1) + 1 by omega, List.range_succ,
      List.map_append]
    simp
  have hpre : π <+: π' := by
    rw [hπ'eq]
    exact List.prefix_append _ _
  have hfix' : ∀ v ∈ π', g v = v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact hfix i (by have := List.mem_range.mp hi; omega)
  have hfixΓ' : ∀ v ∈ CFSG.GH74.BNPair.interiorVertices π, ∀ w, Γ.Adj v w → g w = w := by
    intro v hv w hw
    have hv' : v ∈ CFSG.GH74.BNPair.interiorVertices
        ((List.range ((m - 1) + 2)).map p) := by
      simpa [π, show (m - 1) + 2 = m + 1 by omega] using hv
    obtain ⟨i, hi, rfl⟩ := CFSG.GH74.BNPair.mem_interior_map_range (f := p) (k := m - 1) hv'
    exact hfixΓ (i + 1) (by omega) hi w hw
  exact hpoly.eq_one_of_fix hπ' hlen hlen' hpre hg hfix' hfixΓ'

private def prepend (y : V) {n : ℕ} (p : GPath Γ n) (h : Γ.Adj y (p 0)) :
    GPath Γ (n + 1) where
  toFun i := if i = 0 then y else p (i - 1)
  adj i hi := by
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      simpa using h
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      exact p.adj j (by omega)
  tail i hi := by
    have hi0 : i ≠ 0 := by omega
    have h1 : n ≤ i - 1 := by omega
    simp [hi0, p.tail (i - 1) h1, show n + 1 - 1 = n by omega]

@[simp] private theorem prepend_zero (y : V) {n : ℕ} (p : GPath Γ n)
    (h : Γ.Adj y (p 0)) : prepend y p h 0 = y := rfl

@[simp] private theorem prepend_succ (y : V) {n : ℕ} (p : GPath Γ n)
    (h : Γ.Adj y (p 0)) (i : ℕ) : prepend y p h (i + 1) = p i := by
  show (if i + 1 = 0 then y else p (i + 1 - 1)) = p i
  rw [if_neg (by omega), show i + 1 - 1 = i by omega]

private theorem prepend_noBack (y : V) {n : ℕ} (p : GPath Γ n) (h : Γ.Adj y (p 0))
    (hp : p.NoBack) (hy : y ≠ p 1) : (prepend y p h).NoBack := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    have h2 : prepend y p h 2 = p 1 := by
      rw [show (2 : ℕ) = 1 + 1 by rfl, prepend_succ]
    rw [prepend_zero, h2]
    exact hy
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have h1 : prepend y p h (j + 1) = p j := by rw [prepend_succ]
    have h2 : prepend y p h (j + 1 + 2) = p (j + 2) := by
      rw [show j + 1 + 2 = (j + 2) + 1 by omega, prepend_succ]
    rw [h1, h2]
    exact hp j (by omega)

theorem IsGenPolygon.eq_one_of_fix_root {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    (hT : ∀ v, 3 ≤ (Γ.neighborSet v).encard) (p : GPath Γ m) (hp : p.NoBack)
    {g : Equiv.Perm V} (hg : ∀ v w, Γ.Adj (g v) (g w) ↔ Γ.Adj v w)
    (hfixΓ : ∀ i, 1 ≤ i → i ≤ m - 1 → ∀ w, Γ.Adj (p i) w → g w = w)
    {w : V} (hw : Γ.Adj (p m) w) (hw' : w ≠ p (m - 1)) (hgw : g w = w) : g = 1 := by
  let q : GPath Γ (m + 1) := p.snoc w hw
  have hqnb : q.NoBack := by
    intro i hi
    by_cases hle : i + 2 ≤ m
    · rw [show q i = p i from GPath.snoc_of_le p w hw (by omega),
        show q (i + 2) = p (i + 2) from GPath.snoc_of_le p w hw (by omega)]
      exact hp i hle
    · have him : i = m - 1 := by omega
      subst him
      rw [show q (m - 1) = p (m - 1) from GPath.snoc_of_le p w hw (by omega),
        show q (m - 1 + 2) = w from by
          rw [show m - 1 + 2 = m + 1 by omega, GPath.snoc_last]]
      exact Ne.symm hw'
  refine IsGenPolygon.eq_one_of_fix_gPath hP hm hT q hqnb hg ?_ ?_
  · intro i hi
    by_cases him : i = m + 1
    · subst him
      rw [show q (m + 1) = w from by simp [q]]
      exact hgw
    · have hi' : i ≤ m := by omega
      rw [show q i = p i from GPath.snoc_of_le p w hw hi']
      match i with
      | 0 => exact hfixΓ 1 (by omega) (by omega) (p 0) (p.adj 0 (by omega)).symm
      | 1 => exact hfixΓ 2 (by omega) (by omega) (p 1) (p.adj 1 (by omega)).symm
      | j + 2 =>
          exact hfixΓ (j + 1) (by omega) (by omega) (p (j + 2))
            (p.adj (j + 1) (by omega))
  · intro i hi1 hi2 w' hw'
    have hqi : q i = p i := GPath.snoc_of_le p w hw (by omega)
    rw [hqi] at hw'
    exact hfixΓ i hi1 hi2 w' hw'

private def RigidFull (Γ : SimpleGraph V) (g : Equiv.Perm V) (x : V) : Prop :=
  g x = x ∧ ∀ w, Γ.Adj x w → g w = w

private theorem exists_ne_ne_of_three_le_encard {s : Set V} (hs : 3 ≤ s.encard) (x y : V) :
    ∃ a ∈ s, a ≠ x ∧ a ≠ y := by
  by_contra h
  have hxy : ∀ a, a ∈ s → a = x ∨ a = y := by
    intro a ha
    by_contra hc
    push Not at hc
    exact h ⟨a, ha, hc.1, hc.2⟩
  have hsub : s ⊆ {x, y} := by
    intro a ha
    rcases hxy a ha with h | h
    · simp [h]
    · simp [h]
  have h1 := Set.encard_le_encard hsub
  have h2 : ({x, y} : Set V).encard ≤ 2 := by
    calc ({x, y} : Set V).encard ≤ ({y} : Set V).encard + 1 := Set.encard_insert_le _ _
      _ = 2 := by simp; norm_num
  have h3 := le_trans hs (le_trans h1 h2)
  norm_num at h3

private theorem ne_succ_of_path {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 2 ≤ m)
    {x z : V} {q : GPath Γ (m - 1)} (hzx : Γ.dist x z = m) (hqx : q (m - 1) = x) :
    z ≠ q 1 := by
  intro h
  have hq1x : Γ.dist (q 1) x ≤ m - 2 := by
    have := GPath.dist_le_sub hP.connected q (i := 1) (j := m - 1) (by omega) le_rfl
    rwa [hqx] at this
  have hxq1 : Γ.dist x (q 1) = m := by
    rw [h] at hzx
    exact hzx
  have hxq1' : Γ.dist (q 1) x = m := by
    rwa [SimpleGraph.dist_comm]
  omega

private theorem dist_eq_m_of_adj_ne {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    {u w a v : V} (S : GPath Γ ((m - 2) + 1)) (hS : S.IsGeodesic)
    (hS0 : S 0 = u) (hSw : S ((m - 2) + 1) = w) (hSv : S (m - 2) = v)
    (ha : Γ.Adj w a) (hav : a ≠ v) : Γ.dist u a = m := by
  obtain ⟨col, hcol⟩ := hP.bipartite
  have huw : Γ.dist u w = (m - 2) + 1 := by
    have := hS
    rw [GPath.IsGeodesic, hS0, hSw] at this
    exact this
  have h := GPath.dist_adj_succ_or hP.connected hcol u ha
  rcases h with h | h
  · omega
  · have hda : Γ.dist u a = m - 2 := by omega
    exfalso
    obtain ⟨q, hq0, hqa, -⟩ := GPath.exists_geodesic' hP.connected u a hda
    let R : GPath Γ ((m - 2) + 1) := q.snoc w (by rw [hqa]; exact ha.symm)
    have hR0 : R 0 = u := by
      rw [show R 0 = q 0 from GPath.snoc_of_le q w _ (Nat.zero_le _), hq0]
    have hRw : R ((m - 2) + 1) = w := by simp [R]
    have hRgeo : R.IsGeodesic := by
      show Γ.dist (R 0) (R ((m - 2) + 1)) = (m - 2) + 1
      rw [hR0, hRw]
      exact huw
    have heq : R = S := hP.uniqueGeod ((m - 2) + 1) R S hRgeo hS
      (by rw [hR0, hS0]) (by rw [hRw, hSw]) (by omega)
    have hmid := congrArg (fun P : GPath Γ ((m - 2) + 1) => P (m - 2)) heq
    have hRa : R (m - 2) = a := by
      rw [show R (m - 2) = q (m - 2) from
        GPath.snoc_of_le q w _ (by omega), hqa]
    rw [hRa, hSv] at hmid
    exact hav hmid

private theorem isFull_of_dist_eq {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    {g : Equiv.Perm V} (hg : ∀ v w, Γ.Adj (g v) (g w) ↔ Γ.Adj v w)
    {x y : V} (hx : RigidFull Γ g x) (hy : g y = y) (hxy : Γ.dist x y = m) :
    RigidFull Γ g y := by
  classical
  obtain ⟨col, hcol⟩ := hP.bipartite
  refine ⟨hy, fun a ha => ?_⟩
  have hda : Γ.dist a x = m - 1 := by
    have h := GPath.dist_adj_succ_or hP.connected hcol x ha
    rw [show Γ.dist x y = m from hxy] at h
    have hdiam := hP.diam_le x a
    have h' : Γ.dist x a = m - 1 := by omega
    rwa [SimpleGraph.dist_comm] at h'
  obtain ⟨q, hq0, hqx, hqnb⟩ := GPath.exists_geodesic' hP.connected a x hda
  have hqgeo : q.IsGeodesic := by
    show Γ.dist (q 0) (q (m - 1)) = m - 1
    rw [hq0, hqx]
    exact hda
  have hmapnb : (q.map g (fun u v h => (hg u v).mpr h)).NoBack := by
    intro i hi heq
    exact hqnb i hi (g.injective heq)
  have hmapgeo : (q.map g (fun u v h => (hg u v).mpr h)).IsGeodesic := by
    have h := GPath.isGeodesic_of_noBack hP.connected hcol hP.uniqueGeod (m - 1)
      (by omega) (q.map g (fun u v h => (hg u v).mpr h)) hmapnb
    simpa [GPath.IsGeodesic, hq0, hqx, hx.1] using h
  have hdga : Γ.dist (g a) x = m - 1 := by
    have := hmapgeo
    simpa [GPath.IsGeodesic, hq0, hqx, hx.1] using this
  obtain ⟨q', hq'0, hq'x, hq'nb⟩ := GPath.exists_geodesic' hP.connected (g a) x hdga
  have hq'geo : q'.IsGeodesic := by
    show Γ.dist (q' 0) (q' (m - 1)) = m - 1
    rw [hq'0, hq'x]
    exact hdga
  have heq : q.map g (fun u v h => (hg u v).mpr h) = q' :=
    hP.uniqueGeod (m - 1) _ _ hmapgeo hq'geo
      (by rw [GPath.map_apply, hq0, hq'0])
      (by rw [GPath.map_apply, hqx, hq'x, hx.1]) (by omega)
  have hq'mid : q' (m - 2) = g (q (m - 2)) := by
    have := congrArg (fun r : GPath Γ (m - 1) => r (m - 2)) heq
    simpa [GPath.map_apply] using this.symm
  have hbadj : Γ.Adj (q (m - 2)) x := by
    have h := q.adj (m - 2) (by omega)
    rwa [show m - 2 + 1 = m - 1 by omega, hqx] at h
  have hgb : g (q (m - 2)) = q (m - 2) := hx.2 _ hbadj.symm
  have hq'b : q' (m - 2) = q (m - 2) := by rw [hq'mid, hgb]
  have hyq1 : y ≠ q 1 :=
    ne_succ_of_path hP (by omega) hxy hqx
  let qt : GPath Γ (m - 2) := q.take (m - 2) (by omega)
  have hqt0 : qt 0 = a := by
    rw [show qt 0 = q 0 from GPath.take_apply_of_le q (m - 2) _ (Nat.zero_le _), hq0]
  have hqtlast : qt (m - 2) = q (m - 2) := by
    rw [GPath.take_apply_of_le q (m - 2) _ le_rfl]
  have hqt1 : qt 1 = q 1 := by
    rw [GPath.take_apply_of_le q (m - 2) _ (by omega)]
  let r : GPath Γ ((m - 2) + 1) := prepend y qt (by rw [hqt0]; exact ha)
  have hrnoBack : r.NoBack := by
    simpa [r] using prepend_noBack y qt (by rw [hqt0]; exact ha)
      (hqnb.take (m - 2) (by omega)) (by rw [hqt1]; exact hyq1)
  have hrgeo : r.IsGeodesic :=
    GPath.isGeodesic_of_noBack hP.connected hcol hP.uniqueGeod ((m - 2) + 1)
      (by omega) r hrnoBack
  have hr0 : r 0 = y := by simpa [r] using prepend_zero y qt _
  have hrlast : r ((m - 2) + 1) = q (m - 2) := by
    have h : r ((m - 2) + 1) = qt (m - 2) := by
      simpa [r] using prepend_succ y qt (by rw [hqt0]; exact ha) (m - 2)
    rw [h, hqtlast]
  have hga_y : Γ.Adj y (g a) := by
    have := (hg y a).mpr ha
    rwa [hy] at this
  have hyq'1 : y ≠ q' 1 :=
    ne_succ_of_path hP (by omega) hxy hq'x
  let qt' : GPath Γ (m - 2) := q'.take (m - 2) (by omega)
  have hqt'0 : qt' 0 = g a := by
    rw [show qt' 0 = q' 0 from GPath.take_apply_of_le q' (m - 2) _ (Nat.zero_le _), hq'0]
  have hqt'last : qt' (m - 2) = q (m - 2) := by
    rw [GPath.take_apply_of_le q' (m - 2) _ le_rfl, hq'b]
  have hqt'1 : qt' 1 = q' 1 := by
    rw [GPath.take_apply_of_le q' (m - 2) _ (by omega)]
  let r' : GPath Γ ((m - 2) + 1) := prepend y qt' (by rw [hqt'0]; exact hga_y)
  have hr'noBack : r'.NoBack := by
    simpa [r'] using prepend_noBack y qt' (by rw [hqt'0]; exact hga_y)
      (hq'nb.take (m - 2) (by omega)) (by rw [hqt'1]; exact hyq'1)
  have hr'geo : r'.IsGeodesic :=
    GPath.isGeodesic_of_noBack hP.connected hcol hP.uniqueGeod ((m - 2) + 1)
      (by omega) r' hr'noBack
  have hr'0 : r' 0 = y := by simpa [r'] using prepend_zero y qt' _
  have hr'last : r' ((m - 2) + 1) = q (m - 2) := by
    have h : r' ((m - 2) + 1) = qt' (m - 2) := by
      simpa [r'] using prepend_succ y qt' (by rw [hqt'0]; exact hga_y) (m - 2)
    rw [h, hqt'last]
  have heqr : r = r' :=
    hP.uniqueGeod ((m - 2) + 1) r r' hrgeo hr'geo
      (by rw [hr0, hr'0]) (by rw [hrlast, hr'last]) (by omega)
  have h1 := congrArg (fun P : GPath Γ ((m - 2) + 1) => P 1) heqr
  have hr1 : r 1 = a := by
    have h := prepend_succ y qt (by rw [hqt0]; exact ha) 0
    simpa [r, hqt0] using h
  have hr'1 : r' 1 = g a := by
    have h := prepend_succ y qt' (by rw [hqt'0]; exact hga_y) 0
    simpa [r', hqt'0] using h
  rw [hr1, hr'1] at h1
  exact h1.symm

private theorem isFull_add_two {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    (hT : ∀ v, 3 ≤ (Γ.neighborSet v).encard) (z : ℕ → V)
    (hadj : ∀ k, Γ.Adj (z k) (z (k + 1))) (hzb : ∀ k, z k ≠ z (k + 2))
    (hzp : ∀ k, z (k + 2 * m) = z k)
    {g : Equiv.Perm V} (hg : ∀ v w, Γ.Adj (g v) (g w) ↔ Γ.Adj v w)
    (hfix : ∀ k, g (z k) = z k) {k : ℕ}
    (hk0 : RigidFull Γ g (z k)) (hk1 : RigidFull Γ g (z (k + 1))) :
    RigidFull Γ g (z (k + 2)) := by
  obtain ⟨col, hcol⟩ := hP.bipartite
  have hdist := GPath.window_dist hP.connected hcol hP.uniqueGeod z hadj hzb
  obtain ⟨a, ha_mem, ha_ne1, ha_ne2⟩ :=
    exists_ne_ne_of_three_le_encard (hT (z (k + m + 1))) (z (k + m)) (z (k + m + 2))
  have ha : Γ.Adj (z (k + m + 1)) a := ha_mem
  have hmid : RigidFull Γ g (z (k + m + 1)) := by
    refine isFull_of_dist_eq hP hm hg hk1 (hfix _) ?_
    have h := hdist (k + 1) (d := m) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hafix : g a = a := hmid.2 a ha
  let S1 : GPath Γ ((m - 2) + 1) :=
    GPath.seqPathRev z hadj (k + 2 * m) ((m - 2) + 1) (by omega)
  have hS1_0 : S1 0 = z k := by
    have h : S1 0 = z (k + 2 * m) := by
      simp only [S1]
      rw [GPath.seqPathRev_apply z hadj (k + 2 * m) ((m - 2) + 1) (by omega)
        (i := 0) (by omega)]
      simp
    rw [h, hzp k]
  have hS1_last : S1 ((m - 2) + 1) = z (k + m + 1) := by
    have h : S1 ((m - 2) + 1) = z ((k + 2 * m) - ((m - 2) + 1)) := by
      simp only [S1]
      rw [GPath.seqPathRev_apply z hadj (k + 2 * m) ((m - 2) + 1) (by omega)
        (i := (m - 2) + 1) (by omega)]
    rw [h]
    congr 1
    omega
  have hS1_mid : S1 (m - 2) = z (k + m + 2) := by
    have h : S1 (m - 2) = z ((k + 2 * m) - (m - 2)) := by
      simp only [S1]
      rw [GPath.seqPathRev_apply z hadj (k + 2 * m) ((m - 2) + 1) (by omega)
        (i := m - 2) (by omega)]
    rw [h]
    congr 1
    omega
  have hS1_geo : S1.IsGeodesic := by
    show Γ.dist (S1 0) (S1 ((m - 2) + 1)) = (m - 2) + 1
    rw [hS1_0, hS1_last]
    have h := hdist (k + m + 1) (d := m - 1) (by omega)
    have e : k + m + 1 + (m - 1) = k + 2 * m := by omega
    rw [e, hzp k] at h
    rw [SimpleGraph.dist_comm, h]
    omega
  have hdak : Γ.dist (z k) a = m :=
    dist_eq_m_of_adj_ne hP hm S1 hS1_geo hS1_0 hS1_last hS1_mid ha ha_ne2
  have hafull : RigidFull Γ g a := isFull_of_dist_eq hP hm hg hk0 hafix hdak
  let S2 : GPath Γ ((m - 2) + 1) := GPath.seqPath z hadj (k + 2) ((m - 2) + 1)
  have hS2_0 : S2 0 = z (k + 2) := by
    simp only [S2]
    rw [GPath.seqPath_apply z hadj (k + 2) ((m - 2) + 1) (i := 0) (by omega)]
  have hS2_last : S2 ((m - 2) + 1) = z (k + m + 1) := by
    simp only [S2]
    rw [GPath.seqPath_apply z hadj (k + 2) ((m - 2) + 1)
      (i := (m - 2) + 1) (by omega)]
    congr 1
    omega
  have hS2_mid : S2 (m - 2) = z (k + m) := by
    simp only [S2]
    rw [GPath.seqPath_apply z hadj (k + 2) ((m - 2) + 1) (i := m - 2) (by omega)]
    congr 1
    omega
  have hS2_geo : S2.IsGeodesic := by
    show Γ.dist (S2 0) (S2 ((m - 2) + 1)) = (m - 2) + 1
    rw [hS2_0, hS2_last]
    have h := hdist (k + 2) (d := m - 1) (by omega)
    have e : k + 2 + (m - 1) = k + m + 1 := by omega
    rw [e] at h
    rw [h]
    omega
  have hd2a : Γ.dist (z (k + 2)) a = m :=
    dist_eq_m_of_adj_ne hP hm S2 hS2_geo hS2_0 hS2_last hS2_mid ha ha_ne1
  refine isFull_of_dist_eq hP hm hg hafull (hfix _) ?_
  rwa [SimpleGraph.dist_comm]

theorem IsGenPolygon.eq_one_of_fix_apartment {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    (hT : ∀ v, 3 ≤ (Γ.neighborSet v).encard) (z : ℕ → V)
    (hz : ∀ k, Γ.Adj (z k) (z (k + 1))) (hzb : ∀ k, z k ≠ z (k + 2))
    (hzp : ∀ k, z (k + 2 * m) = z k)
    {g : Equiv.Perm V} (hg : ∀ v w, Γ.Adj (g v) (g w) ↔ Γ.Adj v w)
    (hfix : ∀ k, g (z k) = z k)
    (h0 : ∀ w, Γ.Adj (z 0) w → g w = w)
    (h1 : ∀ w, Γ.Adj (z 1) w → g w = w) : g = 1 := by
  have hfull0 : RigidFull Γ g (z 0) := ⟨hfix 0, h0⟩
  have hfull1 : RigidFull Γ g (z 1) := ⟨hfix 1, h1⟩
  have hfull : ∀ k, k ≤ m - 1 → RigidFull Γ g (z k) := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases k with _ | _ | j
      · exact hfull0
      · exact hfull1
      · have hj1 : RigidFull Γ g (z (j + 1)) := ih (j + 1) (by omega) (by omega)
        have hj : RigidFull Γ g (z j) := ih j (by omega) (by omega)
        exact isFull_add_two hP hm hT z hz hzb hzp hg hfix hj hj1
  let p : GPath Γ (m + 1) := GPath.seqPath z hz 0 (m + 1)
  have hp_apply : ∀ {i : ℕ}, i ≤ m + 1 → p i = z i := by
    intro i hi
    simp only [p]
    rw [GPath.seqPath_apply z hz 0 (m + 1) (i := i) hi]
    simp
  have hp : p.NoBack := by
    intro i hi
    rw [hp_apply (by omega), hp_apply (by omega)]
    exact hzb i
  refine IsGenPolygon.eq_one_of_fix_gPath hP hm hT p hp hg ?_ ?_
  · intro i hi
    rw [hp_apply hi]
    exact hfix i
  · intro i hi1 hi2 w hw
    rw [hp_apply (by omega)] at hw
    exact (hfull i hi2).2 w hw

theorem IsGenPolygon.smul_eq_of_fix_gPath {H : Type*} [Group H] [MulAction H V]
    [GraphAction H Γ] {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    (hT : ∀ v, 3 ≤ (Γ.neighborSet v).encard) (p : GPath Γ (m + 1)) (hp : p.NoBack)
    {g : H} (hfix : ∀ i, i ≤ m + 1 → g • p i = p i)
    (hfixΓ : ∀ i, 1 ≤ i → i ≤ m - 1 → ∀ w, Γ.Adj (p i) w → g • w = w) :
    ∀ v : V, g • v = v := by
  have hperm : MulAction.toPerm g = 1 :=
    IsGenPolygon.eq_one_of_fix_gPath hP hm hT p hp
      (fun v w => by simpa [MulAction.toPerm_apply] using GraphAction.adj_smul g v w)
      (fun i hi => by simpa [MulAction.toPerm_apply] using hfix i hi)
      (fun i hi1 hi2 w hw => by
        simpa [MulAction.toPerm_apply] using hfixΓ i hi1 hi2 w hw)
  intro v
  have := congrArg (fun e : Equiv.Perm V => e v) hperm
  simpa [MulAction.toPerm_apply] using this

theorem IsGenPolygon.smul_eq_of_fix_root {H : Type*} [Group H] [MulAction H V]
    [GraphAction H Γ] {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    (hT : ∀ v, 3 ≤ (Γ.neighborSet v).encard) (p : GPath Γ m) (hp : p.NoBack)
    {g : H} (hfixΓ : ∀ i, 1 ≤ i → i ≤ m - 1 → ∀ w, Γ.Adj (p i) w → g • w = w)
    {w : V} (hw : Γ.Adj (p m) w) (hw' : w ≠ p (m - 1)) (hgw : g • w = w) :
    ∀ v : V, g • v = v := by
  have hperm : MulAction.toPerm g = 1 :=
    IsGenPolygon.eq_one_of_fix_root hP hm hT p hp
      (fun v w => by simpa [MulAction.toPerm_apply] using GraphAction.adj_smul g v w)
      (fun i hi1 hi2 w hw => by
        simpa [MulAction.toPerm_apply] using hfixΓ i hi1 hi2 w hw)
      hw hw' (by simpa [MulAction.toPerm_apply] using hgw)
  intro v
  have := congrArg (fun e : Equiv.Perm V => e v) hperm
  simpa [MulAction.toPerm_apply] using this

theorem IsGenPolygon.smul_eq_of_fix_apartment {H : Type*} [Group H] [MulAction H V]
    [GraphAction H Γ] {m : ℕ} (hP : IsGenPolygon Γ m) (hm : 3 ≤ m)
    (hT : ∀ v, 3 ≤ (Γ.neighborSet v).encard) (z : ℕ → V)
    (hz : ∀ k, Γ.Adj (z k) (z (k + 1))) (hzb : ∀ k, z k ≠ z (k + 2))
    (hzp : ∀ k, z (k + 2 * m) = z k)
    {g : H} (hfix : ∀ k, g • z k = z k)
    (h0 : ∀ w, Γ.Adj (z 0) w → g • w = w)
    (h1 : ∀ w, Γ.Adj (z 1) w → g • w = w) : ∀ v : V, g • v = v := by
  have hperm : MulAction.toPerm g = 1 :=
    IsGenPolygon.eq_one_of_fix_apartment hP hm hT z hz hzb hzp
      (fun v w => by simpa [MulAction.toPerm_apply] using GraphAction.adj_smul g v w)
      (fun k => by simpa [MulAction.toPerm_apply] using hfix k)
      (fun w hw => by simpa [MulAction.toPerm_apply] using h0 w hw)
      (fun w hw => by simpa [MulAction.toPerm_apply] using h1 w hw)
  intro v
  have := congrArg (fun e : Equiv.Perm V => e v) hperm
  simpa [MulAction.toPerm_apply] using this

end CFSG.Quasithin
