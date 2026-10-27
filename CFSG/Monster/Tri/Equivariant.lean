module

public import CFSG.Monster.Tri.LongLocal

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.YGroups CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V} {mid : V → V → V} {lg : V → V → V → Prop}
  {X : Type*} [Group X] [MulAction X V]

structure EquivariantShort (X : Type*) [Group X] [MulAction X V] (G : SimpleGraph V)
    (mid : V → V → V) (lg : V → V → V → Prop) : Prop where
  adj_iff : ∀ (g : X) {a b : V}, G.Adj (g • a) (g • b) ↔ G.Adj a b
  mid_smul : ∀ (g : X) (x y : V), mid (g • x) (g • y) = g • mid x y
  lg_iff : ∀ (g : X) (x y z : V), lg (g • x) (g • y) (g • z) ↔ lg x y z

@[expose] def EquivariantShort.act (E : EquivariantShort X G mid lg) (g : X) : G →g G where
  toFun v := g • v
  map_rel' h := (E.adj_iff g).2 h

theorem EquivariantShort.permClosure_smul (E : EquivariantShort X G mid lg) (g : X) {a b c : V}
    (h : permClosure lg a b c) : permClosure lg (g • a) (g • b) (g • c) :=
  permClosure_map (fun v => g • v) (fun x y z h => (E.lg_iff g x y z).2 h) h

theorem EquivariantShort.permClosure_of_smul (E : EquivariantShort X G mid lg) (g : X)
    {a b c : V} (h : permClosure lg (g • a) (g • b) (g • c)) : permClosure lg a b c := by
  have := E.permClosure_smul g⁻¹ h
  simpa using this

theorem walk4_congr {a b c c' d d' : V} (hc : c = c') (hd : d = d') (h1 : G.Adj a b)
    (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d a) (h2' : G.Adj b c') (h3' : G.Adj c' d')
    (h4' : G.Adj d' a) :
    (Walk.cons h1 (Walk.cons h2 (Walk.cons h3 (Walk.cons h4 Walk.nil))) : G.Walk a a) =
      Walk.cons h1 (Walk.cons h2' (Walk.cons h3' (Walk.cons h4' Walk.nil))) := by
  subst hc hd
  rfl

theorem longLinkGraph_preconnected_smul (E : EquivariantShort X G mid lg) {x : V}
    (hx : (longLinkGraph G lg x).Preconnected) (g : X) :
    (longLinkGraph G lg (g • x)).Preconnected := by
  let φ : longLinkGraph G lg x →g longLinkGraph G lg (g • x) :=
    { toFun := fun s => ⟨g • s.1, (E.adj_iff g).2 s.2⟩
      map_rel' := fun {s t} h => ⟨(E.adj_iff g).2 h.1, E.permClosure_smul g h.2⟩ }
  intro s' t'
  have hs : G.Adj x (g⁻¹ • (s' : V)) := by
    have := (E.adj_iff g⁻¹).2 s'.2
    simpa using this
  have ht : G.Adj x (g⁻¹ • (t' : V)) := by
    have := (E.adj_iff g⁻¹).2 t'.2
    simpa using this
  have hr := (hx ⟨_, hs⟩ ⟨_, ht⟩).map φ
  have e1 : φ ⟨_, hs⟩ = s' := Subtype.ext (smul_inv_smul g (s' : V))
  have e2 : φ ⟨_, ht⟩ = t' := Subtype.ext (smul_inv_smul g (t' : V))
  rwa [e1, e2] at hr

theorem longLinkGraph_preconnected_of_base (E : EquivariantShort X G mid lg) {v₀ : V}
    (htrans : ∀ x, ∃ g : X, g • v₀ = x) (h₀ : (longLinkGraph G lg v₀).Preconnected) (x : V) :
    (longLinkGraph G lg x).Preconnected := by
  obtain ⟨g, rfl⟩ := htrans x
  exact longLinkGraph_preconnected_smul E h₀ g

theorem ShortStruct.quad_map (S : ShortStruct G mid lg) (E : EquivariantShort X G mid lg)
    (g : X) {x y u : V} (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hL : permClosure lg x y u) :
    (S.quad hxy hxu hyu hL).map (E.act g) =
      S.quad ((E.adj_iff g).2 hxy) ((E.adj_iff g).2 hxu) ((E.adj_iff g).2 hyu)
        (E.permClosure_smul g hL) := by
  simp only [ShortStruct.quad, Walk.map_cons, Walk.map_nil]
  exact walk4_congr (E.mid_smul g x u).symm (E.mid_smul g x y).symm _ _ _ _ _ _ _

theorem ShortStruct.quad_null_of_base (S : ShortStruct G mid lg) (E : EquivariantShort X G mid lg)
    {v₀ : V} (htrans : ∀ x, ∃ g : X, g • v₀ = x)
    (hq₀ : ∀ {y u : V} (hxy : G.Adj v₀ y) (hxu : G.Adj v₀ u) (hyu : G.Adj y u)
      (hL : permClosure lg v₀ y u), MarkedHomotopic lg (S.quad hxy hxu hyu hL) .nil)
    {x y u : V} (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hL : permClosure lg x y u) : MarkedHomotopic lg (S.quad hxy hxu hyu hL) .nil := by
  obtain ⟨g, rfl⟩ := htrans x
  obtain ⟨y₀, rfl⟩ : ∃ y₀, y = g • y₀ := ⟨g⁻¹ • y, (smul_inv_smul g y).symm⟩
  obtain ⟨u₀, rfl⟩ : ∃ u₀, u = g • u₀ := ⟨g⁻¹ • u, (smul_inv_smul g u).symm⟩
  have h1 : G.Adj v₀ y₀ := (E.adj_iff g).1 hxy
  have h2 : G.Adj v₀ u₀ := (E.adj_iff g).1 hxu
  have h3 : G.Adj y₀ u₀ := (E.adj_iff g).1 hyu
  have h4 : permClosure lg v₀ y₀ u₀ := E.permClosure_of_smul g hL
  have := markedHomotopic_map (E.act g) (fun a b c h => (E.lg_iff g a b c).2 h) (hq₀ h1 h2 h3 h4)
  rw [S.quad_map E g h1 h2 h3 h4] at this
  exact this

end CFSG.Monster.Tri
