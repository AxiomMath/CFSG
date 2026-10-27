module

public import CFSG.Monster.B.Recog.GenericWalkHomotopy
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace CFSG.Monster.B.Recog

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

@[expose] def IsCovering (f : H →g G) : Prop :=
  ∀ a, Function.Bijective (f.mapNeighborSet a)

@[expose] def LiftsTriangles (f : H →g G) : Prop :=
  ∀ a y z, G.Adj (f a) y → G.Adj y z → G.Adj z (f a) →
    ∃ b c, H.Adj a b ∧ H.Adj b c ∧ H.Adj c a ∧ f b = y ∧ f c = z

namespace IsCovering

variable {f : H →g G}

theorem existsUnique (hf : IsCovering f) (a : W) {y : V} (h : G.Adj (f a) y) :
    ∃! b, H.Adj a b ∧ f b = y := by
  obtain ⟨⟨b, hb⟩, hb'⟩ := (hf a).2 ⟨y, h⟩
  refine ⟨b, ⟨hb, congrArg Subtype.val hb'⟩, fun b' hb₁ => ?_⟩
  have := (hf a).1 (a₁ := ⟨b', hb₁.1⟩) (a₂ := ⟨b, hb⟩)
    (Subtype.ext (hb₁.2.trans (congrArg Subtype.val hb').symm))
  exact congrArg Subtype.val this

theorem of_existsUnique (h : ∀ a y, G.Adj (f a) y → ∃! b, H.Adj a b ∧ f b = y) :
    IsCovering f := by
  refine fun a => ⟨fun b b' hbb => ?_, fun y => ?_⟩
  · obtain ⟨c, -, hc⟩ := h a (f b) (f.map_adj b.2)
    exact Subtype.ext ((hc b ⟨b.2, rfl⟩).trans
      (hc b' ⟨b'.2, (congrArg Subtype.val hbb).symm⟩).symm)
  · obtain ⟨c, ⟨hac, hc⟩, -⟩ := h a y y.2
    exact ⟨⟨c, hac⟩, Subtype.ext hc⟩

noncomputable def nbr (hf : IsCovering f) (a : W) {y : V} (h : G.Adj (f a) y) : W :=
  ((Equiv.ofBijective _ (hf a)).symm ⟨y, h⟩ : H.neighborSet a)

theorem adj_nbr (hf : IsCovering f) (a : W) {y : V} (h : G.Adj (f a) y) :
    H.Adj a (hf.nbr a h) :=
  ((Equiv.ofBijective _ (hf a)).symm ⟨y, h⟩).2

theorem map_nbr (hf : IsCovering f) (a : W) {y : V} (h : G.Adj (f a) y) :
    f (hf.nbr a h) = y :=
  congrArg Subtype.val ((Equiv.ofBijective _ (hf a)).apply_symm_apply ⟨y, h⟩)

theorem nbr_eq (hf : IsCovering f) {a b : W} (hab : H.Adj a b) {y : V} (h : G.Adj (f a) y)
    (hb : f b = y) : hf.nbr a h = b :=
  (hf.existsUnique a h).unique ⟨hf.adj_nbr a h, hf.map_nbr a h⟩ ⟨hab, hb⟩

theorem nbr_eq_of_eq (hf : IsCovering f) {a a' b : W} (e : a = a') (hab : H.Adj a' b)
    {y : V} (h : G.Adj (f a) y) (hb : f b = y) : hf.nbr a h = b := by
  subst e
  exact hf.nbr_eq hab h hb

noncomputable def liftEnd (hf : IsCovering f) : ∀ {u v : V}, G.Walk u v → (a : W) → f a = u → W
  | _, _, .nil, a, _ => a
  | _, _, .cons h p, a, ha => hf.liftEnd p (hf.nbr a (ha ▸ h)) (hf.map_nbr a _)

theorem map_liftEnd (hf : IsCovering f) :
    ∀ {u v : V} (p : G.Walk u v) (a : W) (ha : f a = u), f (hf.liftEnd p a ha) = v
  | _, _, .nil, _, ha => ha
  | _, _, .cons _ p, _, _ => hf.map_liftEnd p _ _

theorem liftEnd_congr (hf : IsCovering f) {u v : V} (p : G.Walk u v) {a a' : W} (e : a = a')
    (ha : f a = u) (ha' : f a' = u) : hf.liftEnd p a ha = hf.liftEnd p a' ha' := by
  subst e
  rfl

theorem liftEnd_append (hf : IsCovering f) :
    ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (a : W) (ha : f a = u),
      hf.liftEnd (p.append q) a ha = hf.liftEnd q (hf.liftEnd p a ha) (hf.map_liftEnd p a ha)
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, _, .cons _ p, q, _, _ => hf.liftEnd_append p q _ _

theorem liftEnd_copy (hf : IsCovering f) {u v u' v' : V} (p : G.Walk u v) (hu : u = u')
    (hv : v = v') (a : W) (ha : f a = u') :
    hf.liftEnd (p.copy hu hv) a ha = hf.liftEnd p a (ha.trans hu.symm) := by
  subst hu hv
  rfl

theorem liftEnd_map (hf : IsCovering f) :
    ∀ {a b : W} (p : H.Walk a b) (ha : f a = f a), hf.liftEnd (p.map f) a ha = b
  | _, _, .nil, _ => rfl
  | _, _, .cons h p, _ => by
    rw [Walk.map_cons]
    exact (hf.liftEnd_congr (p.map f) (hf.nbr_eq h _ rfl) _ rfl).trans (hf.liftEnd_map p rfl)

theorem liftEnd_backtrack (hf : IsCovering f) {x y v : V} (h : G.Adj x y) (q : G.Walk x v)
    (a : W) (ha : f a = x) :
    hf.liftEnd (.cons h (.cons h.symm q)) a ha = hf.liftEnd q a ha := by
  subst ha
  exact hf.liftEnd_congr q (hf.nbr_eq (hf.adj_nbr a _).symm _ rfl) _ _

theorem liftEnd_triangle (hf : IsCovering f) (ht : LiftsTriangles f) {x y z v : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) (q : G.Walk x v) (a : W)
    (ha : f a = x) :
    hf.liftEnd (.cons hxy (.cons hyz (.cons hzx q))) a ha = hf.liftEnd q a ha := by
  subst ha
  obtain ⟨b, c, hab, hbc, hca, hb, hc⟩ := ht a y z hxy hyz hzx
  exact hf.liftEnd_congr q
    (hf.nbr_eq_of_eq (hf.nbr_eq_of_eq (hf.nbr_eq hab _ hb) hbc _ hc) hca _ rfl) _ _

end IsCovering

theorem ElemMove.liftEnd_eq {f : H →g G} (hf : IsCovering f) (ht : LiftsTriangles f)
    {u v : V} {p q : G.Walk u v} (hpq : ElemMove p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  cases hpq with
  | backtrack p q h => rw [hf.liftEnd_append, hf.liftEnd_append, hf.liftEnd_backtrack]
  | triangle p q hxy hyz hzx =>
    rw [hf.liftEnd_append, hf.liftEnd_append, hf.liftEnd_triangle ht]

theorem Homotopic.liftEnd_eq {f : H →g G} (hf : IsCovering f) (ht : LiftsTriangles f)
    {u v : V} {p q : G.Walk u v} (hpq : Homotopic p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  induction hpq with
  | rel p q h => exact h.liftEnd_eq hf ht a ha
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

namespace IsCovering

variable {f : H →g G}

theorem eq_of_reachable (hf : IsCovering f) (ht : LiftsTriangles f) (hG : Triangulable G)
    {a a' : W} (hr : H.Reachable a a') (h : f a = f a') : a = a' := by
  obtain ⟨p⟩ := hr
  have h₁ := (hG (f a) ((p.map f).copy rfl h.symm)).liftEnd_eq hf ht a rfl
  rw [liftEnd_copy, liftEnd_map] at h₁
  exact h₁.symm

theorem injective_of_triangulable (hf : IsCovering f) (ht : LiftsTriangles f)
    (hG : Triangulable G) (hH : H.Preconnected) : Function.Injective f :=
  fun _ _ h => hf.eq_of_reachable ht hG (hH _ _) h

theorem surjective (hf : IsCovering f) (hG : G.Preconnected) [Nonempty W] :
    Function.Surjective f := by
  intro y
  obtain ⟨a⟩ := ‹Nonempty W›
  obtain ⟨p⟩ := hG (f a) y
  exact ⟨hf.liftEnd p a rfl, hf.map_liftEnd p a rfl⟩

theorem adj_iff_of_injective (hf : IsCovering f) (hinj : Function.Injective f) {a b : W} :
    G.Adj (f a) (f b) ↔ H.Adj a b := by
  refine ⟨fun h => ?_, fun h => f.map_adj h⟩
  have := hf.adj_nbr a h
  rwa [hinj (hf.map_nbr a h)] at this

theorem exists_iso_of_triangulable (hf : IsCovering f) (ht : LiftsTriangles f)
    (hG : Triangulable G) (hGc : G.Connected) (hH : H.Connected) : ∃ e : H ≃g G, ⇑e = f := by
  have : Nonempty W := hH.nonempty
  have hinj := hf.injective_of_triangulable ht hG hH.preconnected
  exact ⟨{ toEquiv := Equiv.ofBijective f ⟨hinj, hf.surjective hGc.preconnected⟩
           map_rel_iff' := hf.adj_iff_of_injective hinj }, rfl⟩

end IsCovering

end CFSG.Monster.B.Recog
