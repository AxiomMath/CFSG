module

public import CFSG.Monster.Tri.ASegFactsNine
public import CFSG.Monster.Tri.ASegFactsThreeA
public import CFSG.Monster.Tri.ASegFactsGmat

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog
  CFSG.Monster.Existence CFSG.Monster.Generated CFSG.Monster.Tri.Leech

section Iso

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem elemMove_map (f : G →g H) {u v : V} {p q : G.Walk u v} (h : ElemMove p q) :
    ElemMove (p.map f) (q.map f) := by
  cases h with
  | backtrack p q h =>
    simpa [Walk.map_append] using ElemMove.backtrack (p.map f) (q.map f) (f.map_adj h)
  | triangle p q hxy hyz hzx =>
    simpa [Walk.map_append] using
      ElemMove.triangle (p.map f) (q.map f) (f.map_adj hxy) (f.map_adj hyz) (f.map_adj hzx)

theorem homotopic_map (f : G →g H) {u v : V} {p q : G.Walk u v} (h : Homotopic p q) :
    Homotopic (p.map f) (q.map f) := by
  induction h with
  | rel _ _ h => exact (elemMove_map f h).homotopic
  | refl => exact Homotopic.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem homotopic_copy {u u' v v' : V} (hu : u = u') (hv : v = v') {p q : G.Walk u v}
    (h : Homotopic p q) : Homotopic (p.copy hu hv) (q.copy hu hv) := by
  subst hu hv
  simpa using h

theorem triangulable_of_iso (e : G ≃g H) (h : Triangulable G) : Triangulable H := by
  intro w p
  have hw : e (e.symm w) = w := e.apply_symm_apply w
  have h1 : Homotopic (p.map e.symm.toHom) .nil := h _ _
  have h2 := homotopic_copy hw hw (homotopic_map e.toHom h1)
  have h4 : ((p.map e.symm.toHom).map e.toHom).copy hw hw = p := by
    apply Walk.ext_support
    have hc : (⇑e.toHom ∘ ⇑e.symm.toHom) = id := funext fun x => e.apply_symm_apply x
    simp only [Walk.support_copy, Walk.support_map, List.map_map]
    rw [hc, List.map_id]
  rw [h4] at h2
  simpa using h2

end Iso

@[expose] def twoAGraphIso {G : Type*} [Group G] {a a' : G} (h : IsConj a a') :
    twoAGraph a ≃g twoAGraph a' where
  toEquiv := Equiv.subtypeEquivRight fun _ => ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hne, hc⟩
      exact ⟨fun e => hne (by rw [e]), h.trans hc⟩
    · rintro ⟨hne, hc⟩
      exact ⟨fun e => hne (Subtype.ext (congrArg (fun p : ConjVert a' => (p : G)) e)),
        h.symm.trans hc⟩

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem twoAGraph_triangulable_of_f1_slice
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (F : ASegFacts a z₀) (hL : LeechGraphFacts a z₀) (hS : BabyFi22Slice)
    (hGen : ThreeCGenerated a z₀) : Triangulable (twoAGraph a) :=
  twoAGraph_triangulable_of_gms I hG F hL (threeACommonNbrs_of I hG hS) hGen
      (edgeNbrInQ_of I hG S365.co1FourU (co1FourW S365.co1FourT))

theorem twoAGraph_triangulable_Gmat_of_slice
    (I : GMSInterfaces (phiB Existence.uBar) Gmat)
    (F : ASegFacts tStarG xmatG) (hS : BabyFi22Slice) (hGen : ThreeCGenerated tStarG xmatG) :
    Triangulable (twoAGraph tStarG) :=
  twoAGraph_triangulable_of_f1_slice I gmsF1Type_Gmat F leechGraphFacts_Gmat hS hGen

theorem twoAGraph_triangulable_Gmat_of_isConj
    (I : GMSInterfaces (phiB Existence.uBar) Gmat)
    (F : ASegFacts tStarG xmatG) (hS : BabyFi22Slice) (hGen : ThreeCGenerated tStarG xmatG)
    {a : Gmat} (ha : IsConj tStarG a) : Triangulable (twoAGraph a) :=
  triangulable_of_iso (twoAGraphIso ha) (twoAGraph_triangulable_Gmat_of_slice I F hS hGen)

end CFSG.Monster.Tri
