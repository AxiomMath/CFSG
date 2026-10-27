module

public import CFSG.Monster.B.Recog.GenericTits

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.Recog

variable {V : Type*} {G : SimpleGraph V}

inductive ElemMoveT (T : V → V → V → Prop) {u v : V} : G.Walk u v → G.Walk u v → Prop
  | backtrack {x y : V} (p : G.Walk u x) (q : G.Walk x v) (h : G.Adj x y) :
      ElemMoveT T (p.append q) (p.append (.cons h (.cons h.symm q)))
  | triangle {x y z : V} (p : G.Walk u x) (q : G.Walk x v) (hxy : G.Adj x y) (hyz : G.Adj y z)
      (hzx : G.Adj z x) (hT : T x y z) :
      ElemMoveT T (p.append q) (p.append (.cons hxy (.cons hyz (.cons hzx q))))

@[expose] def HomotopicT (T : V → V → V → Prop) {u v : V} (p q : G.Walk u v) : Prop :=
  Relation.EqvGen (ElemMoveT T) p q

@[expose] def TriSymm (T : V → V → V → Prop) : Prop := ∀ x y z, T x y z → T y z x ∧ T x z y

@[expose] def triLoop {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) :
    G.Walk x x :=
  .cons hxy (.cons hyz (.cons hzx .nil))

variable {T : V → V → V → Prop}

theorem TriSymm.rotate (hT : TriSymm T) {x y z : V} (h : T x y z) : T y z x := (hT x y z h).1

theorem TriSymm.swap (hT : TriSymm T) {x y z : V} (h : T x y z) : T x z y := (hT x y z h).2

theorem TriSymm.not_rotate (hT : TriSymm T) {x y z : V} (h : ¬ T x y z) : ¬ T y z x :=
  fun h' => h (hT.rotate (hT.rotate h'))

theorem TriSymm.not_swap (hT : TriSymm T) {x y z : V} (h : ¬ T x y z) : ¬ T x z y :=
  fun h' => h (hT.swap h')

theorem ElemMoveT.homotopicT {u v : V} {p q : G.Walk u v} (h : ElemMoveT T p q) :
    HomotopicT T p q :=
  Relation.EqvGen.rel _ _ h

namespace HomotopicT

variable {u v w : V}

@[refl] theorem refl (p : G.Walk u v) : HomotopicT T p p := Relation.EqvGen.refl p

@[symm] theorem symm {p q : G.Walk u v} (h : HomotopicT T p q) : HomotopicT T q p :=
  Relation.EqvGen.symm _ _ h

@[trans] theorem trans {p q r : G.Walk u v} (h₁ : HomotopicT T p q) (h₂ : HomotopicT T q r) :
    HomotopicT T p r :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

end HomotopicT

theorem ElemMoveT.append_left {w u v : V} (r : G.Walk w u) {p q : G.Walk u v}
    (h : ElemMoveT T p q) : ElemMoveT T (r.append p) (r.append q) := by
  cases h with
  | backtrack p q h =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .backtrack _ q h
  | triangle p q hxy hyz hzx hT =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .triangle _ q hxy hyz hzx hT

theorem ElemMoveT.append_right {u v w : V} {p q : G.Walk u v} (h : ElemMoveT T p q)
    (r : G.Walk v w) : ElemMoveT T (p.append r) (q.append r) := by
  cases h with
  | backtrack p q h =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append]
    exact .backtrack p _ h
  | triangle p q hxy hyz hzx hT =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append,
      Walk.cons_append]
    exact .triangle p _ hxy hyz hzx hT

theorem ElemMoveT.reverse (hT : TriSymm T) {u v : V} {p q : G.Walk u v} (h : ElemMoveT T p q) :
    ElemMoveT T p.reverse q.reverse := by
  cases h with
  | backtrack p q h =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    exact .backtrack q.reverse p.reverse h
  | triangle p q hxy hyz hzx hT' =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    exact .triangle q.reverse p.reverse hzx.symm hyz.symm hxy.symm (hT.swap hT')

theorem ElemMoveT.mono {T' : V → V → V → Prop} (hTT' : ∀ x y z, T x y z → T' x y z) {u v : V}
    {p q : G.Walk u v} (h : ElemMoveT T p q) : ElemMoveT T' p q := by
  cases h with
  | backtrack p q h => exact .backtrack p q h
  | triangle p q hxy hyz hzx hT => exact .triangle p q hxy hyz hzx (hTT' _ _ _ hT)

theorem ElemMoveT.elemMove {u v : V} {p q : G.Walk u v} (h : ElemMoveT T p q) : ElemMove p q := by
  cases h with
  | backtrack p q h => exact .backtrack p q h
  | triangle p q hxy hyz hzx _ => exact .triangle p q hxy hyz hzx

theorem ElemMoveT.map {V' : Type*} {G' : SimpleGraph V'} (f : G →g G')
    {T' : V' → V' → V' → Prop} (hf : ∀ x y z, T x y z → T' (f x) (f y) (f z)) {u v : V}
    {p q : G.Walk u v} (h : ElemMoveT T p q) : ElemMoveT T' (p.map f) (q.map f) := by
  cases h with
  | backtrack p q h =>
    simp only [Walk.map_append, Walk.map_cons]
    exact .backtrack _ _ (f.map_adj h)
  | triangle p q hxy hyz hzx hT =>
    simp only [Walk.map_append, Walk.map_cons]
    exact .triangle _ _ (f.map_adj hxy) (f.map_adj hyz) (f.map_adj hzx) (hf _ _ _ hT)

namespace HomotopicT

variable {u v w : V}

theorem append_left (r : G.Walk w u) {p q : G.Walk u v} (h : HomotopicT T p q) :
    HomotopicT T (r.append p) (r.append q) := by
  induction h with
  | rel p q h => exact (h.append_left r).homotopicT
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append_right {p q : G.Walk u v} (h : HomotopicT T p q) (r : G.Walk v w) :
    HomotopicT T (p.append r) (q.append r) := by
  induction h with
  | rel p q h => exact (h.append_right r).homotopicT
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append {p p' : G.Walk u v} {q q' : G.Walk v w} (hp : HomotopicT T p p')
    (hq : HomotopicT T q q') : HomotopicT T (p.append q) (p'.append q') :=
  (hp.append_right q).trans (hq.append_left p')

theorem cons (h : G.Adj w u) {p q : G.Walk u v} (hpq : HomotopicT T p q) :
    HomotopicT T (.cons h p) (.cons h q) := by
  simpa using hpq.append_left (.cons h .nil)

theorem reverse (hT : TriSymm T) {p q : G.Walk u v} (h : HomotopicT T p q) :
    HomotopicT T p.reverse q.reverse := by
  induction h with
  | rel p q h => exact (h.reverse hT).homotopicT
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem mono {T' : V → V → V → Prop} (hTT' : ∀ x y z, T x y z → T' x y z) {p q : G.Walk u v}
    (h : HomotopicT T p q) : HomotopicT T' p q := by
  induction h with
  | rel p q h => exact (h.mono hTT').homotopicT
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem homotopic {p q : G.Walk u v} (h : HomotopicT T p q) : Homotopic p q := by
  induction h with
  | rel p q h => exact h.elemMove.homotopic
  | refl p => exact Homotopic.refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem map {V' : Type*} {G' : SimpleGraph V'} (f : G →g G') {T' : V' → V' → V' → Prop}
    (hf : ∀ x y z, T x y z → T' (f x) (f y) (f z)) {p q : G.Walk u v} (h : HomotopicT T p q) :
    HomotopicT T' (p.map f) (q.map f) := by
  induction h with
  | rel p q h => exact (h.map f hf).homotopicT
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end HomotopicT

theorem homotopicT_cons_cons {x y v : V} (h : G.Adj x y) (q : G.Walk x v) :
    HomotopicT T (.cons h (.cons h.symm q)) q := by
  simpa using (ElemMoveT.backtrack (T := T) (.nil : G.Walk x x) q h).homotopicT.symm

theorem homotopicT_append_reverse {u v : V} (p : G.Walk u v) :
    HomotopicT T (p.append p.reverse) .nil := by
  induction p with
  | nil => exact HomotopicT.refl _
  | @cons a b c h p ih =>
    rw [Walk.reverse_cons, Walk.cons_append, Walk.append_assoc]
    refine (HomotopicT.cons h (ih.append_right (.cons h.symm .nil))).trans ?_
    simpa using homotopicT_cons_cons (T := T) h (.nil : G.Walk a a)

theorem homotopicT_reverse_append {u v : V} (p : G.Walk u v) :
    HomotopicT T (p.reverse.append p) .nil := by
  simpa using homotopicT_append_reverse (T := T) p.reverse

theorem triLoop_reverse {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) :
    (triLoop hxy hyz hzx).reverse = triLoop hzx.symm hyz.symm hxy.symm := by
  simp [triLoop]

theorem homotopicT_edge_triangle {u v a b c : V} (p : G.Walk u a) (q : G.Walk c v)
    (hac : G.Adj a c) (hab : G.Adj a b) (hbc : G.Adj b c) (hT : T a b c) :
    HomotopicT T (p.append (.cons hac q)) (p.append (.cons hab (.cons hbc q))) := by
  have h₁ := (ElemMoveT.triangle (T := T) p (.cons hac q) hab hbc hac.symm hT).homotopicT
  have h₂ : HomotopicT T (p.append (.cons hab (.cons hbc (.cons hac.symm (.cons hac q)))))
      (p.append (.cons hab (.cons hbc q))) := by
    have e₁ : (p.append (.cons hab (.cons hbc (.cons hac.symm (.cons hac q)))) : G.Walk u v) =
        (p.append (.cons hab (.cons hbc .nil))).append (.cons hac.symm (.cons hac q)) := by
      rw [← Walk.append_assoc, Walk.cons_append, Walk.cons_append, Walk.nil_append]
    have e₂ : (p.append (.cons hab (.cons hbc q)) : G.Walk u v) =
        (p.append (.cons hab (.cons hbc .nil))).append q := by
      rw [← Walk.append_assoc, Walk.cons_append, Walk.cons_append, Walk.nil_append]
    rw [e₁, e₂]
    exact HomotopicT.append_left _ (homotopicT_cons_cons hac.symm q)
  exact h₁.trans h₂

theorem homotopicT_triLoop_tetra (hT : TriSymm T) {v p q q' : V} (hvp : G.Adj v p)
    (hpq : G.Adj p q) (hqv : G.Adj q v) (hpq' : G.Adj p q') (hq'v : G.Adj q' v)
    (hqq' : G.Adj q q') (h₁ : T p q q') (h₂ : T v q q') :
    HomotopicT T (triLoop hvp hpq hqv) (triLoop hvp hpq' hq'v) := by
  have hpq'q : T p q' q := hT.swap h₁
  have hq'qv : T q' q v := hT.swap (hT.rotate (hT.rotate h₂))
  have s₁ := homotopicT_edge_triangle (T := T) (.cons hvp .nil) (.cons hqv .nil) hpq hpq'
    hqq'.symm hpq'q
  have s₂ := homotopicT_edge_triangle (T := T) (.cons hvp (.cons hpq' .nil)) .nil hq'v
    hqq'.symm hqv hq'qv
  simp only [triLoop, Walk.cons_append, Walk.nil_append] at s₁ s₂ ⊢
  exact s₁.trans s₂.symm

theorem homotopicT_triLoop_of_chain (hT : TriSymm T) {x : V}
    (hC1 : ∀ {p q q' : V} (h₁ : G.Adj x p) (h₂ : G.Adj p q) (h₃ : G.Adj q x) (h₂' : G.Adj p q')
      (h₃' : G.Adj q' x), ¬ T x p q → ¬ T x p q' →
        HomotopicT T (triLoop h₁ h₂ h₃) (triLoop h₁ h₂' h₃'))
    (hC2 : ∀ {p q p' q' : V}, G.Adj x p → G.Adj p q → G.Adj q x → ¬ T x p q →
      G.Adj x p' → G.Adj p' q' → G.Adj q' x → ¬ T x p' q' →
      Relation.ReflTransGen (fun a c => ∃ b, G.Adj x a ∧ G.Adj a b ∧ G.Adj b x ∧ ¬ T x a b ∧
        G.Adj x c ∧ G.Adj c b ∧ ¬ T x c b) p p')
    {p q p' q' : V} (h₁ : G.Adj x p) (h₂ : G.Adj p q) (h₃ : G.Adj q x) (h₁' : G.Adj x p')
    (h₂' : G.Adj p' q') (h₃' : G.Adj q' x) (hb : ¬ T x p q) (hb' : ¬ T x p' q') :
    HomotopicT T (triLoop h₁ h₂ h₃) (triLoop h₁' h₂' h₃') := by
  have hsecond : ∀ {a c b : V} (ha : G.Adj x a) (hab : G.Adj a b) (hc : G.Adj x c)
      (hcb : G.Adj c b) (hbx : G.Adj b x), ¬ T x a b → ¬ T x c b →
        HomotopicT T (triLoop hc hcb hbx) (triLoop ha hab hbx) := by
    intro a c b ha hab hc hcb hbx hab' hcb'
    have h := (hC1 hbx.symm hcb.symm hc.symm hab.symm ha.symm (hT.not_swap hcb')
      (hT.not_swap hab')).reverse hT
    rwa [triLoop_reverse, triLoop_reverse] at h
  let P : V → Prop := fun a => ∀ (b : V) (ha : G.Adj x a) (hab : G.Adj a b) (hbx : G.Adj b x),
    ¬ T x a b → HomotopicT T (triLoop ha hab hbx) (triLoop h₁ h₂ h₃)
  have hP : P p := fun _ ha hab hbx hab' => hC1 ha hab hbx h₂ h₃ hab' hb
  have hstep : ∀ {a c : V}, (∃ b, G.Adj x a ∧ G.Adj a b ∧ G.Adj b x ∧ ¬ T x a b ∧
      G.Adj x c ∧ G.Adj c b ∧ ¬ T x c b) → P a → P c := by
    rintro a c ⟨b, ha, hab, hbx, hab', hc, hcb, hcb'⟩ hPa d hc' hcd hdx hcd'
    exact (hC1 hc' hcd hdx hcb hbx hcd' hcb').trans
      ((hsecond ha hab hc hcb hbx hab' hcb').trans (hPa b ha hab hbx hab'))
  have hall : ∀ a, Relation.ReflTransGen (fun a c => ∃ b, G.Adj x a ∧ G.Adj a b ∧ G.Adj b x ∧
      ¬ T x a b ∧ G.Adj x c ∧ G.Adj c b ∧ ¬ T x c b) p a → P a := by
    intro a ha
    induction ha with
    | refl => exact hP
    | tail _ hbc ih => exact hstep hbc ih
  exact (hall p' (hC2 h₁ h₂ h₃ hb h₁' h₂' h₃' hb') q' h₁' h₂' h₃' hb').symm

section TwoClass

variable (hT : TriSymm T)
  (hedge : ∀ x y, G.Adj x y → ∃ z, G.Adj y z ∧ G.Adj z x ∧ ¬ T x y z)
  (hloc : ∀ {x y z y' z' : V} (h₁ : G.Adj x y) (h₂ : G.Adj y z) (h₃ : G.Adj z x)
    (h₁' : G.Adj x y') (h₂' : G.Adj y' z') (h₃' : G.Adj z' x), ¬ T x y z → ¬ T x y' z' →
      HomotopicT T (triLoop h₁ h₂ h₃) (triLoop h₁' h₂' h₃'))

include hT hedge hloc in
theorem homotopicT_transport {x y : V} (p : G.Walk x y) {b₁ b₂ : V} (hb₁ : G.Adj y b₁)
    (hb₂ : G.Adj b₁ b₂) (hb₃ : G.Adj b₂ y) (hb : ¬ T y b₁ b₂) {a₁ a₂ : V} (ha₁ : G.Adj x a₁)
    (ha₂ : G.Adj a₁ a₂) (ha₃ : G.Adj a₂ x) (ha : ¬ T x a₁ a₂) :
    HomotopicT T (p.append ((triLoop hb₁ hb₂ hb₃).append p.reverse)) (triLoop ha₁ ha₂ ha₃) := by
  induction p generalizing a₁ a₂ with
  | nil =>
    simpa using hloc hb₁ hb₂ hb₃ ha₁ ha₂ ha₃ hb ha
  | @cons x x₁ y h p ih =>
    obtain ⟨z, hxz, hzx₁, hz⟩ := hedge x₁ x h.symm
    have h₁ := ih (hb₁ := hb₁) (hb₃ := hb₃) (hb := hb) (ha₁ := h.symm) (ha₂ := hxz)
      (ha₃ := hzx₁) (ha := hz)
    rw [Walk.reverse_cons, Walk.cons_append]
    have e : p.append ((triLoop hb₁ hb₂ hb₃).append (p.reverse.append (.cons h.symm .nil))) =
        (p.append ((triLoop hb₁ hb₂ hb₃).append p.reverse)).append (.cons h.symm .nil) := by
      simp only [Walk.append_assoc]
    rw [e]
    refine (HomotopicT.cons h (h₁.append_right (.cons h.symm .nil))).trans ?_
    have e' : (Walk.cons h ((triLoop h.symm hxz hzx₁).append (.cons h.symm .nil)) : G.Walk x x) =
        .cons h (.cons h.symm (triLoop hxz hzx₁ h.symm)) := by
      simp [triLoop]
    rw [e']
    refine (homotopicT_cons_cons h _).trans ?_
    exact hloc hxz hzx₁ h.symm ha₁ ha₂ ha₃ (hT.not_rotate hz) ha

include hT hloc in
theorem homotopicT_triLoop_append_triLoop {x a₁ a₂ : V} (ha₁ : G.Adj x a₁) (ha₂ : G.Adj a₁ a₂)
    (ha₃ : G.Adj a₂ x) (ha : ¬ T x a₁ a₂) :
    HomotopicT T ((triLoop ha₁ ha₂ ha₃).append (triLoop ha₁ ha₂ ha₃)) .nil := by
  have hr : HomotopicT T (triLoop ha₁ ha₂ ha₃) (triLoop ha₁ ha₂ ha₃).reverse := by
    rw [triLoop_reverse]
    exact hloc ha₁ ha₂ ha₃ ha₃.symm ha₂.symm ha₁.symm ha (hT.not_swap ha)
  exact (HomotopicT.append_left _ hr).trans (homotopicT_append_reverse _)

include hT hedge hloc in
theorem homotopicT_nil_or_triLoop (hG : Triangulable G) {x a₁ a₂ : V} (ha₁ : G.Adj x a₁)
    (ha₂ : G.Adj a₁ a₂) (ha₃ : G.Adj a₂ x) (ha : ¬ T x a₁ a₂) (W : G.Walk x x) :
    HomotopicT T W .nil ∨ HomotopicT T W (triLoop ha₁ ha₂ ha₃) := by
  set α := triLoop ha₁ ha₂ ha₃ with hα
  have hαα := homotopicT_triLoop_append_triLoop hT hloc ha₁ ha₂ ha₃ ha
  let R : G.Walk x x → G.Walk x x → Prop := fun W W' =>
    HomotopicT T W W' ∨ HomotopicT T W (α.append W')
  have hRsymm : ∀ {W W'}, R W W' → R W' W := by
    rintro W W' (h | h)
    · exact Or.inl h.symm
    · refine Or.inr ?_
      have h1 : HomotopicT T (α.append W) (α.append (α.append W')) := h.append_left α
      have h2 : HomotopicT T (α.append (α.append W')) W' := by
        rw [Walk.append_assoc]
        simpa using hαα.append_right W'
      exact (h2.symm.trans h1.symm)
  have hRtrans : ∀ {W W' W''}, R W W' → R W' W'' → R W W'' := by
    rintro W W' W'' (h | h) (h' | h')
    · exact Or.inl (h.trans h')
    · exact Or.inr (h.trans h')
    · exact Or.inr (h.trans (h'.append_left α))
    · refine Or.inl (h.trans ((h'.append_left α).trans ?_))
      rw [Walk.append_assoc]
      simpa using hαα.append_right W''
  have hRmove : ∀ {W W'}, ElemMove W W' → R W W' := by
    intro W W' h
    cases h with
    | backtrack p q h => exact Or.inl (ElemMoveT.backtrack p q h).homotopicT
    | @triangle y b₁ b₂ p q hxy hyz hzx =>
      by_cases hTy : T y b₁ b₂
      · exact Or.inl (ElemMoveT.triangle p q hxy hyz hzx hTy).homotopicT
      · refine hRsymm (Or.inr ?_)
        have htr := homotopicT_transport hT hedge hloc p hxy hyz hzx hTy ha₁ ha₂ ha₃ ha
        have e : (p.append (.cons hxy (.cons hyz (.cons hzx q))) : G.Walk x x) =
            p.append ((triLoop hxy hyz hzx).append q) := by
          simp [triLoop]
        rw [e]
        have h1 : HomotopicT T (p.append ((triLoop hxy hyz hzx).append q))
            ((p.append ((triLoop hxy hyz hzx).append p.reverse)).append (p.append q)) := by
          have h2 : HomotopicT T ((triLoop hxy hyz hzx).append q)
              ((triLoop hxy hyz hzx).append ((p.reverse.append p).append q)) :=
            HomotopicT.append_left _ (by simpa using
              ((homotopicT_reverse_append (T := T) p).append_right q).symm)
          refine (HomotopicT.append_left p h2).trans ?_
          simp only [Walk.append_assoc]
          exact HomotopicT.refl _
        exact h1.trans (htr.append_right _)
  have hR : ∀ {W W'}, Homotopic W W' → R W W' := by
    intro W W' h
    induction h with
    | rel W W' h => exact hRmove h
    | refl W => exact Or.inl (HomotopicT.refl W)
    | symm W W' _ ih => exact hRsymm ih
    | trans W W' W'' _ _ ih₁ ih₂ => exact hRtrans ih₁ ih₂
  rcases hR (hG x W) with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

end TwoClass

section Covering

variable {W : Type*} {H : SimpleGraph W}

@[expose] def LiftsTrianglesT (T : V → V → V → Prop) (f : H →g G) : Prop :=
  ∀ a y z, G.Adj (f a) y → G.Adj y z → G.Adj z (f a) → T (f a) y z →
    ∃ b c, H.Adj a b ∧ H.Adj b c ∧ H.Adj c a ∧ f b = y ∧ f c = z

theorem liftEnd_triLoop {f : H →g G} (hf : IsCovering f) (ht : LiftsTrianglesT T f)
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) (hT : T x y z) (a : W)
    (ha : f a = x) : hf.liftEnd (triLoop hxy hyz hzx) a ha = a := by
  subst ha
  obtain ⟨b, c, hab, hbc, hca, rfl, rfl⟩ := ht a y z hxy hyz hzx hT
  have e : (Walk.cons hab (.cons hbc (.cons hca .nil)) : H.Walk a a).map f =
      triLoop hxy hyz hzx := by
    simp [triLoop]
  rw [← e]
  exact hf.liftEnd_map _ rfl

theorem liftEnd_triangleT {f : H →g G} (hf : IsCovering f) (ht : LiftsTrianglesT T f)
    {x y z v : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) (hT : T x y z)
    (q : G.Walk x v) (a : W) (ha : f a = x) :
    hf.liftEnd (.cons hxy (.cons hyz (.cons hzx q))) a ha = hf.liftEnd q a ha := by
  have e : (Walk.cons hxy (.cons hyz (.cons hzx q)) : G.Walk x v) =
      (triLoop hxy hyz hzx).append q := by
    simp [triLoop]
  rw [e, hf.liftEnd_append]
  exact hf.liftEnd_congr q (liftEnd_triLoop hf ht hxy hyz hzx hT a ha) _ _

theorem ElemMoveT.liftEnd_eq {f : H →g G} (hf : IsCovering f) (ht : LiftsTrianglesT T f)
    {u v : V} {p q : G.Walk u v} (hpq : ElemMoveT T p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  cases hpq with
  | backtrack p q h => rw [hf.liftEnd_append, hf.liftEnd_append, hf.liftEnd_backtrack]
  | triangle p q hxy hyz hzx hT =>
    rw [hf.liftEnd_append, hf.liftEnd_append, liftEnd_triangleT hf ht hxy hyz hzx hT]

theorem HomotopicT.liftEnd_eq {f : H →g G} (hf : IsCovering f) (ht : LiftsTrianglesT T f)
    {u v : V} {p q : G.Walk u v} (hpq : HomotopicT T p q) (a : W) (ha : f a = u) :
    hf.liftEnd p a ha = hf.liftEnd q a ha := by
  induction hpq with
  | rel p q h => exact h.liftEnd_eq hf ht a ha
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem liftEnd_nil' {f : H →g G} (hf : IsCovering f) (a : W) :
    hf.liftEnd (.nil : G.Walk (f a) (f a)) a rfl = a := by
  simpa using hf.liftEnd_map (Walk.nil : H.Walk a a) rfl

theorem liftEnd_map_copy {f : H →g G} (hf : IsCovering f) {a b : W} (q : H.Walk a b)
    (hb : f b = f a) : hf.liftEnd ((q.map f).copy rfl hb) a rfl = b := by
  rw [hf.liftEnd_copy, hf.liftEnd_map]

variable (hT : TriSymm T)
  (hedge : ∀ x y, G.Adj x y → ∃ z, G.Adj y z ∧ G.Adj z x ∧ ¬ T x y z)
  (hloc : ∀ {x y z y' z' : V} (h₁ : G.Adj x y) (h₂ : G.Adj y z) (h₃ : G.Adj z x)
    (h₁' : G.Adj x y') (h₂' : G.Adj y' z') (h₃' : G.Adj z' x), ¬ T x y z → ¬ T x y' z' →
      HomotopicT T (triLoop h₁ h₂ h₃) (triLoop h₁' h₂' h₃'))

include hT hedge hloc in
theorem exists_fiber_subset_pair (hG : Triangulable G) {f : H →g G} (hf : IsCovering f)
    (ht : LiftsTrianglesT T f) (a : W) :
    ∃ a', ∀ b, H.Reachable a b → f b = f a → b = a ∨ b = a' := by
  by_cases hn : ∃ y, G.Adj (f a) y
  · obtain ⟨y, hy⟩ := hn
    obtain ⟨z, hyz, hzx, hz⟩ := hedge (f a) y hy
    refine ⟨hf.liftEnd (triLoop hy hyz hzx) a rfl, fun b hab hb => ?_⟩
    obtain ⟨q⟩ := hab
    rcases homotopicT_nil_or_triLoop hT hedge hloc hG hy hyz hzx hz ((q.map f).copy rfl hb)
      with h | h
    · left
      have e := h.liftEnd_eq hf ht a rfl
      rwa [liftEnd_map_copy, liftEnd_nil'] at e
    · right
      have e := h.liftEnd_eq hf ht a rfl
      rwa [liftEnd_map_copy] at e
  · refine ⟨a, fun b hab _ => ?_⟩
    obtain ⟨q⟩ := hab
    cases q with
    | nil => exact Or.inl rfl
    | cons h _ => exact absurd ⟨_, f.map_adj h⟩ hn

end Covering

section Amalgam

variable {X : Type*} [Group X] [MulAction X V] {Z : Type*} [Group Z]

open Recog.Tits in
theorem liftsTrianglesT_cosetHom (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    {v w : V} (hvw : G.Adj v w) {Xv Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    (p : Z →* X) {Zv Ze : Subgroup Z} (hinje : Set.InjOn p Ze)
    (himv : Zv.map p = Xv) (hime : Ze.map p = Xe) (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map p)
    {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X} {Zt : ι → Subgroup Z}
    (hinjt : ∀ j, Set.InjOn p (Zt j)) (himt : ∀ j, (Zt j).map p = Xt j)
    (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map p) (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map p)
    {s : Z} (hsZe : s ∈ Ze) (hsv : p s • v = w) (hsw : p s • w = v)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (hTinv : ∀ (g : X) a b c, T a b c → T (g • a) (g • b) (g • c))
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v → T v y₁ y₂ →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂) :
    LiftsTrianglesT T (cosetHom hadj p Zv s v (fun _ ha => smul_eq_of_mem hXv p himv ha)
      (hsv ▸ hvw)) := by
  have hs := not_mem_of_smul_eq hvw hXv p himv hsv
  have hs₂ := mul_self_mem hXv p hinje hime hve hsZe hsv hsw
  intro x y₁ y₂ h₁ h₂ h₃ hT₀
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  rw [cosetHom_mk] at h₁ h₃ hT₀
  have hT' : T v ((p z)⁻¹ • y₁) ((p z)⁻¹ • y₂) := by
    simpa using hTinv (p z)⁻¹ _ _ _ hT₀
  obtain ⟨j, g, hgv, hgw, hgu⟩ := htri ((p z)⁻¹ • y₁) ((p z)⁻¹ • y₂)
    (by simpa using hadj (p z)⁻¹ h₁) (hadj (p z)⁻¹ h₂) (by simpa using hadj (p z)⁻¹ h₃) hT'
  obtain ⟨a, ha, rfl⟩ : g ∈ Zv.map p := himv ▸ (hXv g).2 hgv
  obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
  obtain ⟨t, ht, rfl⟩ : τ ∈ (Zt j).map p := (himt j).symm ▸ hτm
  obtain ⟨ρ, hρm, hρv, hρw, hρu⟩ := hρ j
  obtain ⟨r, hr, rfl⟩ : ρ ∈ (Zt j).map p := (himt j).symm ▸ hρm
  have hsr : s⁻¹ * r ∈ Zv :=
    inv_mul_mem_of_tri hXv hXe p hinje hime hve hinjt himt hvt het hsZe hsv ht hτv hτw hr hρv
  have hr₃ : r * r * r ∈ Zv := mem_of_mem_tri_of_smul_eq hXv p hinjt himt hvt
    ((Zt j).mul_mem ((Zt j).mul_mem hr hr) hr) (by simp only [map_mul, mul_smul, hρv, hρw, hρu])
  have e₁ : ((z : Z) : Z ⧸ Zv) = ((z * a : Z) : Z ⧸ Zv) :=
    QuotientGroup.eq.2 (by simpa using ha)
  have e₂ : ((z : Z) : Z ⧸ Zv) = ((z * a * r * r * r : Z) : Z ⧸ Zv) :=
    QuotientGroup.eq.2 (by simpa [mul_assoc] using Zv.mul_mem ha hr₃)
  refine ⟨((z * a * r : Z) : Z ⧸ Zv), ((z * a * r * r : Z) : Z ⧸ Zv), ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₁]
    exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · rw [e₂]
    exact cosetGraph_adj_mk_mul hs hs₂ _ hsr
  · rw [cosetHom_mk, map_mul, map_mul, mul_smul, mul_smul, hρv, hgw, smul_inv_smul]
  · rw [cosetHom_mk, map_mul, map_mul, map_mul, mul_smul, mul_smul, mul_smul, hρv, hρw, hgu,
      smul_inv_smul]

variable (hT : TriSymm T)
  (hedge : ∀ x y, G.Adj x y → ∃ z, G.Adj y z ∧ G.Adj z x ∧ ¬ T x y z)
  (hloc : ∀ {x y z y' z' : V} (h₁ : G.Adj x y) (h₂ : G.Adj y z) (h₃ : G.Adj z x)
    (h₁' : G.Adj x y') (h₂' : G.Adj y' z') (h₃' : G.Adj z' x), ¬ T x y z → ¬ T x y' z' →
      HomotopicT T (triLoop h₁ h₂ h₃) (triLoop h₁' h₂' h₃'))

open Recog.Tits in
include hT hedge hloc in
theorem exists_ker_subset_pair (hG : Triangulable G)
    (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    {v w : V} (hvw : G.Adj v w) (hlocv : ∀ y, G.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    (hswap : ∃ g : X, g • v = w ∧ g • w = v)
    {Xv Xe : Subgroup X} (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    {ι : Type*} {u : ι → V} {Xt : ι → Subgroup X}
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (hTinv : ∀ (g : X) a b c, T a b c → T (g • a) (g • b) (g • c))
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v → T v y₁ y₂ →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂)
    (p : Z →* X) {Zv Ze : Subgroup Z} {Zt : ι → Subgroup Z}
    (hinjv : Set.InjOn p Zv) (hinje : Set.InjOn p Ze) (hinjt : ∀ j, Set.InjOn p (Zt j))
    (himv : Zv.map p = Xv) (hime : Ze.map p = Xe) (himt : ∀ j, (Zt j).map p = Xt j)
    (hve : Xv ⊓ Xe ≤ (Zv ⊓ Ze).map p) (hvt : ∀ j, Xv ⊓ Xt j ≤ (Zv ⊓ Zt j).map p)
    (het : ∀ j, Xe ⊓ Xt j ≤ (Ze ⊓ Zt j).map p) :
    ∃ n ∈ Zv ⊔ Ze, p n = 1 ∧ ∀ z ∈ Zv ⊔ Ze, p z = 1 → z = 1 ∨ z = n := by
  obtain ⟨s, hsZe, hsv, hsw⟩ := exists_swap_lift hXe p hime hswap
  have hs := not_mem_of_smul_eq hvw hXv p himv hsv
  have hs₂ := mul_self_mem hXv p hinje hime hve hsZe hsv hsw
  have hcov := isCovering_cosetHom hadj hvw hXv hXe p hinjv hinje himv hime hve hlocv hsZe hsv
    hsw
  have htr := liftsTrianglesT_cosetHom hadj hvw hXv hXe p hinje himv hime hve hinjt himt hvt
    het hsZe hsv hsw hτ hρ hTinv htri
  obtain ⟨a', ha'⟩ := exists_fiber_subset_pair hT hedge hloc hG hcov htr ((1 : Z) : Z ⧸ Zv)
  have hfib : ∀ z ∈ Zv ⊔ Ze, p z = 1 →
      ((z : Z) : Z ⧸ Zv) = ((1 : Z) : Z ⧸ Zv) ∨ ((z : Z) : Z ⧸ Zv) = a' := fun z hz hpz =>
    ha' _ (reachable_cosetGraph hXv hXe p hinje hime hve hs hs₂ hsZe hsv hz)
      (by rw [cosetHom_mk, cosetHom_mk, hpz, map_one])
  have hone : ∀ z, p z = 1 → ((z : Z) : Z ⧸ Zv) = ((1 : Z) : Z ⧸ Zv) → z = 1 := by
    intro z hpz h
    have hzv : z ∈ Zv := by simpa using QuotientGroup.eq.1 h.symm
    exact hinjv hzv Zv.one_mem (by rw [hpz, map_one])
  by_cases hex : ∃ n ∈ Zv ⊔ Ze, p n = 1 ∧ ((n : Z) : Z ⧸ Zv) = a'
  · obtain ⟨n, hn, hpn, hna⟩ := hex
    refine ⟨n, hn, hpn, fun z hz hpz => ?_⟩
    rcases hfib z hz hpz with h | h
    · exact Or.inl (hone z hpz h)
    · right
      have hnz : n⁻¹ * z ∈ Zv := QuotientGroup.eq.1 (hna.trans h.symm)
      have := hinjv hnz Zv.one_mem (by rw [map_mul, map_inv, hpn, hpz, inv_one, mul_one,
        map_one])
      exact (inv_mul_eq_one.1 this).symm
  · refine ⟨1, (Zv ⊔ Ze).one_mem, map_one p, fun z hz hpz => ?_⟩
    rcases hfib z hz hpz with h | h
    · exact Or.inl (hone z hpz h)
    · exact absurd ⟨z, hz, hpz, h⟩ hex

open Recog.Tits in
include hT hedge hloc in
theorem tits_completion_ker_le_two (hconn : G.Preconnected) (hG : Triangulable G)
    (hadj : ∀ (g : X) {a b : V}, G.Adj a b → G.Adj (g • a) (g • b))
    {v w : V} (hvw : G.Adj v w) (hlocv : ∀ y, G.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    (hswap : ∃ g : X, g • v = w ∧ g • w = v)
    (Xv Xe : Subgroup X) (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    {ι : Type*} (u : ι → V) (Xt : ι → Subgroup X)
    (hXt : ∀ j, ∀ g ∈ Xt j, g • v = v ∨ g • v = w ∨ g • v = u j)
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v)
    (hTinv : ∀ (g : X) a b c, T a b c → T (g • a) (g • b) (g • c))
    (htri : ∀ y₁ y₂, G.Adj v y₁ → G.Adj y₁ y₂ → G.Adj y₂ v → T v y₁ y₂ →
      ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂)
    {Y : Type*} [Group Y] (φv : Xv →* Y) (φe : Xe →* Y) (φt : ∀ j, Xt j →* Y)
    (hve : ∀ a (ha : a ∈ Xv) (hb : a ∈ Xe), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ Xv) (hb : a ∈ Xt j), φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ Xe) (hb : a ∈ Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    (∀ j (a : Xt j), (φt j a, (a : X)) ∈ homGraph φv ⊔ homGraph φe) ∧
      (homGraph φv ⊔ homGraph φe).map (MonoidHom.snd Y X) = ⊤ ∧
      ∃ n ∈ homGraph φv ⊔ homGraph φe, n.2 = 1 ∧
        ∀ k ∈ homGraph φv ⊔ homGraph φe, k.2 = 1 → k = 1 ∨ k = n := by
  set K := homGraph φv ⊔ homGraph φe with hK
  have htK : ∀ j (a : Xt j), (φt j a, (a : X)) ∈ K := by
    intro j
    let L := K.comap ((φt j).prod (Xt j).subtype)
    have hLv : ∀ a : Xt j, (a : X) • v = v → a ∈ L := fun ⟨a, ha⟩ hav => by
      change (φt j ⟨a, ha⟩, a) ∈ K
      rw [← hvt j a ((hXv a).2 hav) ha]
      exact Subgroup.mem_sup_left (mk_mem_homGraph φv ⟨a, _⟩)
    obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
    obtain ⟨ρ, hρm, hρv, hρw, -⟩ := hρ j
    have hτL : (⟨τ, hτm⟩ : Xt j) ∈ L := by
      change (φt j ⟨τ, hτm⟩, τ) ∈ K
      rw [← het j τ ((hXe τ).2 (Or.inr ⟨hτv, hτw⟩)) hτm]
      exact Subgroup.mem_sup_right (mk_mem_homGraph φe ⟨τ, _⟩)
    have hLw : ∀ a : Xt j, (a : X) • v = w → a ∈ L := fun a hav => by
      have : (⟨τ, hτm⟩ : Xt j)⁻¹ * a ∈ L := hLv _ (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hav, inv_smul_eq_iff, hτv])
      simpa using L.mul_mem hτL this
    intro a
    rcases hXt j a a.2 with h | h | h
    · exact hLv a h
    · exact hLw a h
    · have : (⟨ρ, hρm⟩ : Xt j)⁻¹ * a ∈ L := hLw _ (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h, inv_smul_eq_iff, hρw])
      exact (by simpa using L.mul_mem (hLw ⟨ρ, hρm⟩ hρv) this : a ∈ L)
  have htop : Xv ⊔ Xe = ⊤ := sup_eq_top_of_preconnected hadj hconn hlocv hswap hXv hXe
  refine ⟨htK, by rw [Subgroup.map_sup, map_snd_homGraph, map_snd_homGraph, htop], ?_⟩
  obtain ⟨n, hn, hpn, hker⟩ := exists_ker_subset_pair hT hedge hloc hG hadj hvw hlocv hswap
    hXv hXe hτ hρ hTinv htri (MonoidHom.snd Y X) (injOn_snd_homGraph φv)
    (injOn_snd_homGraph φe) (fun j => injOn_snd_homGraph (φt j)) (map_snd_homGraph φv)
    (map_snd_homGraph φe) (fun j => map_snd_homGraph (φt j)) (inf_le_map_inf_homGraph hve)
    (fun j => inf_le_map_inf_homGraph (hvt j)) (fun j => inf_le_map_inf_homGraph (het j))
  exact ⟨n, hn, hpn, hker⟩

end Amalgam

end CFSG.Monster.B.GSide
