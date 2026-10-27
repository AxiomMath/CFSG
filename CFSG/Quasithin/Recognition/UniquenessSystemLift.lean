module

public import CFSG.Quasithin.Recognition.UniquenessSystemMoves
public import CFSG.Quasithin.Background.F3Cover

public section

namespace CFSG.Quasithin.Asc94

universe u₁ u₂

variable {Vh : Type u₁} {V : Type u₂} {Γh : SimpleGraph Vh} {Γ : SimpleGraph V} {θ : Vh → V}

variable (Γh θ) in
@[expose] noncomputable def liftStep (q : Vh) (w : V) : Vh :=
  open Classical in if h : ∃ q', Γh.Adj q q' ∧ θ q' = w then h.choose else q

theorem liftStep_spec {q : Vh} {w : V} (h : ∃ q', Γh.Adj q q' ∧ θ q' = w) :
    Γh.Adj q (liftStep Γh θ q w) ∧ θ (liftStep Γh θ q w) = w := by
  classical
  rw [liftStep, dite_eq_left h]
  exact h.choose_spec

theorem liftStep_self (hθ : GraphCovering Γh Γ θ) (q : Vh) : liftStep Γh θ q (θ q) = q := by
  classical
  rw [liftStep, dite_eq_right]
  rintro ⟨q', hqq', hθq'⟩
  exact (hθ.adj q q' hqq').ne hθq'.symm

theorem liftStep_of_adj (hθ : GraphCovering Γh Γ θ) {q q' : Vh} (h : Γh.Adj q q') :
    liftStep Γh θ q (θ q') = q' := by
  have hs := liftStep_spec (Γh := Γh) (θ := θ) ⟨q', h, rfl⟩
  exact hθ.loc_inj q _ _ hs.1 h hs.2

theorem liftStep_over (hθ : GraphCovering Γh Γ θ) {q : Vh} {w : V} (h : Γ.Adj (θ q) w) :
    Γh.Adj q (liftStep Γh θ q w) ∧ θ (liftStep Γh θ q w) = w :=
  liftStep_spec (hθ.loc_surj q w h)

theorem foldl_liftStep_map (hθ : GraphCovering Γh Γ θ) :
    ∀ (l : List Vh) (q : Vh), (q :: l).IsChain Γh.Adj →
      ((q :: l).map θ).foldl (liftStep Γh θ) q = (q :: l).getLast (List.cons_ne_nil _ _)
  | [], q, _ => by simp [liftStep_self hθ]
  | q' :: l, q, h => by
    rw [List.isChain_cons_cons] at h
    have ih := foldl_liftStep_map hθ l q' h.2
    simp only [List.map_cons, List.foldl_cons] at ih ⊢
    rw [liftStep_self hθ, liftStep_of_adj hθ h.1, List.getLast_cons (List.cons_ne_nil _ _)]
    rw [liftStep_self hθ] at ih
    exact ih

theorem θ_foldl_liftStep_aux (hθ : GraphCovering Γh Γ θ) :
    ∀ (l : List V) (q : Vh), (θ q :: l).IsChain Γ.Adj →
      θ (l.foldl (liftStep Γh θ) q) = (θ q :: l).getLast (List.cons_ne_nil _ _)
  | [], q, _ => rfl
  | w :: l, q, h => by
    rw [List.isChain_cons_cons] at h
    have hs := liftStep_over hθ h.1
    simp only [List.foldl_cons]
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    have := θ_foldl_liftStep_aux hθ l (liftStep Γh θ q w) (by rw [hs.2]; exact h.2)
    rw [this]
    simp only [hs.2]

theorem θ_foldl_liftStep (hθ : GraphCovering Γh Γ θ) {p : List V} (hp : IsPath Γ p) {q : Vh}
    (hq : p.head? = some (θ q)) : θ (p.foldl (liftStep Γh θ) q) = p.getLast hp.1 := by
  obtain ⟨-, hch⟩ := hp
  cases p with
  | nil => simp at hq
  | cons a l =>
    simp only [List.head?_cons, Option.some.injEq] at hq
    subst hq
    simp only [List.foldl_cons, liftStep_self hθ]
    exact θ_foldl_liftStep_aux hθ l q hch

theorem θ_foldl_liftStep_prefix (hθ : GraphCovering Γh Γ θ) {l₁ l₂ : List V} {w : V}
    (hp : (l₁ ++ w :: l₂).IsChain Γ.Adj) {q : Vh} (hq : (l₁ ++ w :: l₂).head? = some (θ q)) :
    θ ((l₁ ++ [w]).foldl (liftStep Γh θ) q) = w := by
  have hp' : IsPath Γ (l₁ ++ [w]) := ⟨by simp, (List.isChain_split.mp hp).1⟩
  have hq' : (l₁ ++ [w]).head? = some (θ q) := by
    rw [← hq]; cases l₁ <;> simp
  rw [θ_foldl_liftStep hθ hp' hq']
  simp

theorem foldl_liftStep_elemMove (hθ : GraphCovering Γh Γ θ) {C : Set (List V)}
    (hC : ∀ c ∈ rotRev C, IsPath Γ c ∧
      ∀ w, c.head? = some w → ∀ q : Vh, θ q = w → c.foldl (liftStep Γh θ) q = q)
    {p p' : List V} (hm : ElemMove Γ C p p') (hp : IsPath Γ p) {q : Vh}
    (hq : p.head? = some (θ q)) :
    p.foldl (liftStep Γh θ) q = p'.foldl (liftStep Γh θ) q := by
  obtain ⟨-, hch⟩ := hp
  cases hm with
  | backDel l₁ l₂ w v h =>
    have hw := θ_foldl_liftStep_prefix hθ hch hq
    set q₁ := (l₁ ++ [w]).foldl (liftStep Γh θ) q
    have e1 : (l₁ ++ w :: v :: w :: l₂).foldl (liftStep Γh θ) q =
        (v :: w :: l₂).foldl (liftStep Γh θ) q₁ := by
      rw [show l₁ ++ w :: v :: w :: l₂ = (l₁ ++ [w]) ++ v :: w :: l₂ by simp, List.foldl_append]
    have e2 : (l₁ ++ w :: l₂).foldl (liftStep Γh θ) q = l₂.foldl (liftStep Γh θ) q₁ := by
      rw [show l₁ ++ w :: l₂ = (l₁ ++ [w]) ++ l₂ by simp, List.foldl_append]
    rw [e1, e2]
    have hs := liftStep_over hθ (q := q₁) (w := v) (by rw [hw]; exact h)
    simp only [List.foldl_cons]
    rw [show w = θ q₁ from hw.symm, liftStep_of_adj hθ hs.1.symm]
  | backIns l₁ l₂ w v h =>
    have hw := θ_foldl_liftStep_prefix hθ hch hq
    set q₁ := (l₁ ++ [w]).foldl (liftStep Γh θ) q
    have e1 : (l₁ ++ w :: v :: w :: l₂).foldl (liftStep Γh θ) q =
        (v :: w :: l₂).foldl (liftStep Γh θ) q₁ := by
      rw [show l₁ ++ w :: v :: w :: l₂ = (l₁ ++ [w]) ++ v :: w :: l₂ by simp, List.foldl_append]
    have e2 : (l₁ ++ w :: l₂).foldl (liftStep Γh θ) q = l₂.foldl (liftStep Γh θ) q₁ := by
      rw [show l₁ ++ w :: l₂ = (l₁ ++ [w]) ++ l₂ by simp, List.foldl_append]
    rw [e1, e2]
    have hs := liftStep_over hθ (q := q₁) (w := v) (by rw [hw]; exact h)
    simp only [List.foldl_cons]
    rw [show w = θ q₁ from hw.symm, liftStep_of_adj hθ hs.1.symm]
  | cycIns l₁ l₂ c w hc h₁ h₂ =>
    have hw := θ_foldl_liftStep_prefix hθ hch hq
    set q₁ := (l₁ ++ [w]).foldl (liftStep Γh θ) q
    obtain ⟨⟨c₁, rfl⟩, -⟩ := exists_cons_concat_of_head_last h₁ h₂
    have e1 : (l₁ ++ (w :: c₁) ++ l₂).foldl (liftStep Γh θ) q =
        l₂.foldl (liftStep Γh θ) (c₁.foldl (liftStep Γh θ) q₁) := by
      rw [show l₁ ++ (w :: c₁) ++ l₂ = (l₁ ++ [w]) ++ c₁ ++ l₂ by simp, List.foldl_append,
        List.foldl_append]
    have e2 : (l₁ ++ w :: l₂).foldl (liftStep Γh θ) q = l₂.foldl (liftStep Γh θ) q₁ := by
      rw [show l₁ ++ w :: l₂ = (l₁ ++ [w]) ++ l₂ by simp, List.foldl_append]
    rw [e1, e2]
    have hcl := (hC _ hc).2 w h₁ q₁ hw
    simp only [List.foldl_cons] at hcl
    rw [← hw, liftStep_self hθ] at hcl
    rw [hcl]
  | cycDel l₁ l₂ c w hc h₁ h₂ =>
    obtain ⟨⟨c₁, rfl⟩, -⟩ := exists_cons_concat_of_head_last h₁ h₂
    have hch' : (l₁ ++ w :: (c₁ ++ l₂)).IsChain Γ.Adj := by simpa using hch
    have hq' : (l₁ ++ w :: (c₁ ++ l₂)).head? = some (θ q) := by
      rw [← hq]; cases l₁ <;> simp
    have hw := θ_foldl_liftStep_prefix hθ hch' hq'
    set q₁ := (l₁ ++ [w]).foldl (liftStep Γh θ) q
    have e1 : (l₁ ++ (w :: c₁) ++ l₂).foldl (liftStep Γh θ) q =
        l₂.foldl (liftStep Γh θ) (c₁.foldl (liftStep Γh θ) q₁) := by
      rw [show l₁ ++ (w :: c₁) ++ l₂ = (l₁ ++ [w]) ++ c₁ ++ l₂ by simp, List.foldl_append,
        List.foldl_append]
    have e2 : (l₁ ++ w :: l₂).foldl (liftStep Γh θ) q = l₂.foldl (liftStep Γh θ) q₁ := by
      rw [show l₁ ++ w :: l₂ = (l₁ ++ [w]) ++ l₂ by simp, List.foldl_append]
    rw [e1, e2]
    have hcl := (hC _ hc).2 w h₁ q₁ hw
    simp only [List.foldl_cons] at hcl
    rw [← hw, liftStep_self hθ] at hcl
    rw [hcl]

theorem foldl_liftStep_moves (hθ : GraphCovering Γh Γ θ) {C : Set (List V)}
    (hC : ∀ c ∈ rotRev C, IsPath Γ c ∧
      ∀ w, c.head? = some w → ∀ q : Vh, θ q = w → c.foldl (liftStep Γh θ) q = q)
    {p p' : List V} (hm : Moves Γ C p p') (hp : IsPath Γ p) {q : Vh}
    (hq : p.head? = some (θ q)) :
    p.foldl (liftStep Γh θ) q = p'.foldl (liftStep Γh θ) q := by
  induction hm with
  | refl => rfl
  | tail hm₁ hm₂ ih =>
    rw [ih]
    have hpath := Moves.isPath (fun c hc => (hC c hc).1) hm₁ hp
    exact foldl_liftStep_elemMove hθ hC hm₂ hpath (by rw [← Moves.head?_eq hm₁, hq])

end CFSG.Quasithin.Asc94
