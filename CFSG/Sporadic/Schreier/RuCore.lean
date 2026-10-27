module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.Algebra.Pointwise.Stabilizer

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped Pointwise

@[expose] def evalSigned {G : Type*} [Group G] (gens : List G) : List ℤ → G
  | [] => 1
  | l :: w => (if 0 < l then gens.getD (l.natAbs - 1) 1 else (gens.getD (l.natAbs - 1) 1)⁻¹) *
      evalSigned gens w

theorem evalSigned_nil {G : Type*} [Group G] (gens : List G) : evalSigned gens [] = 1 := rfl

theorem evalSigned_cons {G : Type*} [Group G] (gens : List G) (l : ℤ) (w : List ℤ) :
    evalSigned gens (l :: w) =
      (if 0 < l then gens.getD (l.natAbs - 1) 1 else (gens.getD (l.natAbs - 1) 1)⁻¹) *
        evalSigned gens w := rfl

theorem evalSigned_append {G : Type*} [Group G] (gens : List G) (v w : List ℤ) :
    evalSigned gens (v ++ w) = evalSigned gens v * evalSigned gens w := by
  induction v with
  | nil => simp [evalSigned]
  | cons l v ih => rw [List.cons_append, evalSigned_cons, evalSigned_cons, ih, mul_assoc]

theorem evalSigned_mem {G : Type*} [Group G] {H : Subgroup G} {gens : List G}
    (hg : ∀ g ∈ gens, g ∈ H) (w : List ℤ) : evalSigned gens w ∈ H := by
  have hget : ∀ k, gens.getD k 1 ∈ H := fun k => by
    rw [List.getD_eq_getElem?_getD]
    cases h : gens[k]? with
    | none => exact H.one_mem
    | some g => exact hg g (List.mem_of_getElem? h)
  induction w with
  | nil => exact H.one_mem
  | cons l w ih =>
    rw [evalSigned_cons]
    refine H.mul_mem ?_ ih
    split
    · exact hget _
    · exact H.inv_mem (hget _)

theorem map_evalSigned {G H : Type*} [Group G] [Group H] (f : G →* H) (gens : List G)
    (w : List ℤ) : f (evalSigned gens w) = evalSigned (gens.map f) w := by
  induction w with
  | nil => simp [evalSigned]
  | cons l w ih =>
    rw [evalSigned_cons, evalSigned_cons, map_mul, ih]
    have hk : ∀ k, f (gens.getD k 1) = (gens.map f).getD k 1 := fun k => by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases gens[k]? <;> simp
    split
    · rw [hk]
    · rw [map_inv, hk]

theorem rep_wordA_evalSigned {n k : ℕ} {S Sinv : Array (Array ℕ)} {gens : List (Equiv.Perm (Fin n))}
    (hS : ∀ h < k, Rep n S[h]! (gens.getD h 1))
    (hSinv : ∀ h < k, Rep n Sinv[h]! (gens.getD h 1)⁻¹) :
    ∀ w : List ℤ, lettersOK k w = true → Rep n (wordA n S Sinv w) (evalSigned gens w)
  | [], _ => by simpa [wordA, evalSigned] using (rep_idA (n := n))
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlk⟩, hw⟩ := hw
    have hw' : lettersOK k w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    rw [wordA, evalSigned_cons]
    refine rep_compA ?_ (rep_wordA_evalSigned hS hSinv w hw')
    unfold letterA
    by_cases hpos : 0 < l
    · rw [ite_eq_left hpos, ite_eq_left hpos]
      have e : l.toNat - 1 = l.natAbs - 1 := by omega
      rw [e]
      exact hS _ (by omega)
    · rw [ite_eq_right hpos, ite_eq_right hpos]
      have e : (-l).toNat - 1 = l.natAbs - 1 := by omega
      rw [e]
      exact hSinv _ (by omega)

@[expose] def powA (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | e + 1 => compA n t (powA n t e)

theorem rep_powA {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    ∀ e, Rep n (powA n t e) (g ^ e)
  | 0 => by simpa [powA] using (rep_idA (n := n))
  | e + 1 => by
    rw [powA, pow_succ']
    exact rep_compA ht (rep_powA ht e)

inductive SlotRow where
  | mu (i j k : ℕ)
  | iv (i j : ℕ)
  | pwr (e i j : ℕ)

theorem lookup_cons_self {β : Type*} (k : ℕ) (b : β) (l : List (ℕ × β)) :
    List.lookup k ((k, b) :: l) = some b := by
  rw [List.lookup_cons, beq_self_eq_true]

theorem lookup_cons_ne {β : Type*} {k a : ℕ} (h : k ≠ a) (b : β) (l : List (ℕ × β)) :
    List.lookup k ((a, b) :: l) = List.lookup k l := by
  rw [List.lookup_cons, beq_eq_false_iff_ne.2 h]

@[expose] def slotRead {G : Type*} [Group G] (s : List (ℕ × G)) (k : ℕ) : G :=
  (s.lookup k).getD 1

@[expose] def slotStep {G : Type*} [Group G] (s : List (ℕ × G)) : SlotRow → List (ℕ × G)
  | .mu i j k => (k, slotRead s i * slotRead s j) :: s
  | .iv i j => (j, (slotRead s i)⁻¹) :: s
  | .pwr e i j => (j, slotRead s i ^ e) :: s

@[expose] def slotRun {G : Type*} [Group G] (rows : List SlotRow) (g₁ g₂ : G) : G × G :=
  let s := rows.foldl slotStep [(1, g₁), (2, g₂)]
  (slotRead s 1, slotRead s 2)

theorem map_slotRun {G H : Type*} [Group G] [Group H] (f : G →* H) (rows : List SlotRow)
    (g₁ g₂ : G) : (f (slotRun rows g₁ g₂).1, f (slotRun rows g₁ g₂).2) =
      slotRun rows (f g₁) (f g₂) := by
  have hread : ∀ (s : List (ℕ × G)) k, f (slotRead s k) =
      slotRead (s.map fun p => (p.1, f p.2)) k := by
    intro s k
    induction s with
    | nil => simp [slotRead]
    | cons p s ih =>
      obtain ⟨a, g⟩ := p
      by_cases h : k = a
      · subst h
        simp only [slotRead, List.map_cons, lookup_cons_self, Option.getD_some]
      · simp only [slotRead, List.map_cons, lookup_cons_ne h] at ih ⊢
        exact ih
  have hstep : ∀ (rows : List SlotRow) (s : List (ℕ × G)),
      (rows.foldl slotStep s).map (fun p => (p.1, f p.2)) =
        rows.foldl slotStep (s.map fun p => (p.1, f p.2)) := by
    intro rows
    induction rows with
    | nil => intro s; rfl
    | cons r rows ih =>
      intro s
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      cases r with
      | mu i j k => simp [slotStep, hread, map_mul]
      | iv i j => simp [slotStep, hread, map_inv]
      | pwr e i j => simp [slotStep, hread, map_pow]
  simp only [slotRun, hread, hstep]
  rfl

@[expose] def slotReadA (n : ℕ) (s : List (ℕ × Array ℕ)) (k : ℕ) : Array ℕ :=
  (s.lookup k).getD (idA n)

@[expose] def slotStepA (n : ℕ) (s : List (ℕ × Array ℕ) × Bool) : SlotRow →
    List (ℕ × Array ℕ) × Bool
  | .mu i j k => ((k, compA n (slotReadA n s.1 i) (slotReadA n s.1 j)) :: s.1, s.2)
  | .iv i j => ((j, invCand n (slotReadA n s.1 i)) :: s.1,
      s.2 && isInvA n (slotReadA n s.1 i) (invCand n (slotReadA n s.1 i)))
  | .pwr e i j => ((j, powA n (slotReadA n s.1 i) e) :: s.1, s.2)

@[expose] def slotFinalA (n : ℕ) (rows : List SlotRow) (t₁ t₂ : Array ℕ) :
    List (ℕ × Array ℕ) × Bool :=
  rows.foldl (slotStepA n) ([(1, t₁), (2, t₂)], true)

@[expose] def slotRunA (n : ℕ) (rows : List SlotRow) (t₁ t₂ : Array ℕ) :
    Array ℕ × Array ℕ × Bool :=
  let s := slotFinalA n rows t₁ t₂
  (slotReadA n s.1 1, slotReadA n s.1 2, s.2)

@[expose] def SlotRep (n : ℕ) (a : List (ℕ × Array ℕ)) (s : List (ℕ × Equiv.Perm (Fin n))) :
    Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ Rep n p.2 q.2) a s

theorem slotRep_read {n : ℕ} {a : List (ℕ × Array ℕ)} {s : List (ℕ × Equiv.Perm (Fin n))}
    (h : SlotRep n a s) (k : ℕ) : Rep n (slotReadA n a k) (slotRead s k) := by
  induction h with
  | nil => simpa [slotReadA, slotRead] using (rep_idA (n := n))
  | @cons p q a s hpq _ ih =>
    obtain ⟨pk, pv⟩ := p
    obtain ⟨qk, qv⟩ := q
    obtain ⟨hk1, hk2⟩ := hpq
    dsimp only at hk1 hk2
    subst hk1
    by_cases hk : k = pk
    · subst hk
      simp only [slotReadA, slotRead, lookup_cons_self, Option.getD_some]
      exact hk2
    · simp only [slotReadA, slotRead, lookup_cons_ne hk] at ih ⊢
      exact ih

theorem rep_slotRunA {n : ℕ} (rows : List SlotRow) {t₁ t₂ : Array ℕ}
    {g₁ g₂ : Equiv.Perm (Fin n)} (h₁ : Rep n t₁ g₁) (h₂ : Rep n t₂ g₂)
    (hflag : (slotRunA n rows t₁ t₂).2.2 = true) :
    Rep n (slotRunA n rows t₁ t₂).1 (slotRun rows g₁ g₂).1 ∧
      Rep n (slotRunA n rows t₁ t₂).2.1 (slotRun rows g₁ g₂).2 := by
  have key : ∀ (rows : List SlotRow) (a : List (ℕ × Array ℕ) × Bool)
      (s : List (ℕ × Equiv.Perm (Fin n))), SlotRep n a.1 s →
      (rows.foldl (slotStepA n) a).2 = true →
      SlotRep n (rows.foldl (slotStepA n) a).1 (rows.foldl slotStep s) := by
    intro rows
    induction rows with
    | nil => intro a s h _; exact h
    | cons r rows ih =>
      intro a s h hf
      rw [List.foldl_cons] at hf ⊢
      rw [List.foldl_cons]
      have hmono : ∀ (rows : List SlotRow) (b : List (ℕ × Array ℕ) × Bool),
          (rows.foldl (slotStepA n) b).2 = true → b.2 = true := by
        intro rows
        induction rows with
        | nil => intro b hb; exact hb
        | cons r' rows' ih' =>
          intro b hb
          rw [List.foldl_cons] at hb
          have := ih' _ hb
          cases r' <;> simp_all [slotStepA]
      have hstep := hmono rows _ hf
      refine ih _ _ ?_ hf
      cases r with
      | mu i j k =>
        exact List.Forall₂.cons ⟨rfl, rep_compA (slotRep_read h i) (slotRep_read h j)⟩ h
      | iv i j =>
        have hinv : isInvA n (slotReadA n a.1 i) (invCand n (slotReadA n a.1 i)) = true := by
          simp only [slotStepA, Bool.and_eq_true] at hstep
          exact hstep.2
        exact List.Forall₂.cons ⟨rfl, rep_inv_of_isInvA (slotRep_read h i) hinv⟩ h
      | pwr e i j =>
        exact List.Forall₂.cons ⟨rfl, rep_powA (slotRep_read h i) e⟩ h
  have h0 : SlotRep n ([(1, t₁), (2, t₂)] : List (ℕ × Array ℕ)) [(1, g₁), (2, g₂)] :=
    List.Forall₂.cons ⟨rfl, h₁⟩ (List.Forall₂.cons ⟨rfl, h₂⟩ List.Forall₂.nil)
  have hS := key rows _ _ h0 hflag
  exact ⟨slotRep_read hS 1, slotRep_read hS 2⟩

@[expose] def ptSet (n : ℕ) (Fl : Array ℕ) : Set (Fin n) :=
  {x | ∃ i < Fl.size, Fl[i]! = (x : ℕ)}

structure PtList (n : ℕ) (Fl : Array ℕ) : Prop where
  lt : ∀ i < Fl.size, Fl[i]! < n
  inj : ∀ i < Fl.size, ∀ j < Fl.size, Fl[i]! = Fl[j]! → i = j

theorem ptSet_finite (n : ℕ) (Fl : Array ℕ) : (ptSet n Fl).Finite := Set.toFinite _

@[expose] noncomputable def ptEquiv {n : ℕ} {Fl : Array ℕ} (h : PtList n Fl) :
    Fin Fl.size ≃ ptSet n Fl :=
  Equiv.ofBijective (fun i => ⟨⟨Fl[(i : ℕ)]!, h.lt i i.2⟩, i, i.2, rfl⟩)
    ⟨fun i j hij => Fin.ext (h.inj i i.2 j j.2 (congrArg (fun x : ptSet n Fl => (x : ℕ)) hij)),
      fun ⟨_, i, hi, hx⟩ => ⟨⟨i, hi⟩, Subtype.ext (Fin.ext hx)⟩⟩

theorem ptEquiv_apply_val {n : ℕ} {Fl : Array ℕ} (h : PtList n Fl) (i : Fin Fl.size) :
    (((ptEquiv h i : ptSet n Fl) : Fin n) : ℕ) = Fl[(i : ℕ)]! := rfl

@[expose] noncomputable def resHom {n : ℕ} {Fl : Array ℕ} (h : PtList n Fl) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) (ptSet n Fl) →* Equiv.Perm (Fin Fl.size) :=
  (Equiv.permCongrHom (ptEquiv h).symm).toMonoidHom.comp (MulAction.toPermHom _ _)

theorem resHom_apply_val {n : ℕ} {Fl : Array ℕ} (h : PtList n Fl)
    (g : MulAction.stabilizer (Equiv.Perm (Fin n)) (ptSet n Fl)) (i : Fin Fl.size) :
    Fl[((resHom h g i : Fin Fl.size) : ℕ)]! =
      ((g : Equiv.Perm (Fin n)) ⟨Fl[(i : ℕ)]!, h.lt i i.2⟩ : ℕ) := by
  rw [← ptEquiv_apply_val h]
  change ((((ptEquiv h) ((ptEquiv h).symm (g • ptEquiv h i)) : ptSet n Fl) : Fin n) : ℕ) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem mem_stabilizer_ptSet {n : ℕ} {Fl : Array ℕ} {g : Equiv.Perm (Fin n)}
    (hg : ∀ x ∈ ptSet n Fl, g x ∈ ptSet n Fl) :
    g ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) (ptSet n Fl) :=
  (MulAction.mem_stabilizer_set' (ptSet_finite n Fl)).2 fun x hx => hg x hx

@[expose] def resA (Fl pos g : Array ℕ) : Array ℕ :=
  Array.ofFn (n := Fl.size) fun i => pos[g[Fl[i.val]!]!]!

theorem rep_resA {n : ℕ} {Fl pos t : Array ℕ} (h : PtList n Fl)
    (hpos : ∀ i < Fl.size, pos[Fl[i]!]! = i) {G : Equiv.Perm (Fin n)}
    (ht : Rep n t G) (hG : G ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) (ptSet n Fl)) :
    Rep Fl.size (resA Fl pos t) (resHom h ⟨G, hG⟩) := by
  intro i
  rw [resA, getElem!_ofFn_nat _ i.2]
  have e : Fl[((resHom h ⟨G, hG⟩ i : Fin Fl.size) : ℕ)]! =
      ((G ⟨Fl[(i : ℕ)]!, h.lt i i.2⟩ : Fin n) : ℕ) := resHom_apply_val h ⟨G, hG⟩ i
  have ht' : t[Fl[(i : ℕ)]!]! = ((G ⟨Fl[(i : ℕ)]!, h.lt i i.2⟩ : Fin n) : ℕ) :=
    ht ⟨Fl[(i : ℕ)]!, h.lt i i.2⟩
  rw [ht', ← e]
  exact hpos _ (resHom h ⟨G, hG⟩ i).2

end CFSG.Sporadic.RuSchreier
