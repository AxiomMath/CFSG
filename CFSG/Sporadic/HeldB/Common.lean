module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native Pointwise

variable {n : ℕ}

@[expose] def permOfCheck (n : ℕ) (t r : Array ℕ) (h : isInvA n t r = true ∧ isInvA n r t = true) :
    Equiv.Perm (Fin n) where
  toFun i := ⟨t[i.val]!, (isInvA_spec h.1 i.2).1⟩
  invFun i := ⟨r[i.val]!, (isInvA_spec h.2 i.2).1⟩
  left_inv i := Fin.ext (isInvA_spec h.1 i.2).2
  right_inv i := Fin.ext (isInvA_spec h.2 i.2).2

@[expose, irreducible] def permOrId (n : ℕ) (t : Array ℕ) : Equiv.Perm (Fin n) :=
  if h : isInvA n t (invCand n t) = true ∧ isInvA n (invCand n t) t = true then
    permOfCheck n t (invCand n t) h
  else 1

theorem rep_permOrId {t : Array ℕ}
    (h : isInvA n t (invCand n t) = true ∧ isInvA n (invCand n t) t = true) :
    Rep n t (permOrId n t) := fun x => by
  rw [permOrId, dite_eq_left h]
  rfl

theorem permOrId_eq_permOfArr {t : Array ℕ}
    (h : isInvA n t (invCand n t) = true ∧ isInvA n (invCand n t) t = true) :
    permOrId n t = permOfArr n t :=
  (rep_permOrId h).unique (rep_permOfArr h.1).1

@[expose, irreducible] noncomputable def evalSignedWord (gs : List (Equiv.Perm (Fin n)))
    (w : List ℤ) : Equiv.Perm (Fin n) :=
  if lettersOK gs.length w = true then
    Quiver.SchreierGraph.evalWord (fun h : Fin gs.length => gs.get h) (toLetters gs.length w)
  else 1

theorem rep_wordA_evalSignedWord {gs : List (Equiv.Perm (Fin n))} {S Sinv : Array (Array ℕ)}
    (hS : ∀ h < gs.length, Rep n S[h]! (gs.getD h 1))
    (hSinv : ∀ h < gs.length, Rep n Sinv[h]! (gs.getD h 1)⁻¹) {w : List ℤ}
    (hw : lettersOK gs.length w = true) : Rep n (wordA n S Sinv w) (evalSignedWord gs w) := by
  rw [evalSignedWord, ite_eq_left hw]
  have h := rep_wordA (gs := fun h => gs.getD h 1) hS hSinv w hw
  convert h using 2
  funext h
  simp [List.getD_eq_getElem?_getD]

theorem evalSignedWord_mem {gs : List (Equiv.Perm (Fin n))} (H : Subgroup (Equiv.Perm (Fin n)))
    (hgs : ∀ g ∈ gs, g ∈ H) (w : List ℤ) : evalSignedWord gs w ∈ H := by
  rw [evalSignedWord]
  split_ifs
  · exact (Subgroup.closure_le H).2 (by
      rintro _ ⟨h, rfl⟩
      exact hgs _ (List.get_mem gs h))
      (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  · exact H.one_mem

@[expose] def permChk (n : ℕ) (t : Array ℕ) : Bool :=
  isInvA n t (invCand n t) && isInvA n (invCand n t) t

@[expose] def fixListOK (n m : ℕ) (t F : Array ℕ) : Bool :=
  F.size == m && allLt m (fun k => decide (F[k]! < n) && t[F[k]!]! == F[k]!) &&
    allLt (m - 1) (fun k => decide (F[k]! < F[k + 1]!)) &&
    (List.range n).countP (fun i => t[i]! == i) == m

@[expose] def agreeOK (m : ℕ) (g F σ : Array ℕ) : Bool :=
  allLt m fun k => g[F[k]!]! == F[σ[k]!]!

@[expose] def listPt (n : ℕ) [NeZero n] (F : Array ℕ) {m : ℕ} (k : Fin m) : Fin n :=
  ⟨F[k.val]! % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem permChk_spec {t : Array ℕ} (h : permChk n t = true) :
    Rep n t (permOrId n t) ∧ Rep n (invCand n t) (permOrId n t)⁻¹ := by
  have h' : isInvA n t (invCand n t) = true ∧ isInvA n (invCand n t) t = true := by
    simpa [permChk] using h
  exact ⟨rep_permOrId h', rep_inv_of_isInvA (rep_permOrId h') h'.1⟩

theorem fixListOK_parts {m : ℕ} {t F : Array ℕ} (h : fixListOK n m t F = true) :
    F.size = m ∧ (∀ k < m, F[k]! < n ∧ t[F[k]!]! = F[k]!) ∧
      (∀ k < m - 1, F[k]! < F[k + 1]!) ∧ (List.range n).countP (fun i => t[i]! == i) = m := by
  simp only [fixListOK, Bool.and_eq_true, beq_iff_eq, allLt_iff, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem fixListOK_lt_of_lt {m : ℕ} {t F : Array ℕ} (h : fixListOK n m t F = true) :
    ∀ d k, k + d + 1 < m → F[k]! < F[k + d + 1]! := by
  have hc := (fixListOK_parts h).2.2.1
  intro d
  induction d with
  | zero => intro k hk; exact hc k (by omega)
  | succ d ih =>
    intro k hk
    exact (ih k (by omega)).trans (hc (k + d + 1) (by omega))

theorem listPt_injective [NeZero n] {m : ℕ} {t F : Array ℕ} (h : fixListOK n m t F = true) :
    Function.Injective (listPt n F (m := m)) := by
  have hlt := (fixListOK_parts h).2.1
  have hmono := fixListOK_lt_of_lt h
  intro k l hkl
  have e : F[k.val]! = F[l.val]! := by
    have := congrArg Fin.val hkl
    simp only [listPt] at this
    rwa [Nat.mod_eq_of_lt (hlt k k.2).1, Nat.mod_eq_of_lt (hlt l l.2).1] at this
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hkl' | hkl'
  · have := hmono (l.val - k.val - 1) k.val (by omega)
    rw [show k.val + (l.val - k.val - 1) + 1 = l.val by omega] at this
    omega
  · have := hmono (k.val - l.val - 1) l.val (by omega)
    rw [show l.val + (k.val - l.val - 1) + 1 = k.val by omega] at this
    omega

theorem listPt_val [NeZero n] {m : ℕ} {t F : Array ℕ} (h : fixListOK n m t F = true)
    (k : Fin m) : (listPt n F k : ℕ) = F[k.val]! := by
  simp only [listPt]
  exact Nat.mod_eq_of_lt ((fixListOK_parts h).2.1 k k.2).1

theorem fixListOK_range [NeZero n] {m : ℕ} {t F : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : Rep n t g) (h : fixListOK n m t F = true) :
    Set.range (listPt n F (m := m)) = {x | g x = x} := by
  classical
  obtain ⟨-, hfix, -, hcount⟩ := fixListOK_parts h
  have hsub : Set.range (listPt n F (m := m)) ⊆ {x | g x = x} := by
    rintro _ ⟨k, rfl⟩
    apply Fin.ext
    rw [← ht, listPt_val h]
    exact (hfix k k.2).2
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.ncard_range_of_injective (listPt_injective h), Nat.card_fin]
  have e : {x : Fin n | g x = x} = ↑(Finset.univ.filter fun x : Fin n => g x = x) := by
    ext x
    simp
  rw [e, Set.ncard_coe_finset, ← hcount]
  have e2 : (List.range n).countP (fun i => t[i]! == i) =
      (List.finRange n).countP (fun x : Fin n => decide (g x = x)) := by
    rw [← List.map_coe_finRange_eq_range, List.countP_map]
    congr 1
    funext x
    simp only [Function.comp_apply, ht x]
    exact Bool.eq_iff_iff.2 (by simp [Fin.ext_iff])
  rw [e2, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    ((List.nodup_finRange n).filter _), List.toFinset_filter, List.toFinset_finRange]
  simp

theorem agreeOK_spec [NeZero n] {m : ℕ} {t' : Array ℕ} {g F σ : Array ℕ}
    {gp : Equiv.Perm (Fin n)} {σp : Equiv.Perm (Fin m)} (hF : fixListOK n m t' F = true)
    (hg : Rep n g gp) (hσ : Rep m σ σp) (h : agreeOK m g F σ = true) (k : Fin m) :
    gp (listPt n F k) = listPt n F (σp k) := by
  apply Fin.ext
  rw [← hg, listPt_val hF, listPt_val hF, ← hσ k]
  simp only [agreeOK, allLt_iff, beq_iff_eq] at h
  exact h k k.2

theorem listPt_val_of_lt [NeZero n] {m : ℕ} {F : Array ℕ} (h : ∀ k < m, F[k]! < n) (k : Fin m) :
    (listPt n F k : ℕ) = F[k.val]! := by
  simp only [listPt]
  exact Nat.mod_eq_of_lt (h k k.2)

theorem listPt_injective_of_inc [NeZero n] {m : ℕ} {F : Array ℕ} (hlt : ∀ k < m, F[k]! < n)
    (hinc : ∀ k < m - 1, F[k]! < F[k + 1]!) : Function.Injective (listPt n F (m := m)) := by
  have hmono : ∀ d k, k + d + 1 < m → F[k]! < F[k + d + 1]! := by
    intro d
    induction d with
    | zero => intro k hk; exact hinc k (by omega)
    | succ d ih =>
      intro k hk
      exact (ih k (by omega)).trans (hinc (k + d + 1) (by omega))
  intro k l hkl
  have e : F[k.val]! = F[l.val]! := by
    rw [← listPt_val_of_lt hlt k, ← listPt_val_of_lt hlt l, hkl]
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hkl' | hkl'
  · have := hmono (l.val - k.val - 1) k.val (by omega)
    rw [show k.val + (l.val - k.val - 1) + 1 = l.val by omega] at this
    omega
  · have := hmono (k.val - l.val - 1) l.val (by omega)
    rw [show l.val + (k.val - l.val - 1) + 1 = k.val by omega] at this
    omega

theorem agreeOK_spec_of_lt [NeZero n] {m : ℕ} {g F σ : Array ℕ}
    {gp : Equiv.Perm (Fin n)} {σp : Equiv.Perm (Fin m)} (hlt : ∀ k < m, F[k]! < n)
    (hg : Rep n g gp) (hσ : Rep m σ σp) (h : agreeOK m g F σ = true) (k : Fin m) :
    gp (listPt n F k) = listPt n F (σp k) := by
  apply Fin.ext
  rw [← hg, listPt_val_of_lt hlt, listPt_val_of_lt hlt, ← hσ k]
  simp only [agreeOK, allLt_iff, beq_iff_eq] at h
  exact h k k.2

section Literal

variable {α β : Type*}

theorem arr2_get0 [Inhabited α] (a b : α) : #[a, b][0]! = a := rfl

theorem arr2_get1 [Inhabited α] (a b : α) : #[a, b][1]! = b := rfl

theorem arr3_get0 [Inhabited α] (a b c : α) : #[a, b, c][0]! = a := rfl

theorem arr3_get1 [Inhabited α] (a b c : α) : #[a, b, c][1]! = b := rfl

theorem arr3_get2 [Inhabited α] (a b c : α) : #[a, b, c][2]! = c := rfl

theorem arr2_map_get0 [Inhabited β] (f : α → β) (a b : α) : (#[a, b].map f)[0]! = f a := by
  simp

theorem arr2_map_get1 [Inhabited β] (f : α → β) (a b : α) : (#[a, b].map f)[1]! = f b := by
  simp

theorem arr3_map_get0 [Inhabited β] (f : α → β) (a b c : α) :
    (#[a, b, c].map f)[0]! = f a := by
  simp

theorem arr3_map_get1 [Inhabited β] (f : α → β) (a b c : α) :
    (#[a, b, c].map f)[1]! = f b := by
  simp

theorem arr3_map_get2 [Inhabited β] (f : α → β) (a b c : α) :
    (#[a, b, c].map f)[2]! = f c := by
  simp

theorem list2_getD0 (a b d : α) : [a, b].getD 0 d = a := rfl

theorem list2_getD1 (a b d : α) : [a, b].getD 1 d = b := rfl

theorem list3_getD0 (a b c d : α) : [a, b, c].getD 0 d = a := rfl

theorem list3_getD1 (a b c d : α) : [a, b, c].getD 1 d = b := rfl

theorem list3_getD2 (a b c d : α) : [a, b, c].getD 2 d = c := rfl

end Literal

section Restrict

variable {N m : ℕ} {δ : Fin m → Fin N}

theorem mem_stabilizer_of_agree {g : Equiv.Perm (Fin N)} {σ : Equiv.Perm (Fin m)}
    (h : ∀ k, g (δ k) = δ (σ k)) :
    g ∈ MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ) := by
  rw [MulAction.mem_stabilizer_set_iff_smul_set_subset (Set.finite_range δ)]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨σ k, (h k).symm⟩

@[expose] noncomputable def restrictHom (hδ : Function.Injective δ)
    (H : Subgroup (Equiv.Perm (Fin N)))
    (hH : H ≤ MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ)) :
    H →* Equiv.Perm (Fin m) :=
  ((Equiv.ofInjective δ hδ).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ))
      (Set.range δ))).comp (Subgroup.inclusion hH)

theorem restrictHom_apply (hδ : Function.Injective δ) {H : Subgroup (Equiv.Perm (Fin N))}
    (hH : H ≤ MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ)) (h : H) (k : Fin m) :
    δ (restrictHom hδ H hH h k) = (h : Equiv.Perm (Fin N)) (δ k) := by
  have e := Equiv.apply_ofInjective_symm hδ
    ⟨(h : Equiv.Perm (Fin N)) (δ k), (hH h.2).symm ▸ ⟨δ k, ⟨k, rfl⟩, rfl⟩⟩
  exact e

theorem restrictHom_eq_of_agree (hδ : Function.Injective δ) {H : Subgroup (Equiv.Perm (Fin N))}
    (hH : H ≤ MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ)) (h : H)
    {σ : Equiv.Perm (Fin m)} (hσ : ∀ k, (h : Equiv.Perm (Fin N)) (δ k) = δ (σ k)) :
    restrictHom hδ H hH h = σ := by
  ext k
  exact congrArg Fin.val (hδ ((restrictHom_apply hδ hH h k).trans (hσ k)))

theorem restrictHom_eq_one_iff (hδ : Function.Injective δ) {H : Subgroup (Equiv.Perm (Fin N))}
    (hH : H ≤ MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ)) (h : H) :
    restrictHom hδ H hH h = 1 ↔ ∀ k, (h : Equiv.Perm (Fin N)) (δ k) = δ k := by
  constructor
  · intro h1 k
    rw [← restrictHom_apply hδ hH h k, h1]
    rfl
  · intro h1
    exact restrictHom_eq_of_agree hδ hH h (σ := 1) fun k => h1 k

theorem restrictHom_range (hδ : Function.Injective δ) {H : Subgroup (Equiv.Perm (Fin N))}
    (hH : H ≤ MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ))
    {gens : Set (Equiv.Perm (Fin N))} (hgen : H = Subgroup.closure gens) :
    (restrictHom hδ H hH).range =
      Subgroup.closure ((restrictHom hδ H hH) '' {h : H | (h : Equiv.Perm (Fin N)) ∈ gens}) := by
  rw [MonoidHom.range_eq_map, ← MonoidHom.map_closure]
  congr 1
  rw [eq_comm, Subgroup.eq_top_iff']
  intro h
  have hmem : (h : Equiv.Perm (Fin N)) ∈ Subgroup.closure gens := hgen ▸ h.2
  have : Subgroup.closure gens ≤
      (Subgroup.closure {h : H | (h : Equiv.Perm (Fin N)) ∈ gens}).map H.subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    have hgH : g ∈ H := hgen ▸ Subgroup.subset_closure hg
    exact ⟨⟨g, hgH⟩, Subgroup.subset_closure hg, rfl⟩
  obtain ⟨k, hk, hkh⟩ := this hmem
  have : k = h := Subtype.ext hkh
  rwa [← this]

end Restrict

end CFSG.Sporadic.HeldB
