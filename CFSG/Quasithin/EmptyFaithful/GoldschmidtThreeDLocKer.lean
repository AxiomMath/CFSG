module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot
public import Mathlib.Data.List.Sort
import all Mathlib.Data.List.Sort

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

namespace GoldD3

@[expose] def insK (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insK a l

@[expose] def sortK : List ℕ → List ℕ
  | [] => []
  | a :: l => insK a (sortK l)

theorem insK_eq (a : ℕ) (l : List ℕ) : insK a l = l.orderedInsert (· ≤ ·) a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [insK, List.orderedInsert]
    split_ifs <;> simp_all

theorem sortK_eq (l : List ℕ) : sortK l = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show insK a (sortK l) = List.orderedInsert _ a (List.insertionSort _ l)
    rw [ih, insK_eq]

theorem sortN_eq_sortK (l : List ℕ) : sortN l = sortK l :=
  (List.mergeSort_eq_insertionSort (· ≤ ·) l).trans (sortK_eq l).symm

@[expose] def codeActK (n : ℕ) (t : Array ℕ) (c : ℕ) : ℕ :=
  encodeSet n (sortK ((decodeSet n c c).map fun p => t.getD p 0))

@[expose] def codeSetActK (n : ℕ) (t : Array ℕ) (L : List ℕ) : List ℕ :=
  sortK (L.map (codeActK n t))

theorem codeSetActK_eq (n : ℕ) : codeSetActK n = codeSetAct n := by
  funext t L
  unfold codeSetActK codeSetAct codeActK codeAct
  simp only [sortN_eq_sortK]

@[expose] def idTabK (n : ℕ) : Array ℕ := (List.range n).toArray

theorem idTabK_eq (n : ℕ) : idTabK n = idTab n := by
  unfold idTabK idTab
  rw [List.toArray_range]

@[expose] def powTabK (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idTabK n
  | k + 1 => compArr t (powTabK n t k)

theorem powTabK_eq (n : ℕ) (t : Array ℕ) (k : ℕ) : powTabK n t k = powTab n t k := by
  induction k with
  | zero => exact idTabK_eq n
  | succ k ih => simp only [powTabK, powTab, ih]

@[expose] def wordTabK (tabs : Array (Array ℕ)) (n : ℕ) (w : List ℕ) : Array ℕ :=
  (List.range n).toArray.map (wordImg tabs w)

theorem wordTabK_eq (tabs : Array (Array ℕ)) (n : ℕ) (w : List ℕ) :
    wordTabK tabs n w = wordTabA tabs n w := by
  unfold wordTabK wordTabA
  rw [List.toArray_range]

@[expose] def quotGtK (n : ℕ) (L : List (Array ℕ)) (x : QuotGen) : Array ℕ :=
  powTabK n (wordTabK L.toArray n x.w) x.k

@[expose] def quotGiK (n : ℕ) (L : List (Array ℕ)) (x : QuotGen) : Array ℕ :=
  powTabK n (quotGtK n L x) (x.m - 1)

theorem quotGtK_eq (n : ℕ) (L : List (Array ℕ)) (x : QuotGen) : quotGtK n L x = quotGt n L x := by
  simp only [quotGtK, quotGt, powTabK_eq, wordTabK_eq]

theorem quotGiK_eq (n : ℕ) (L : List (Array ℕ)) (x : QuotGen) : quotGiK n L x = quotGi n L x := by
  simp only [quotGiK, quotGi, powTabK_eq, quotGtK_eq]

section Omega

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

omit [Inhabited Lab] in
theorem distinctB_of_nodup {a : Array Lab} (h : a.toList.Nodup) : distinctB a = true := by
  have key : ∀ (l : List Lab) (f : Bool) (S : Std.HashSet Lab), f = true → l.Nodup →
      (∀ x ∈ l, S.contains x = false) → (l.foldl distinctStep (f, S)).1 = true := by
    intro l
    induction l with
    | nil => intro f S hf _ _; simpa using hf
    | cons x l ih =>
      intro f S hf hnd hS
      have hx : S.contains x = false := hS x List.mem_cons_self
      simp only [List.foldl_cons, distinctStep, hx]
      refine ih f _ hf (List.nodup_cons.1 hnd).2 fun y hy => ?_
      rw [Std.HashSet.contains_insert, hS y (List.mem_cons_of_mem _ hy)]
      have : y ≠ x := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hy)
      simp [Ne.symm this]
  unfold distinctB
  rw [← Array.foldl_toList]
  exact key a.toList true ∅ rfl h fun x _ => by simp

@[expose] def OmegaSpecK (act : Array ℕ → Lab → Lab) (letters : Array (Array ℕ)) (Δ : Lab)
    (O : OmegaData Lab) : Prop :=
  O.lbl[0]! = Δ ∧ 0 < O.lbl.size ∧
  (∀ l < letters.size, ∀ i < O.lbl.size,
    (O.pn[l]!)[i]! < O.lbl.size ∧ O.lbl[(O.pn[l]!)[i]!]! = act letters[l]! O.lbl[i]!) ∧
  (∀ i < O.lbl.size, 0 < i → O.par[i]! < i ∧ O.via[i]! < letters.size ∧
    (O.pn[O.via[i]!]!)[O.par[i]!]! = i) ∧
  O.lbl.toList.Nodup

instance (act : Array ℕ → Lab → Lab) (letters : Array (Array ℕ)) (Δ : Lab) (O : OmegaData Lab) :
    Decidable (OmegaSpecK act letters Δ O) := by
  unfold OmegaSpecK; infer_instance

theorem OmegaSpecK.spec {act : Array ℕ → Lab → Lab} {letters : Array (Array ℕ)} {Δ : Lab}
    {O : OmegaData Lab} (h : OmegaSpecK act letters Δ O) : OmegaSpec act letters Δ O :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, distinctB_of_nodup h.2.2.2.2⟩

end Omega

end GoldD3

end CFSG.Quasithin
