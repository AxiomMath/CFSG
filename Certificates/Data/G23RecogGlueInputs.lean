module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.G23RecogGluePresentationInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

def fwdTab : List (List ℕ) := [
  [1, 3, 5, 0, 10, 9, 14, 15, 8, 2, 13, 11, 19, 4, 16, 21, 6, 24, 25, 23, 20, 7, 22, 12, 27, 29, 26, 17, 28, 18, 30, 31],
  [0, 4, 2, 8, 11, 12, 6, 7, 13, 20, 10, 1, 22, 3, 21, 16, 26, 17, 18, 19, 23, 28, 5, 9, 29, 27, 15, 30, 14, 31, 25, 24],
  [2, 5, 6, 9, 12, 14, 0, 10, 20, 16, 19, 22, 21, 23, 1, 13, 3, 17, 18, 7, 26, 4, 28, 15, 24, 25, 8, 27, 11, 29, 30, 31],
  [0, 1, 7, 3, 4, 15, 17, 18, 8, 21, 10, 11, 16, 13, 24, 25, 27, 19, 2, 6, 28, 29, 26, 14, 23, 5, 30, 12, 31, 9, 22, 20],
  [0, 3, 6, 1, 13, 16, 2, 19, 11, 14, 10, 8, 15, 4, 9, 12, 5, 18, 17, 7, 28, 23, 26, 21, 29, 27, 22, 25, 20, 24, 30, 31],]

def bwdTab : List (List ℕ) := [
  [3, 0, 9, 1, 13, 2, 16, 21, 8, 5, 4, 11, 23, 10, 6, 7, 14, 27, 29, 12, 20, 15, 22, 19, 17, 18, 26, 24, 28, 25, 30, 31],
  [0, 11, 2, 13, 1, 22, 6, 7, 3, 23, 10, 4, 5, 8, 28, 26, 15, 17, 18, 19, 9, 14, 12, 20, 31, 30, 16, 25, 21, 24, 27, 29],
  [6, 14, 0, 16, 21, 1, 2, 19, 26, 3, 7, 28, 4, 15, 5, 23, 9, 17, 18, 10, 8, 12, 11, 13, 24, 25, 20, 27, 22, 29, 30, 31],
  [0, 1, 18, 3, 4, 25, 19, 2, 8, 29, 10, 11, 27, 13, 23, 5, 12, 6, 7, 17, 31, 9, 30, 24, 14, 15, 22, 16, 20, 21, 26, 28],
  [0, 3, 6, 1, 13, 16, 2, 19, 11, 14, 10, 8, 15, 4, 9, 12, 5, 18, 17, 7, 28, 23, 26, 21, 29, 27, 22, 25, 20, 24, 30, 31],]

def fwd (k : Fin 5) (i : Fin 32) : Fin 32 :=
  ⟨(fwdTab.getD k.val []).getD i.val 0 % 32, Nat.mod_lt _ (by norm_num)⟩

def bwd (k : Fin 5) (i : Fin 32) : Fin 32 :=
  ⟨(bwdTab.getD k.val []).getD i.val 0 % 32, Nat.mod_lt _ (by norm_num)⟩

theorem bwd_fwd : ∀ k : Fin 5, ∀ i : Fin 32, bwd k (fwd k i) = i := by decide +kernel

theorem fwd_bwd : ∀ k : Fin 5, ∀ i : Fin 32, fwd k (bwd k i) = i := by decide +kernel

def gen (k : Fin 5) : Equiv.Perm (Fin 32) := ⟨fwd k, bwd k, bwd_fwd k, fwd_bwd k⟩

@[expose] def Hc : Subgroup (Equiv.Perm (Fin 32)) := Subgroup.closure (Set.range gen)

section BFS

variable {α : Type*} [DecidableEq α]

def addOne (cap : ℕ) (mul : α → α → α) (x : α) (acc : List α × List α) (g : α) :
    List α × List α :=
  if acc.1.length < cap ∧ ¬ acc.1.contains (mul x g) then
    (acc.1 ++ [mul x g], acc.2 ++ [mul x g])
  else acc

def bfsStep (cap : ℕ) (mul : α → α → α) (gens : List α) (seen fr : List α) :
    List α × List α :=
  fr.foldl (fun acc x => gens.foldl (addOne cap mul x) acc) (seen, [])

def bfsAux (cap : ℕ) (mul : α → α → α) (gens : List α) : ℕ → List α → List α → List α
  | 0, seen, _ => seen
  | n + 1, seen, fr =>
    if fr.isEmpty then seen else
      let r := bfsStep cap mul gens seen fr
      bfsAux cap mul gens n r.1 r.2

end BFS

section Sound

variable {α : Type*} [DecidableEq α]

theorem addOne_sub (P : α → Prop) (cap : ℕ) (mul : α → α → α)
    (hmul : ∀ x g, P x → P g → P (mul x g)) (x g : α) (acc : List α × List α)
    (hx : P x) (hg : P g) (h1 : ∀ y ∈ acc.1, P y) (h2 : ∀ y ∈ acc.2, P y) :
    (∀ y ∈ (addOne cap mul x acc g).1, P y) ∧
      (∀ y ∈ (addOne cap mul x acc g).2, P y) := by
  unfold addOne
  split_ifs with h
  · have hy : P (mul x g) := hmul x g hx hg
    refine ⟨fun y hy' => ?_, fun y hy' => ?_⟩
    · rcases List.mem_append.mp hy' with h' | h'
      · exact h1 y h'
      · rw [List.mem_singleton.mp h']; exact hy
    · rcases List.mem_append.mp hy' with h' | h'
      · exact h2 y h'
      · rw [List.mem_singleton.mp h']; exact hy
  · exact ⟨h1, h2⟩

theorem gens_fold_sub (P : α → Prop) (cap : ℕ) (mul : α → α → α)
    (hmul : ∀ x g, P x → P g → P (mul x g)) (x : α) (hx : P x) :
    ∀ (gs : List α), (∀ g ∈ gs, P g) → ∀ (acc : List α × List α),
      (∀ y ∈ acc.1, P y) → (∀ y ∈ acc.2, P y) →
      (∀ y ∈ (gs.foldl (addOne cap mul x) acc).1, P y) ∧
        (∀ y ∈ (gs.foldl (addOne cap mul x) acc).2, P y) := by
  intro gs
  induction gs with
  | nil => intro _ acc h1 h2; exact ⟨h1, h2⟩
  | cons g gs ih =>
    intro hgs acc h1 h2
    simp only [List.foldl_cons]
    obtain ⟨h1', h2'⟩ :=
      addOne_sub P cap mul hmul x g acc hx (hgs g List.mem_cons_self) h1 h2
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ h1' h2'

theorem bfsFold_sub (P : α → Prop) (cap : ℕ) (mul : α → α → α)
    (hmul : ∀ x g, P x → P g → P (mul x g)) (gens : List α) (hgs : ∀ g ∈ gens, P g) :
    ∀ (fr : List α) (acc : List α × List α),
      (∀ y ∈ acc.1, P y) → (∀ y ∈ acc.2, P y) → (∀ x ∈ fr, P x) →
      (∀ y ∈ (fr.foldl (fun acc x => gens.foldl (addOne cap mul x) acc) acc).1, P y) ∧
        (∀ y ∈ (fr.foldl (fun acc x => gens.foldl (addOne cap mul x) acc) acc).2, P y) := by
  intro fr
  induction fr with
  | nil => intro acc h1 h2 _; exact ⟨h1, h2⟩
  | cons x fr ih =>
    intro acc h1 h2 hf
    simp only [List.foldl_cons]
    obtain ⟨h1', h2'⟩ :=
      gens_fold_sub P cap mul hmul x (hf x List.mem_cons_self) gens hgs acc h1 h2
    exact ih _ h1' h2' (fun y hy => hf y (List.mem_cons_of_mem _ hy))

theorem bfsStep_sub (P : α → Prop) (cap : ℕ) (mul : α → α → α)
    (hmul : ∀ x g, P x → P g → P (mul x g)) (gens : List α) (hgs : ∀ g ∈ gens, P g)
    (seen fr : List α) (hs : ∀ y ∈ seen, P y) (hf : ∀ y ∈ fr, P y) :
    (∀ y ∈ (bfsStep cap mul gens seen fr).1, P y) ∧
      (∀ y ∈ (bfsStep cap mul gens seen fr).2, P y) := by
  unfold bfsStep
  exact bfsFold_sub P cap mul hmul gens hgs fr (seen, []) hs
    (fun y hy => absurd hy (by simp)) hf

theorem bfsAux_sub (P : α → Prop) (cap : ℕ) (mul : α → α → α)
    (hmul : ∀ x g, P x → P g → P (mul x g)) (gens : List α) (hgs : ∀ g ∈ gens, P g) :
    ∀ (n : ℕ) (seen fr : List α), (∀ y ∈ seen, P y) → (∀ y ∈ fr, P y) →
      ∀ y ∈ bfsAux cap mul gens n seen fr, P y := by
  intro n
  induction n with
  | zero =>
    intro seen _ hs _ y hy
    simp only [bfsAux] at hy
    exact hs y hy
  | succ n ih =>
    intro seen fr hs hf y hy
    simp only [bfsAux] at hy
    split_ifs at hy with hfe
    · exact hs y hy
    · exact ih _ _ (bfsStep_sub P cap mul hmul gens hgs seen fr hs hf).1
        (bfsStep_sub P cap mul hmul gens hgs seen fr hs hf).2 y hy

end Sound

def Lst (σ : Equiv.Perm (Fin 32)) : List ℕ := List.ofFn (fun i => (σ i : ℕ))

def mulL (x g : List ℕ) : List ℕ := g.map (fun j => x.getD j 0)

def idL : List ℕ := Lst 1

def gensL : List (List ℕ) :=
  List.ofFn (fun k => Lst (gen k)) ++ List.ofFn (fun k => Lst (gen k)⁻¹)

def elts : List (List ℕ) := bfsAux 576 mulL gensL 600 [idL] [idL]

theorem getD_ofFn_perm (σ : Equiv.Perm (Fin 32)) (j : Fin 32) :
    (List.ofFn fun i : Fin 32 => (σ i : ℕ)).getD j.val 0 = (σ j : ℕ) := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn, Fin.eta]

theorem Lst_mul (σ τ : Equiv.Perm (Fin 32)) : Lst (σ * τ) = mulL (Lst σ) (Lst τ) := by
  simp only [Lst, mulL, List.map_ofFn, Function.comp_def, Equiv.Perm.mul_apply, getD_ofFn_perm]

theorem Lst_injective : Function.Injective Lst := by
  intro σ τ h
  have h' : (fun i : Fin 32 => (σ i : ℕ)) = (fun i : Fin 32 => (τ i : ℕ)) :=
    List.ofFn_injective h
  apply Equiv.ext
  intro i
  apply Fin.ext
  exact congrFun h' i

theorem gen_mem_gensL (k : Fin 5) : Lst (gen k) ∈ gensL :=
  List.mem_append_left _ (List.mem_ofFn.mpr (Set.mem_range_self k))

theorem inv_gen_mem_gensL (k : Fin 5) : Lst (gen k)⁻¹ ∈ gensL :=
  List.mem_append_right _ (List.mem_ofFn.mpr (Set.mem_range_self k))

theorem glue_idL_eq : idL = Lst 1 := by decide +kernel

theorem elts_sound : ∀ l ∈ elts, ∃ σ ∈ Hc, Lst σ = l := by
  have hmul : ∀ x g, (∃ σ ∈ Hc, Lst σ = x) → (∃ τ ∈ Hc, Lst τ = g) →
      ∃ ρ ∈ Hc, Lst ρ = mulL x g := by
    rintro x g ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, Subgroup.mul_mem _ hσ hτ, Lst_mul σ τ⟩
  have hgs : ∀ g ∈ gensL, ∃ τ ∈ Hc, Lst τ = g := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
      exact ⟨gen k, Subgroup.subset_closure (Set.mem_range_self k), rfl⟩
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
      exact ⟨(gen k)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self k)), rfl⟩
  have hs : ∀ y ∈ [idL], ∃ σ ∈ Hc, Lst σ = y := by
    intro y hy
    rw [List.mem_singleton.mp hy]
    exact ⟨1, Subgroup.one_mem _, rfl⟩
  intro l hl
  exact bfsAux_sub (fun l => ∃ σ ∈ Hc, Lst σ = l) 576 mulL hmul gensL hgs 600 [idL] [idL] hs hs
    l hl

open CFSG.CosetTable

theorem len5 : (subsetOf 6 [0, 1, 2, 3, 4]).length = 5 := by decide

def f5 (i : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) : Equiv.Perm (Fin 32) :=
  gen (Fin.cast len5 i)

theorem g23H5_rel : ∀ r ∈ g23H5, (r.map fun x => cond x.2 (f5 x.1) (f5 x.1)⁻¹).prod = 1 := by
  decide +kernel

theorem range_f5 : Set.range f5 = Set.range gen := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast len5 i, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k.val, by rw [len5]; exact k.isLt⟩, rfl⟩

end CFSG.GH74.QTGen4.Recog.G23
