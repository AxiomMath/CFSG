module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTBridge
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTRoots

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

private theorem dot_ofFn (γ γ' : Fin Tag.E6.rank → ℤ) :
    dot (List.ofFn γ) (List.ofFn γ') = ∑ i : Fin Tag.E6.rank, γ i * γ' i := by
  rw [dot]
  have h : List.zipWith (fun x1 x2 => x1 * x2) (List.ofFn γ) (List.ofFn γ') =
      List.ofFn (fun i : Fin Tag.E6.rank => γ i * γ' i) := by
    apply List.ext_getElem
    · simp [List.length_zipWith]
    · intro i h1 h2
      simp only [List.getElem_zipWith, List.getElem_ofFn]
  rw [h, List.sum_ofFn]

private theorem ofFn_getD (x : Vec) (hx : x.length = 6) :
    List.ofFn (fun i : Fin Tag.E6.rank => x.getD i.val 0) = x := by
  apply List.ext_getElem
  · rw [List.length_ofFn, hx]
    rfl
  · intro i h1 h2
    rw [List.getElem_ofFn]
    simpa using List.getD_eq_getElem (l := x) (n := i) (d := 0) h2

private theorem chi_apply (x : Vec) (γ : Fin Tag.E6.rank → ℤ) :
    e6Chi (vecZ x) (Multiplicative.ofAdd γ) =
      Multiplicative.ofAdd
        (∑ k : Fin Tag.E6.rank, ((γ k : ℤ) : ZMod 3) * ((x.getD k.val 0 : ℤ) : ZMod 3)) :=
  rfl

private theorem getD_ofFn (γ : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    (List.ofFn γ).getD i.val 0 = γ i := by
  rw [List.getD_eq_getElem (l := List.ofFn γ) (n := i.val) (d := 0) (by simp)]
  rw [List.getElem_ofFn]

private theorem length_ofFn_six (γ : Fin Tag.E6.rank → ℤ) : (List.ofFn γ).length = 6 := by
  rw [List.length_ofFn]
  rfl

private theorem ofFn_getD_any {α : Type*} (x : List α) (hx : x.length = 6) (d : α) :
    List.ofFn (fun i : Fin Tag.E6.rank => x.getD i.val d) = x := by
  apply List.ext_getElem
  · rw [List.length_ofFn, hx]
    rfl
  · intro i h1 h2
    rw [List.getElem_ofFn]
    simpa using List.getD_eq_getElem (l := x) (n := i) (d := d) h2

private theorem cartan_getD (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan i j = (cartan.getD i.val []).getD j.val 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem cartan_getD_length (i : Fin Tag.E6.rank) :
    (cartan.getD i.val []).length = 6 := by
  fin_cases i <;> decide +kernel

private theorem lib_iform_of_getD (a b : Vec) (ha : a.length = 6) (hb : b.length = 6) :
    CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6)
      (fun i : Fin Tag.E6.rank => a.getD i.val 0)
      (fun i : Fin Tag.E6.rank => b.getD i.val 0) = iform a b := by
  set fa : Fin Tag.E6.rank → ℤ := fun i => a.getD i.val 0 with hfa
  set fb : Fin Tag.E6.rank → ℤ := fun i => b.getD i.val 0 with hfb
  have ha' : List.ofFn fa = a := by rw [hfa]; exact ofFn_getD a ha
  have hb' : List.ofFn fb = b := by rw [hfb]; exact ofFn_getD b hb
  have hlib : CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) fa fb =
      ∑ i : Fin Tag.E6.rank, ∑ j : Fin Tag.E6.rank, fa i * Tag.E6.cartan i j * fb j := by
    simp only [CFSG.LieType.Steinberg.Adjoint.iform, Tag.symmetrizedCartan, Tag.symmetrizer,
      Matrix.one_mul]
  have hmap : cartan.map (dot (List.ofFn fb)) =
      List.ofFn (fun i : Fin Tag.E6.rank => dot (List.ofFn fb) (cartan.getD i.val [])) := by
    have hc : cartan = List.ofFn (fun i : Fin Tag.E6.rank => cartan.getD i.val []) :=
      ofFn_getD_any cartan (by rfl) []
    rw [hc, List.map_ofFn]
    rfl
  have h2 : ∀ i : Fin Tag.E6.rank,
      dot (List.ofFn fb) (cartan.getD i.val []) =
        ∑ j : Fin Tag.E6.rank, fb j * Tag.E6.cartan i j := by
    intro i
    conv_lhs => rw [← ofFn_getD_any (cartan.getD i.val []) (cartan_getD_length i) 0]
    rw [dot_ofFn]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cartan_getD]
  have hchk : iform (List.ofFn fa) (List.ofFn fb) =
      ∑ i : Fin Tag.E6.rank, fa i * (∑ j : Fin Tag.E6.rank, fb j * Tag.E6.cartan i j) := by
    rw [iform, hmap, dot_ofFn]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2 i]
  rw [← ha', ← hb', hlib, hchk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem lib_iform_of_list (γ γ' : Fin Tag.E6.rank → ℤ) :
    CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) γ γ' =
      iform (List.ofFn γ) (List.ofFn γ') := by
  have hγ : γ = fun i : Fin Tag.E6.rank => (List.ofFn γ).getD i.val 0 := by
    funext i; rw [getD_ofFn]
  have hγ' : γ' = fun i : Fin Tag.E6.rank => (List.ofFn γ').getD i.val 0 := by
    funext i; rw [getD_ofFn]
  conv_lhs => rw [hγ, hγ']
  exact lib_iform_of_getD (List.ofFn γ) (List.ofFn γ')
    (length_ofFn_six γ) (length_ofFn_six γ')

private theorem symm_symm (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan i j = Tag.E6.symmetrizedCartan j i := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem lib_iform_comm (γ γ' : Fin Tag.E6.rank → ℤ) :
    CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) γ γ' =
      CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) γ' γ := by
  simp only [CFSG.LieType.Steinberg.Adjoint.iform]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [symm_symm b a]
  ring

private theorem iform_ofFn_comm (γ γ' : Fin Tag.E6.rank → ℤ) :
    iform (List.ofFn γ) (List.ofFn γ') = iform (List.ofFn γ') (List.ofFn γ) := by
  rw [← lib_iform_of_list γ γ', ← lib_iform_of_list γ' γ]
  exact lib_iform_comm γ γ'

private def classesDataK (cl : List (List Vec)) : Bool :=
  cl.all fun l => (l.dedup.length == l.length) && (l.all fun x => x.length == 6) && !l.isEmpty

private def classesSubK (K : List Vec) (cl : List (List Vec)) : Bool :=
  cl.all fun l => l.all fun x => K.contains x

private def classesClosedK (K : List Vec) (cl : List (List Vec)) : Bool :=
  cl.all fun l => l.all fun x => K.all fun y => !(iform x y != 0) || l.contains y

private def classesCoverK (K : List Vec) (cl : List (List Vec)) : Bool :=
  K.all fun x => cl.any fun l => l.contains x

private def cstep (K : List Vec) (a : Vec) (p : List Vec × List Vec) :
    List Vec × List Vec :=
  K.foldl (fun p b =>
    if p.1.contains b || p.2.contains b then p
    else if iform a b != 0 then (p.1, p.2 ++ [b]) else p) p

private theorem classStep_eq (K acc frontier : List Vec) :
    classStep K acc frontier = (frontier.foldl (fun p a => cstep K a p) (acc, [])).2 := rfl

private theorem classAux_succ (fuel : Nat) (K acc frontier : List Vec) :
    classAux (fuel + 1) K acc frontier =
      (if (classStep K acc frontier).isEmpty then acc
       else classAux fuel K (acc ++ classStep K acc frontier) (classStep K acc frontier)) := rfl

private theorem classes_facts_repA2 :
    classesDataK (classes repA2) = true ∧
    classesSubK (kerRoots repA2) (classes repA2) = true ∧
    classesClosedK (kerRoots repA2) (classes repA2) = true ∧
    classesCoverK (kerRoots repA2) (classes repA2) = true := by
  decide +kernel

private theorem classes_facts_repA4A1 :
    classesDataK (classes repA4A1) = true ∧
    classesSubK (kerRoots repA4A1) (classes repA4A1) = true ∧
    classesClosedK (kerRoots repA4A1) (classes repA4A1) = true ∧
    classesCoverK (kerRoots repA4A1) (classes repA4A1) = true := by
  decide +kernel

private theorem classes_facts_repD4 :
    classesDataK (classes repD4) = true ∧
    classesSubK (kerRoots repD4) (classes repD4) = true ∧
    classesClosedK (kerRoots repD4) (classes repD4) = true ∧
    classesCoverK (kerRoots repD4) (classes repD4) = true := by
  decide +kernel

private theorem classes_facts_repA5 :
    classesDataK (classes repA5) = true ∧
    classesSubK (kerRoots repA5) (classes repA5) = true ∧
    classesClosedK (kerRoots repA5) (classes repA5) = true ∧
    classesCoverK (kerRoots repA5) (classes repA5) = true := by
  decide +kernel

private def xD5 : Vec := (kerRoots repD5).headD []

private def new0D5 : List Vec := classStep (kerRoots repD5) [xD5] [xD5]

private def new1aD5 : List Vec :=
  [[0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, 0, -1, 0, 0], [0, 0, 0, 1, 1, 0],
   [0, -1, 0, -1, 0, 0], [0, 1, 0, 1, 1, 0], [0, 0, 0, -1, -1, 0], [0, -1, 0, -1, -1, 0],
   [1, 1, 2, 2, 1, 0], [-1, -1, -2, -2, -1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0],
   [0, -1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0]]

private def lD5 : List Vec := xD5 :: new0D5 ++ new1aD5

private theorem kerRoots_repD5_length : (kerRoots repD5).length = 40 := by
  decide +kernel

private theorem classStep_repD5_1 :
    classStep (kerRoots repD5) ([xD5] ++ new0D5) new0D5 = new1aD5 := by
  rw [classStep_eq, ← List.take_append_drop 13 new0D5, List.foldl_append]
  rw [show (new0D5.take 13).foldl (fun p a => cstep (kerRoots repD5) a p)
      ([xD5] ++ (new0D5.take 13 ++ new0D5.drop 13), []) =
      ([xD5] ++ (new0D5.take 13 ++ new0D5.drop 13), new1aD5) from by decide +kernel]
  rw [show (new0D5.drop 13).foldl (fun p a => cstep (kerRoots repD5) a p)
      ([xD5] ++ (new0D5.take 13 ++ new0D5.drop 13), new1aD5) =
      ([xD5] ++ (new0D5.take 13 ++ new0D5.drop 13), new1aD5) from by decide +kernel]

private theorem classStep_repD5_2 :
    classStep (kerRoots repD5) (([xD5] ++ new0D5) ++ new1aD5) new1aD5 = [] := by
  decide +kernel

private theorem classAux_repD5 :
    classAux (kerRoots repD5).length (kerRoots repD5) [xD5] [xD5] = lD5 := by
  rw [show (kerRoots repD5).length = 40 from kerRoots_repD5_length]
  rw [classAux_succ]
  rw [show classStep (kerRoots repD5) [xD5] [xD5] = new0D5 from rfl]
  split_ifs with h0
  · exact absurd h0 (by decide +kernel)
  · rw [classAux_succ]
    rw [classStep_repD5_1]
    split_ifs with h1
    · exact absurd h1 (by decide +kernel)
    · rw [classAux_succ]
      rw [classStep_repD5_2]
      simp only [List.isEmpty_nil, if_true]
      simp [lD5, List.singleton_append]

private theorem kerRoots_repD5_subset : ∀ x ∈ kerRoots repD5, x ∈ lD5 := by
  have h : (kerRoots repD5).all (fun x => lD5.contains x) = true := by
    decide +kernel
  intro x hx
  exact List.contains_iff.mp (List.all_eq_true.mp h x hx)

private theorem foldl_repD5_skip (acc : List (List Vec)) (L : List Vec)
    (hL : ∀ y ∈ L, y ∈ lD5) :
    L.foldl (fun p x => if p.2.contains x then p
        else (p.1 ++ [classAux (kerRoots repD5).length (kerRoots repD5) [x] [x]],
              p.2 ++ classAux (kerRoots repD5).length (kerRoots repD5) [x] [x]))
      (acc, lD5) = (acc, lD5) := by
  induction L generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    have hx : lD5.contains x = true := List.contains_iff.mpr (hL x (by simp))
    rw [hx]
    exact ih acc (fun y hy => hL y (List.mem_cons_of_mem x hy))

private theorem classesOf_repD5 : classesOf (kerRoots repD5) = [lD5] := by
  have hne : kerRoots repD5 ≠ [] := by
    intro h
    have hlen := kerRoots_repD5_length
    rw [h] at hlen
    simp at hlen
  obtain ⟨a, t, hK⟩ := List.exists_cons_of_ne_nil hne
  have ha : a = xD5 := by
    unfold xD5
    rw [hK]
    rfl
  have hKt : xD5 :: t = kerRoots repD5 := by rw [hK, ha]
  rw [show kerRoots repD5 = xD5 :: t from hKt.symm]
  unfold classesOf
  rw [List.foldl_cons]
  simp only [List.contains_nil, Bool.false_or, Bool.false_eq_true, if_false, List.append_nil,
    List.nil_append]
  rw [hKt, classAux_repD5]
  have hskip := foldl_repD5_skip [lD5] t (fun y hy =>
    kerRoots_repD5_subset y (by rw [hK]; exact List.mem_cons_of_mem a hy))
  exact congrArg Prod.fst hskip

private theorem classes_repD5 : classes repD5 = [lD5] := by
  change classesOf (kerRoots repD5) = [lD5]
  exact classesOf_repD5

private theorem classesDataK_repD5 : classesDataK (classes repD5) = true := by
  rw [classes_repD5]
  decide +kernel

private theorem classesSubK_repD5 : classesSubK (kerRoots repD5) (classes repD5) = true := by
  rw [classes_repD5]
  decide +kernel

private theorem classesClosedK_repD5 : classesClosedK (kerRoots repD5) (classes repD5) = true := by
  rw [classes_repD5]
  decide +kernel

private theorem classesCoverK_repD5 : classesCoverK (kerRoots repD5) (classes repD5) = true := by
  rw [classes_repD5]
  decide +kernel

private theorem classesDataK_eq_true (k : Fin 5) :
    classesDataK (classes (reps.getD k [])) = true := by
  fin_cases k
  · exact classes_facts_repA2.1
  · exact classes_facts_repA4A1.1
  · exact classes_facts_repD4.1
  · exact classes_facts_repA5.1
  · exact classesDataK_repD5

private theorem classesSubK_eq_true (k : Fin 5) :
    classesSubK (kerRoots (reps.getD k [])) (classes (reps.getD k [])) = true := by
  fin_cases k
  · exact classes_facts_repA2.2.1
  · exact classes_facts_repA4A1.2.1
  · exact classes_facts_repD4.2.1
  · exact classes_facts_repA5.2.1
  · exact classesSubK_repD5

private theorem classesClosedK_eq_true (k : Fin 5) :
    classesClosedK (kerRoots (reps.getD k [])) (classes (reps.getD k [])) = true := by
  fin_cases k
  · exact classes_facts_repA2.2.2.1
  · exact classes_facts_repA4A1.2.2.1
  · exact classes_facts_repD4.2.2.1
  · exact classes_facts_repA5.2.2.1
  · exact classesClosedK_repD5

private theorem classesCoverK_eq_true (k : Fin 5) :
    classesCoverK (kerRoots (reps.getD k [])) (classes (reps.getD k [])) = true := by
  fin_cases k
  · exact classes_facts_repA2.2.2.2
  · exact classes_facts_repA4A1.2.2.2
  · exact classes_facts_repD4.2.2.2
  · exact classes_facts_repA5.2.2.2
  · exact classesCoverK_repD5

private theorem classes_facts (k : Fin 5) :
    (∀ l ∈ classes (reps.getD k []),
        l.Nodup ∧ (∀ x ∈ l, x.length = 6) ∧ l ≠ [] ∧
        (∀ x ∈ l, x ∈ kerRoots (reps.getD k [])) ∧
        (∀ x ∈ l, ∀ y ∈ kerRoots (reps.getD k []), iform x y ≠ 0 → y ∈ l)) ∧
    (∀ x ∈ kerRoots (reps.getD k []), ∃ l ∈ classes (reps.getD k []), x ∈ l) := by
  have hd := classesDataK_eq_true k
  have hs := classesSubK_eq_true k
  have hc := classesClosedK_eq_true k
  have hcv := classesCoverK_eq_true k
  rw [classesDataK, List.all_eq_true] at hd
  rw [classesSubK, List.all_eq_true] at hs
  rw [classesClosedK, List.all_eq_true] at hc
  rw [classesCoverK, List.all_eq_true] at hcv
  constructor
  · intro l hl
    have h1 := hd l hl
    have h2 := hs l hl
    have h3 := hc l hl
    rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff] at h1
    obtain ⟨⟨hdd, hlen⟩, hne⟩ := h1
    refine ⟨(List.nodup_iff_length_dedup_eq).2 (beq_iff_eq.mp hdd), ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact beq_iff_eq.mp (List.all_eq_true.mp hlen x hx)
    · exact List.isEmpty_eq_false_iff.mp (by simpa [Bool.not_eq_true'] using hne)
    · intro x hx
      exact List.contains_iff.mp (List.all_eq_true.mp h2 x hx)
    · intro x hx y hy hif
      have hy' := List.all_eq_true.mp (List.all_eq_true.mp h3 x hx) y hy
      rw [Bool.or_eq_true_iff, Bool.not_eq_true', bne_eq_false_iff_eq] at hy'
      rcases hy' with h0 | hyl
      · exact absurd h0 hif
      · exact List.contains_iff.mp hyl
  · intro x hx
    rcases List.any_eq_true.mp (hcv x hx) with ⟨l, hl, hc'⟩
    exact ⟨l, hl, List.contains_iff.mp hc'⟩

private theorem reps_getD_length (k : Fin 5) : (reps.getD k []).length = 6 := by
  fin_cases k <;> rfl

private def classRel (K : List Vec) (a b : Vec) : Prop := a ∈ K ∧ b ∈ K ∧ iform a b ≠ 0

private def subRel (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (ZMod 3))
    (u v : kernelRoots χ) : Prop :=
  dotProduct (u : Fin Tag.E6.rank → ℤ)
    (Matrix.mulVec Tag.E6.symmetrizedCartan (v : Fin Tag.E6.rank → ℤ)) ≠ 0

private theorem cstep_witness (K : List Vec) (a : Vec) (p : List Vec × List Vec) :
    ∀ b ∈ (cstep K a p).2, b ∈ p.2 ∨ (b ∈ K ∧ iform a b ≠ 0) := by
  unfold cstep
  induction K generalizing p with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldl_cons]
    intro b hb
    set q : List Vec × List Vec :=
      (if p.1.contains y || p.2.contains y then p
        else if iform a y != 0 then (p.1, p.2 ++ [y]) else p) with hq
    rcases ih (p := q) b hb with h | h
    · rw [hq] at h
      split_ifs at h with hc hd
      · exact Or.inl h
      · rw [List.mem_append, List.mem_singleton] at h
        rcases h with h1 | h1
        · exact Or.inl h1
        · subst h1
          exact Or.inr ⟨List.mem_cons_self .., by simpa using hd⟩
      · exact Or.inl h
    · exact Or.inr ⟨List.mem_cons_of_mem y h.1, h.2⟩

private theorem foldl_cstep_witness (K L : List Vec) (p : List Vec × List Vec) :
    ∀ b ∈ (L.foldl (fun p a => cstep K a p) p).2,
      b ∈ p.2 ∨ (b ∈ K ∧ ∃ a ∈ L, iform a b ≠ 0) := by
  induction L generalizing p with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    intro b hb
    rcases ih (p := cstep K x p) b hb with h | h
    · rcases cstep_witness K x p b h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, x, List.mem_cons_self .., h'.2⟩
    · rcases h with ⟨hK, a, ha, hif⟩
      exact Or.inr ⟨hK, a, List.mem_cons_of_mem x ha, hif⟩

private theorem classStep_witness {K acc frontier : List Vec} {b : Vec}
    (hb : b ∈ classStep K acc frontier) : b ∈ K ∧ ∃ a ∈ frontier, iform a b ≠ 0 := by
  rw [classStep_eq] at hb
  rcases foldl_cstep_witness K frontier (acc, []) b hb with h | h
  · simpa using h
  · exact h

private theorem classAux_zero (K acc frontier : List Vec) : classAux 0 K acc frontier = acc := rfl

private theorem classAux_sound (fuel : Nat) (K acc frontier : List Vec) (x : Vec)
    (hacc : ∀ y ∈ acc, Relation.EqvGen (classRel K) x y)
    (hfront : ∀ y ∈ frontier, Relation.EqvGen (classRel K) x y)
    (hfrontK : ∀ y ∈ frontier, y ∈ K) (y : Vec)
    (hy : y ∈ classAux fuel K acc frontier) :
    Relation.EqvGen (classRel K) x y := by
  induction fuel generalizing acc frontier with
  | zero => exact hacc y (by simpa [classAux_zero] using hy)
  | succ fuel ih =>
    rw [classAux_succ] at hy
    split_ifs at hy with hnew
    · exact hacc y hy
    · exact ih (acc ++ classStep K acc frontier) (classStep K acc frontier)
        (fun z hz => by
          rcases List.mem_append.mp hz with h | h
          · exact hacc z h
          · obtain ⟨hzK, a, ha, hif⟩ := classStep_witness h
            exact Relation.EqvGen.trans _ _ _
              (hfront a ha) (Relation.EqvGen.rel (r := classRel K) _ _ ⟨hfrontK a ha, hzK, hif⟩))
        (fun z hz => by
          obtain ⟨hzK, a, ha, hif⟩ := classStep_witness hz
          exact Relation.EqvGen.trans _ _ _
            (hfront a ha) (Relation.EqvGen.rel (r := classRel K) _ _ ⟨hfrontK a ha, hzK, hif⟩))
        (fun z hz => (classStep_witness hz).1)
        hy

private theorem mem_fold_classesOf (K L : List Vec) (p : List (List Vec) × List Vec) :
    ∀ l ∈ (L.foldl (fun p x => if p.2.contains x then p
        else (p.1 ++ [classAux K.length K [x] [x]], p.2 ++ classAux K.length K [x] [x])) p).1,
      l ∈ p.1 ∨ ∃ x ∈ L, l = classAux K.length K [x] [x] := by
  induction L generalizing p with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    intro l hl
    rcases ih (p := if p.2.contains x then p
        else (p.1 ++ [classAux K.length K [x] [x]], p.2 ++ classAux K.length K [x] [x]))
      l hl with h | h
    · by_cases hc : p.2.contains x
      · rw [if_pos hc] at h; exact Or.inl h
      · rw [if_neg hc] at h
        rcases List.mem_append.mp h with h1 | h1
        · exact Or.inl h1
        · rw [List.mem_singleton] at h1
          exact Or.inr ⟨x, List.mem_cons_self .., h1⟩
    · rcases h with ⟨x', hx', hl'⟩
      exact Or.inr ⟨x', List.mem_cons_of_mem x hx', hl'⟩

private theorem exists_classAux_of_mem_classesOf {K : List Vec} {l : List Vec}
    (hl : l ∈ classesOf K) : ∃ x ∈ K, l = classAux K.length K [x] [x] := by
  rcases mem_fold_classesOf K K ([], []) l hl with h | h
  · simpa using h
  · exact h

private theorem mem_iff_of_eqvGen_classRel {K : List Vec} {x y : Vec}
    (h : Relation.EqvGen (classRel K) x y) : (x ∈ K ↔ y ∈ K) := by
  induction h with
  | rel a b hab => exact ⟨fun _ => hab.2.1, fun _ => hab.1⟩
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

private def toRoot (K : List Vec)
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (ZMod 3))
    (hA : ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ kernelRoots χ ↔ List.ofFn γ ∈ K)
    (hlen : ∀ x ∈ K, x.length = 6) (a : Vec) (ha : a ∈ K) : kernelRoots χ :=
  ⟨fun i => a.getD i.val 0, (hA _).2 (by rw [ofFn_getD a (hlen a ha)]; exact ha)⟩

private theorem eqvGen_subtype_of_classRel (K : List Vec)
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (ZMod 3))
    (hA : ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ kernelRoots χ ↔ List.ofFn γ ∈ K)
    (hlen : ∀ x ∈ K, x.length = 6) {a b : Vec}
    (h : Relation.EqvGen (classRel K) a b) :
    ∀ (ha : a ∈ K) (hb : b ∈ K),
      Relation.EqvGen (subRel χ) (toRoot K χ hA hlen a ha) (toRoot K χ hA hlen b hb) := by
  induction h with
  | rel x y hr =>
    intro ha hb
    refine Relation.EqvGen.rel (r := subRel χ) _ _ ?_
    unfold subRel
    have hx : (toRoot K χ hA hlen x ha : Fin Tag.E6.rank → ℤ) = fun i => x.getD i.val 0 := rfl
    have hy : (toRoot K χ hA hlen y hb : Fin Tag.E6.rank → ℤ) = fun i => y.getD i.val 0 := rfl
    rw [hx, hy, dotProduct_mulVec_eq_iform, lib_iform_of_list, ofFn_getD x (hlen x ha),
      ofFn_getD y (hlen y hb)]
    exact hr.2.2
  | refl x => intro ha hb; exact Relation.EqvGen.refl _
  | symm x y t ih => intro ha hb; exact Relation.EqvGen.symm _ _ (ih hb ha)
  | trans x y z t1 t2 ih1 ih2 =>
    intro ha hb
    have hy : y ∈ K := (mem_iff_of_eqvGen_classRel t1).1 ha
    exact Relation.EqvGen.trans _ _ _ (ih1 ha hy) (ih2 hy hb)

private theorem isClass_mem_iff_of_subtype_eqvGen (K : List Vec)
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (ZMod 3))
    (hA : ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ kernelRoots χ ↔ List.ofFn γ ∈ K)
    (hlen : ∀ x ∈ K, x.length = 6) (l : List Vec)
    (hlK : ∀ x ∈ l, x ∈ K)
    (hclosed : ∀ x ∈ l, ∀ y ∈ K, iform x y ≠ 0 → y ∈ l) {u v : kernelRoots χ}
    (h : Relation.EqvGen (subRel χ) u v) :
    (List.ofFn (u : Fin Tag.E6.rank → ℤ) ∈ l ↔
      List.ofFn (v : Fin Tag.E6.rank → ℤ) ∈ l) := by
  induction h with
  | rel x y hr =>
    have hx : List.ofFn (x : Fin Tag.E6.rank → ℤ) ∈ K := (hA x).1 x.2
    have hy : List.ofFn (y : Fin Tag.E6.rank → ℤ) ∈ K := (hA y).1 y.2
    have hif : iform (List.ofFn (x : Fin Tag.E6.rank → ℤ))
        (List.ofFn (y : Fin Tag.E6.rank → ℤ)) ≠ 0 := by
      rw [← lib_iform_of_list (x : Fin Tag.E6.rank → ℤ) (y : Fin Tag.E6.rank → ℤ),
        ← dotProduct_mulVec_eq_iform]
      exact hr
    have hif' : iform (List.ofFn (y : Fin Tag.E6.rank → ℤ))
        (List.ofFn (x : Fin Tag.E6.rank → ℤ)) ≠ 0 := by
      rw [iform_ofFn_comm]; exact hif
    exact ⟨fun hxu => hclosed _ hxu _ hy hif, fun hyu => hclosed _ hyu _ hx hif'⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private theorem componentRoots_eq_classSet (K : List Vec)
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (ZMod 3))
    (hA : ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ kernelRoots χ ↔ List.ofFn γ ∈ K)
    (hlen : ∀ x ∈ K, x.length = 6) (l : List Vec) (hl : l ∈ classesOf K)
    (hlK : ∀ x ∈ l, x ∈ K)
    (hclosed : ∀ x ∈ l, ∀ y ∈ K, iform x y ≠ 0 → y ∈ l)
    (α : Fin Tag.E6.rank → ℤ) (hα : α ∈ kernelRoots χ) (hmem : List.ofFn α ∈ l) :
    componentRoots χ (Quotient.mk _ ⟨α, hα⟩) = classSet l := by
  ext β
  constructor
  · rintro ⟨hβ, heq⟩
    have hiff := isClass_mem_iff_of_subtype_eqvGen K χ hA hlen l hlK hclosed
      (Quotient.exact heq)
    exact hiff.2 hmem
  · intro hβmem
    have hβK : List.ofFn β ∈ K := hlK _ hβmem
    have hβ : β ∈ kernelRoots χ := (hA β).2 hβK
    have hαK : List.ofFn α ∈ K := (hA α).1 hα
    obtain ⟨x, hxK, rfl⟩ := exists_classAux_of_mem_classesOf hl
    have hcon : Relation.EqvGen (classRel K) (List.ofFn β) (List.ofFn α) :=
      Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (classAux_sound K.length K [x] [x] x
          (fun y hy => by rw [List.mem_singleton] at hy; subst hy; exact Relation.EqvGen.refl _)
          (fun y hy => by rw [List.mem_singleton] at hy; subst hy; exact Relation.EqvGen.refl _)
          (fun y hy => by rw [List.mem_singleton] at hy; subst hy; exact hxK)
          (List.ofFn β) hβmem))
        (classAux_sound K.length K [x] [x] x
          (fun y hy => by rw [List.mem_singleton] at hy; subst hy; exact Relation.EqvGen.refl _)
          (fun y hy => by rw [List.mem_singleton] at hy; subst hy; exact Relation.EqvGen.refl _)
          (fun y hy => by rw [List.mem_singleton] at hy; subst hy; exact hxK)
          (List.ofFn α) hmem)
    have hsub := eqvGen_subtype_of_classRel K χ hA hlen hcon hβK hαK
    have htoβ : toRoot K χ hA hlen (List.ofFn β) hβK = ⟨β, hβ⟩ :=
      Subtype.ext (funext fun i => getD_ofFn β i)
    have htoα : toRoot K χ hA hlen (List.ofFn α) hαK = ⟨α, hα⟩ :=
      Subtype.ext (funext fun i => getD_ofFn α i)
    refine ⟨hβ, ?_⟩
    rw [← htoβ, ← htoα]
    exact Quotient.sound hsub

private theorem dot_mod_iff_chi (x : Vec) (hx : x.length = 6) (γ : Fin Tag.E6.rank → ℤ) :
    (dot (List.ofFn γ) x % 3 == 0) = true ↔
      e6Chi (vecZ x) (Multiplicative.ofAdd γ) = 1 := by
  have hdot : dot (List.ofFn γ) x = ∑ i : Fin Tag.E6.rank, γ i * x.getD i.val 0 := by
    conv_lhs => rw [← ofFn_getD x hx]
    exact dot_ofFn γ (fun i : Fin Tag.E6.rank => x.getD i.val 0)
  have hcast : ((∑ i : Fin Tag.E6.rank, γ i * x.getD i.val 0 : ℤ) : ZMod 3) =
      ∑ i : Fin Tag.E6.rank, ((γ i : ℤ) : ZMod 3) * ((x.getD i.val 0 : ℤ) : ZMod 3) := by
    push_cast
    rfl
  have h1 : (dot (List.ofFn γ) x % 3 == 0) = true ↔
      ((dot (List.ofFn γ) x : ℤ) : ZMod 3) = 0 := by
    rw [beq_iff_eq, ← Int.dvd_iff_emod_eq_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).symm
  rw [h1, hdot, hcast, chi_apply, ofAdd_eq_one]

private theorem ofFn_mem_kerRoots_iff (x : Vec) (hx : x.length = 6)
    (γ : Fin Tag.E6.rank → ℤ) :
    List.ofFn γ ∈ kerRoots x ↔
      IsRoot Tag.E6 γ ∧ e6Chi (vecZ x) (Multiplicative.ofAdd γ) = 1 := by
  rw [kerRoots, kerRootsOf, List.mem_filter]
  rw [isRoot_iff_mem_roots]
  exact and_congr_right fun _ => dot_mod_iff_chi x hx γ

theorem e6KerComponent_iff_classes (k : Fin 5) (Ψ : Set (Fin Tag.E6.rank → ℤ)) :
    E6KerComponent (repZ k) Ψ ↔ ∃ l ∈ classes (reps.getD k []), Ψ = classSet l := by
  have hfacts := (classes_facts k).1
  have hcover := (classes_facts k).2
  have hlenK : ∀ x ∈ kerRoots (reps.getD k []), x.length = 6 := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := hcover x hx
    exact (hfacts l hl).2.1 x hxl
  have hA : ∀ γ : Fin Tag.E6.rank → ℤ,
      γ ∈ kernelRoots (e6Chi (repZ k)) ↔ List.ofFn γ ∈ kerRoots (reps.getD k []) :=
    fun γ => (ofFn_mem_kerRoots_iff (reps.getD k []) (reps_getD_length k) γ).symm
  constructor
  · rintro ⟨i, rfl⟩
    refine Quotient.inductionOn i ?_
    intro u
    obtain ⟨l, hl, hmem⟩ := hcover (List.ofFn u.1) ((hA u.1).1 u.2)
    obtain ⟨-, -, -, hsub, hclos⟩ := hfacts l hl
    exact ⟨l, hl, componentRoots_eq_classSet (kerRoots (reps.getD k [])) (e6Chi (repZ k))
      hA hlenK l hl hsub hclos u.1 u.2 hmem⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨-, hlen, hlne, hsub, hclos⟩ := hfacts l hl
    obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hlne
    have hh : h ∈ h :: t := List.mem_cons_self ..
    have hhK : h ∈ kerRoots (reps.getD k []) := hsub h hh
    have hlenh : h.length = 6 := hlen h hh
    set α : Fin Tag.E6.rank → ℤ := fun i => h.getD i.val 0 with hαdef
    have hα : α ∈ kernelRoots (e6Chi (repZ k)) := by
      rw [hA, hαdef, ofFn_getD h hlenh]
      exact hhK
    refine ⟨Quotient.mk _ ⟨α, hα⟩, ?_⟩
    exact (componentRoots_eq_classSet (kerRoots (reps.getD k [])) (e6Chi (repZ k)) hA hlenK
      (h :: t) hl hsub hclos α hα (by rw [hαdef, ofFn_getD h hlenh]; exact hh)).symm

private theorem class_lengths_repA2 : (classes repA2).map List.length = [6, 6, 6] := by
  decide +kernel

private theorem class_lengths_repA4A1 : (classes repA4A1).map List.length = [20, 2] := by
  decide +kernel

private theorem class_lengths_repD4 : (classes repD4).map List.length = [24] := by
  decide +kernel

private theorem class_lengths_repA5 : (classes repA5).map List.length = [30] := by
  decide +kernel

private theorem class_lengths_repD5 : (classes repD5).map List.length = [40] := by
  rw [classes_repD5]
  have h0 : new0D5.length = 25 := by decide +kernel
  have h1 : new1aD5.length = 14 := rfl
  simp [lD5, h0, h1]

theorem classes_lengths : (List.range 5).map (fun k => (classes (reps.getD k [])).map List.length) =
    [[6, 6, 6], [20, 2], [24], [30], [40]] := by
  rw [show List.range 5 = [0, 1, 2, 3, 4] from by decide]
  simp only [List.map_cons, List.map_nil, reps, List.getD_cons_zero, List.getD_cons_succ]
  rw [class_lengths_repA2, class_lengths_repA4A1, class_lengths_repD4,
    class_lengths_repA5, class_lengths_repD5]

theorem classSet_ncard (k : Fin 5) (l : List Vec) (hl : l ∈ classes (reps.getD k [])) :
    (classSet l).ncard = l.length := by
  obtain ⟨hnodup, hlen, -, -, -⟩ := (classes_facts k).1 l hl
  have himg : classSet l =
      (fun x : Vec => fun i : Fin Tag.E6.rank => x.getD i.val 0) '' (l.toFinset : Set Vec) := by
    ext γ
    simp only [classSet, Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    constructor
    · intro hγ
      exact ⟨List.ofFn γ, hγ, funext fun i => getD_ofFn γ i⟩
    · rintro ⟨x, hx, rfl⟩
      change List.ofFn (fun i : Fin Tag.E6.rank => x.getD i.val 0) ∈ l
      rwa [ofFn_getD x (hlen x hx)]
  have hinj : Set.InjOn (fun x : Vec => fun i : Fin Tag.E6.rank => x.getD i.val 0)
      (l.toFinset : Set Vec) := by
    intro x hx y hy hxy
    have hx' : x ∈ l := by simpa using hx
    have hy' : y ∈ l := by simpa using hy
    have h2 : List.ofFn (fun i : Fin Tag.E6.rank => x.getD i.val 0) =
        List.ofFn (fun i : Fin Tag.E6.rank => y.getD i.val 0) := congrArg List.ofFn hxy
    rwa [ofFn_getD x (hlen x hx'), ofFn_getD y (hlen y hy')] at h2
  rw [himg, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnodup]

end CFSG.StandardType.TablePThreeKG

end
