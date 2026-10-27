module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTBridge
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTRoots
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTClasses
public import Certificates.Data.E6TableTTwo

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

@[expose] def E6TableTTwoAt (v : Fin Tag.E6.rank → ZMod 3) : Prop :=
  ∀ (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)),
    (∀ x y, ρ (x + y) = ρ x + ρ y) → (∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ)) →
    E6Admissible (fun i => ρ (Pi.single i 1)) v 2 → v ≠ 0 →
    ∀ Ψ : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ → ¬ E6SolvTwo ρ Ψ →
      (∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
        (∀ k : ℕ, (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] '' Ψ ≠ Ψ') → E6SolvTwo ρ Ψ') →
      (E6CosetW ρ → E6RowTwoW ρ Ψ) ∧ (¬ E6CosetW ρ → E6RowTwoT ρ Ψ)

theorem e6TableTTwoStmt_iff : E6TableTTwoStmt ↔ ∀ v, E6TableTTwoAt v :=
  ⟨fun h v ρ hadd hroot hadm hv0 Ψ hΨ hnot hall => h ρ v hadd hroot hadm hv0 Ψ hΨ hnot hall,
    fun h ρ v hadd hroot hadm hv0 Ψ hΨ hnot hall => h v ρ hadd hroot hadm hv0 Ψ hΨ hnot hall⟩

private def e6tBridge_classesDataK (cl : List (List Vec)) : Bool :=
  cl.all fun l => (l.dedup.length == l.length) && (l.all fun x => x.length == 6) && !l.isEmpty

private def e6tBridge_classesSubK (K : List Vec) (cl : List (List Vec)) : Bool :=
  cl.all fun l => l.all fun x => K.contains x

private def e6tBridge_classesClosedK (K : List Vec) (cl : List (List Vec)) : Bool :=
  cl.all fun l => l.all fun x => K.all fun y => !(iform x y != 0) || l.contains y

private def e6tBridge_classesCoverK (K : List Vec) (cl : List (List Vec)) : Bool :=
  K.all fun x => cl.any fun l => l.contains x

private def e6tBridge_cstep (K : List Vec) (a : Vec) (p : List Vec × List Vec) :
    List Vec × List Vec :=
  K.foldl (fun p b =>
    if p.1.contains b || p.2.contains b then p
    else if iform a b != 0 then (p.1, p.2 ++ [b]) else p) p

private theorem e6tBridge_classStep_eq (K acc frontier : List Vec) :
    classStep K acc frontier = (frontier.foldl (fun p a => e6tBridge_cstep K a p) (acc, [])).2 := rfl

private theorem e6tBridge_classAux_succ (fuel : Nat) (K acc frontier : List Vec) :
    classAux (fuel + 1) K acc frontier =
      (if (classStep K acc frontier).isEmpty then acc
       else classAux fuel K (acc ++ classStep K acc frontier) (classStep K acc frontier)) := rfl

private theorem e6tBridge_classes_facts_repA2 :
    e6tBridge_classesDataK (classes repA2) = true ∧
    e6tBridge_classesSubK (kerRoots repA2) (classes repA2) = true ∧
    e6tBridge_classesClosedK (kerRoots repA2) (classes repA2) = true ∧
    e6tBridge_classesCoverK (kerRoots repA2) (classes repA2) = true := by
  decide +kernel

private theorem e6tBridge_classes_facts_repA4A1 :
    e6tBridge_classesDataK (classes repA4A1) = true ∧
    e6tBridge_classesSubK (kerRoots repA4A1) (classes repA4A1) = true ∧
    e6tBridge_classesClosedK (kerRoots repA4A1) (classes repA4A1) = true ∧
    e6tBridge_classesCoverK (kerRoots repA4A1) (classes repA4A1) = true := by
  decide +kernel

private theorem e6tBridge_classes_facts_repD4 :
    e6tBridge_classesDataK (classes repD4) = true ∧
    e6tBridge_classesSubK (kerRoots repD4) (classes repD4) = true ∧
    e6tBridge_classesClosedK (kerRoots repD4) (classes repD4) = true ∧
    e6tBridge_classesCoverK (kerRoots repD4) (classes repD4) = true := by
  decide +kernel

private theorem e6tBridge_classes_facts_repA5 :
    e6tBridge_classesDataK (classes repA5) = true ∧
    e6tBridge_classesSubK (kerRoots repA5) (classes repA5) = true ∧
    e6tBridge_classesClosedK (kerRoots repA5) (classes repA5) = true ∧
    e6tBridge_classesCoverK (kerRoots repA5) (classes repA5) = true := by
  decide +kernel

private def e6tBridge_xD5 : Vec := (kerRoots repD5).headD []

private def e6tBridge_new0D5 : List Vec := classStep (kerRoots repD5) [e6tBridge_xD5] [e6tBridge_xD5]

private def e6tBridge_new1aD5 : List Vec :=
  [[0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, 0, -1, 0, 0], [0, 0, 0, 1, 1, 0],
   [0, -1, 0, -1, 0, 0], [0, 1, 0, 1, 1, 0], [0, 0, 0, -1, -1, 0], [0, -1, 0, -1, -1, 0],
   [1, 1, 2, 2, 1, 0], [-1, -1, -2, -2, -1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0],
   [0, -1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0]]

private def e6tBridge_lD5 : List Vec := e6tBridge_xD5 :: e6tBridge_new0D5 ++ e6tBridge_new1aD5

private theorem e6tBridge_kerRoots_repD5_length : (kerRoots repD5).length = 40 := by
  decide +kernel

private theorem e6tBridge_classStep_repD5_1 :
    classStep (kerRoots repD5) ([e6tBridge_xD5] ++ e6tBridge_new0D5) e6tBridge_new0D5 =
      e6tBridge_new1aD5 := by
  rw [e6tBridge_classStep_eq, ← List.take_append_drop 13 e6tBridge_new0D5, List.foldl_append]
  rw [show (e6tBridge_new0D5.take 13).foldl (fun p a => e6tBridge_cstep (kerRoots repD5) a p)
      ([e6tBridge_xD5] ++ (e6tBridge_new0D5.take 13 ++ e6tBridge_new0D5.drop 13), []) =
      ([e6tBridge_xD5] ++ (e6tBridge_new0D5.take 13 ++ e6tBridge_new0D5.drop 13),
        e6tBridge_new1aD5) from by decide +kernel]
  rw [show (e6tBridge_new0D5.drop 13).foldl (fun p a => e6tBridge_cstep (kerRoots repD5) a p)
      ([e6tBridge_xD5] ++ (e6tBridge_new0D5.take 13 ++ e6tBridge_new0D5.drop 13),
        e6tBridge_new1aD5) =
      ([e6tBridge_xD5] ++ (e6tBridge_new0D5.take 13 ++ e6tBridge_new0D5.drop 13),
        e6tBridge_new1aD5) from by decide +kernel]

private theorem e6tBridge_classStep_repD5_2 :
    classStep (kerRoots repD5) (([e6tBridge_xD5] ++ e6tBridge_new0D5) ++ e6tBridge_new1aD5)
      e6tBridge_new1aD5 = [] := by
  decide +kernel

private theorem e6tBridge_classAux_repD5 :
    classAux (kerRoots repD5).length (kerRoots repD5) [e6tBridge_xD5] [e6tBridge_xD5] =
      e6tBridge_lD5 := by
  rw [show (kerRoots repD5).length = 40 from e6tBridge_kerRoots_repD5_length]
  rw [e6tBridge_classAux_succ]
  rw [show classStep (kerRoots repD5) [e6tBridge_xD5] [e6tBridge_xD5] = e6tBridge_new0D5 from rfl]
  split_ifs with h0
  · exact absurd h0 (by decide +kernel)
  · rw [e6tBridge_classAux_succ]
    rw [e6tBridge_classStep_repD5_1]
    split_ifs with h1
    · exact absurd h1 (by decide +kernel)
    · rw [e6tBridge_classAux_succ]
      rw [e6tBridge_classStep_repD5_2]
      simp only [List.isEmpty_nil, if_true]
      simp [e6tBridge_lD5, List.singleton_append]

private theorem e6tBridge_kerRoots_repD5_subset : ∀ x ∈ kerRoots repD5, x ∈ e6tBridge_lD5 := by
  have h : (kerRoots repD5).all (fun x => e6tBridge_lD5.contains x) = true := by
    decide +kernel
  intro x hx
  exact List.contains_iff.mp (List.all_eq_true.mp h x hx)

private theorem e6tBridge_foldl_repD5_skip (acc : List (List Vec)) (L : List Vec)
    (hL : ∀ y ∈ L, y ∈ e6tBridge_lD5) :
    L.foldl (fun p x => if p.2.contains x then p
        else (p.1 ++ [classAux (kerRoots repD5).length (kerRoots repD5) [x] [x]],
              p.2 ++ classAux (kerRoots repD5).length (kerRoots repD5) [x] [x]))
      (acc, e6tBridge_lD5) = (acc, e6tBridge_lD5) := by
  induction L generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    have hx : e6tBridge_lD5.contains x = true := List.contains_iff.mpr (hL x (by simp))
    rw [hx]
    exact ih acc (fun y hy => hL y (List.mem_cons_of_mem x hy))

private theorem e6tBridge_classesOf_repD5 : classesOf (kerRoots repD5) = [e6tBridge_lD5] := by
  have hne : kerRoots repD5 ≠ [] := by
    intro h
    have hlen := e6tBridge_kerRoots_repD5_length
    rw [h] at hlen
    simp at hlen
  obtain ⟨a, t, hK⟩ := List.exists_cons_of_ne_nil hne
  have ha : a = e6tBridge_xD5 := by
    unfold e6tBridge_xD5
    rw [hK]
    rfl
  have hKt : e6tBridge_xD5 :: t = kerRoots repD5 := by rw [hK, ha]
  rw [show kerRoots repD5 = e6tBridge_xD5 :: t from hKt.symm]
  unfold classesOf
  rw [List.foldl_cons]
  simp only [List.contains_nil, Bool.false_or, Bool.false_eq_true, if_false, List.append_nil,
    List.nil_append]
  rw [hKt, e6tBridge_classAux_repD5]
  have hskip := e6tBridge_foldl_repD5_skip [e6tBridge_lD5] t (fun y hy =>
    e6tBridge_kerRoots_repD5_subset y (by rw [hK]; exact List.mem_cons_of_mem a hy))
  exact congrArg Prod.fst hskip

private theorem e6tBridge_classes_repD5 : classes repD5 = [e6tBridge_lD5] := by
  change classesOf (kerRoots repD5) = [e6tBridge_lD5]
  exact e6tBridge_classesOf_repD5

private theorem e6tBridge_classesDataK_repD5 : e6tBridge_classesDataK (classes repD5) = true := by
  rw [e6tBridge_classes_repD5]
  decide +kernel

private theorem e6tBridge_classesSubK_repD5 :
    e6tBridge_classesSubK (kerRoots repD5) (classes repD5) = true := by
  rw [e6tBridge_classes_repD5]
  decide +kernel

private theorem e6tBridge_classesClosedK_repD5 :
    e6tBridge_classesClosedK (kerRoots repD5) (classes repD5) = true := by
  rw [e6tBridge_classes_repD5]
  decide +kernel

private theorem e6tBridge_classesCoverK_repD5 :
    e6tBridge_classesCoverK (kerRoots repD5) (classes repD5) = true := by
  rw [e6tBridge_classes_repD5]
  decide +kernel

private theorem e6tBridge_classesDataK_eq_true (k : Fin 5) :
    e6tBridge_classesDataK (classes (reps.getD k [])) = true := by
  fin_cases k
  · exact e6tBridge_classes_facts_repA2.1
  · exact e6tBridge_classes_facts_repA4A1.1
  · exact e6tBridge_classes_facts_repD4.1
  · exact e6tBridge_classes_facts_repA5.1
  · exact e6tBridge_classesDataK_repD5

private theorem e6tBridge_classesSubK_eq_true (k : Fin 5) :
    e6tBridge_classesSubK (kerRoots (reps.getD k [])) (classes (reps.getD k [])) = true := by
  fin_cases k
  · exact e6tBridge_classes_facts_repA2.2.1
  · exact e6tBridge_classes_facts_repA4A1.2.1
  · exact e6tBridge_classes_facts_repD4.2.1
  · exact e6tBridge_classes_facts_repA5.2.1
  · exact e6tBridge_classesSubK_repD5

private theorem e6tBridge_classesClosedK_eq_true (k : Fin 5) :
    e6tBridge_classesClosedK (kerRoots (reps.getD k [])) (classes (reps.getD k [])) = true := by
  fin_cases k
  · exact e6tBridge_classes_facts_repA2.2.2.1
  · exact e6tBridge_classes_facts_repA4A1.2.2.1
  · exact e6tBridge_classes_facts_repD4.2.2.1
  · exact e6tBridge_classes_facts_repA5.2.2.1
  · exact e6tBridge_classesClosedK_repD5

private theorem e6tBridge_classesCoverK_eq_true (k : Fin 5) :
    e6tBridge_classesCoverK (kerRoots (reps.getD k [])) (classes (reps.getD k [])) = true := by
  fin_cases k
  · exact e6tBridge_classes_facts_repA2.2.2.2
  · exact e6tBridge_classes_facts_repA4A1.2.2.2
  · exact e6tBridge_classes_facts_repD4.2.2.2
  · exact e6tBridge_classes_facts_repA5.2.2.2
  · exact e6tBridge_classesCoverK_repD5

theorem e6Two_classes_facts (k : Fin 5) :
    (∀ l ∈ classes (reps.getD k []),
        l.Nodup ∧ (∀ x ∈ l, x.length = 6) ∧ l ≠ [] ∧
        (∀ x ∈ l, x ∈ kerRoots (reps.getD k [])) ∧
        (∀ x ∈ l, ∀ y ∈ kerRoots (reps.getD k []), iform x y ≠ 0 → y ∈ l)) ∧
    (∀ x ∈ kerRoots (reps.getD k []), ∃ l ∈ classes (reps.getD k []), x ∈ l) := by
  have hd := e6tBridge_classesDataK_eq_true k
  have hs := e6tBridge_classesSubK_eq_true k
  have hc := e6tBridge_classesClosedK_eq_true k
  have hcv := e6tBridge_classesCoverK_eq_true k
  rw [e6tBridge_classesDataK, List.all_eq_true] at hd
  rw [e6tBridge_classesSubK, List.all_eq_true] at hs
  rw [e6tBridge_classesClosedK, List.all_eq_true] at hc
  rw [e6tBridge_classesCoverK, List.all_eq_true] at hcv
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

private abbrev e6tBridge_ofVec (x : Fin Tag.E6.rank → ℤ) : Vec := List.ofFn x

private abbrev e6tBridge_ofVec6 (x : Fin 6 → ℤ) : Vec := List.ofFn x

private lemma e6tBridge_intList_add_eq (a b : Vec) :
    a + b = List.zipWithAll (fun x y => x.getD 0 + y.getD 0) a b := by
  change Lean.Omega.IntList.add a b = _
  rfl

private lemma e6tBridge_length_zipWithAll {α β γ : Type*} (f : Option α → Option β → γ)
    (a : List α) (b : List β) :
    (List.zipWithAll f a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => cases b <;> simp [List.zipWithAll]
  | cons x xs ih => cases b with
    | nil => simp [List.zipWithAll]
    | cons y ys => simp [List.zipWithAll_cons_cons, ih]

private lemma e6tBridge_length_add (a b : Vec) : (a + b).length = max a.length b.length := by
  rw [e6tBridge_intList_add_eq, e6tBridge_length_zipWithAll]

private lemma e6tBridge_act_length (b : List Vec) (x : Vec)
    (h0 : (b.getD 0 []).length = 6) (h1 : (b.getD 1 []).length = 6)
    (h2 : (b.getD 2 []).length = 6) (h3 : (b.getD 3 []).length = 6)
    (h4 : (b.getD 4 []).length = 6) (h5 : (b.getD 5 []).length = 6) :
    (act b x).length = 6 := by
  unfold act
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  simp only [e6tBridge_length_add, Certificates.Data.E6TableT.scalarMul, List.length_map,
    List.length_ofFn, List.length_replicate, h0, h1, h2, h3, h4, h5, max_self]

private lemma e6tBridge_sum_apply_smul (x : Fin 6 → ℤ) (g : Fin 6 → (Fin 6 → ℤ)) (k : Fin 6) :
    (∑ i, x i • g i) k = ∑ i, x i * g i k := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]

private lemma e6tBridge_act_ofVec (g : Fin 6 → (Fin 6 → ℤ)) (x : Fin 6 → ℤ) :
    act (List.ofFn fun i => e6tBridge_ofVec6 (g i)) (e6tBridge_ofVec6 x) =
      e6tBridge_ofVec6 (∑ i, x i • g i) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 6
  · have hL : (act (List.ofFn fun i => e6tBridge_ofVec6 (g i)) (e6tBridge_ofVec6 x))[k]? =
        some (∑ i : Fin 6, x i * g i ⟨k, hk⟩) := by
      unfold act
      rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
      simp only [List.foldl_cons, List.foldl_nil, e6tBridge_intList_add_eq,
        List.zipWithAll_cons_cons, List.getElem?_zipWithAll, List.getElem?_map,
        Certificates.Data.E6TableT.scalarMul, e6tBridge_ofVec6, List.getElem?_ofFn,
        List.getElem?_replicate, List.getD_eq_getElem?_getD, Option.getD_some, Option.getD_none,
        Option.map_some]
      interval_cases k <;> simp [Fin.sum_univ_six] <;> ring
    have hR : (e6tBridge_ofVec6 (∑ i, x i • g i))[k]? =
        some (∑ i : Fin 6, x i * g i ⟨k, hk⟩) := by
      rw [e6tBridge_ofVec6, List.getElem?_ofFn, dif_pos hk, e6tBridge_sum_apply_smul,
        Fin.sum_univ_six]
    rw [hL, hR]
  · have hk' : ¬ k < 6 := hk
    have hL : (act (List.ofFn fun i => e6tBridge_ofVec6 (g i)) (e6tBridge_ofVec6 x))[k]? = none := by
      rw [List.getElem?_eq_none_iff]
      rw [e6tBridge_act_length (List.ofFn fun i => e6tBridge_ofVec6 (g i)) (e6tBridge_ofVec6 x)
        (by simp [e6tBridge_ofVec6, List.length_ofFn]) (by simp [e6tBridge_ofVec6, List.length_ofFn])
        (by simp [e6tBridge_ofVec6, List.length_ofFn]) (by simp [e6tBridge_ofVec6, List.length_ofFn])
        (by simp [e6tBridge_ofVec6, List.length_ofFn]) (by simp [e6tBridge_ofVec6, List.length_ofFn])]
      exact Nat.le_of_not_lt hk
    have hR : (e6tBridge_ofVec6 (∑ i, x i • g i))[k]? = none := by
      rw [List.getElem?_eq_none_iff]
      simpa [e6tBridge_ofVec6] using Nat.le_of_not_lt hk
    rw [hL, hR]

private lemma e6tBridge_act_ofVec' (g : Fin Tag.E6.rank → (Fin Tag.E6.rank → ℤ))
    (x : Fin Tag.E6.rank → ℤ) :
    act (List.ofFn fun i => e6tBridge_ofVec (g i)) (e6tBridge_ofVec x) =
      e6tBridge_ofVec (∑ i, x i • g i) :=
  e6tBridge_act_ofVec (fun i : Fin 6 => g ⟨i.val, i.isLt⟩)
    (fun i : Fin 6 => x ⟨i.val, i.isLt⟩)

theorem act_bList_ofFn (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (γ : Fin Tag.E6.rank → ℤ) : act (bList fun i => ρ (Pi.single i 1)) (List.ofFn γ) = List.ofFn (ρ γ) := by
  change act (bList fun i => ρ (Pi.single i 1)) (e6tBridge_ofVec γ) = e6tBridge_ofVec (ρ γ)
  unfold bList
  rw [e6tBridge_act_ofVec']
  congr 1
  let ρA : (Fin Tag.E6.rank → ℤ) ≃+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := ρ, invFun := ρ.symm, left_inv := ρ.left_inv, right_inv := ρ.right_inv,
      map_add' := hadd }
  have hy : γ = ∑ i, γ i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; simp [Pi.single_eq_of_ne (Ne.symm hbj)]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  conv_rhs => rw [hy]
  change ∑ i, γ i • ρA (Pi.single i 1) = ρA (∑ i, γ i • (Pi.single i 1))
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (map_zsmul ρA (γ i) (Pi.single i 1)).symm

end CFSG.StandardType.TablePThreeKG

end
