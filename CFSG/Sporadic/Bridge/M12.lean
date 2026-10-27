module

public import CFSG.Sporadic.Bridge.M12Check
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Blueprint.NativeSporadic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Bridge.M12

open CFSG.Certificates CFSG.Certificates.CosetEnumeration TauCeti Equiv

theorem generatorCount_eq : Sporadic.m12Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

private theorem presentation_eq : SporadicName.M12.presentation = Sporadic.m12Presentation := rfl

@[expose] def subWord : List (Fin Sporadic.m12Presentation.generatorCount × Bool) :=
  [(⟨1, by simp [generatorCount_eq]⟩, false), (⟨0, by simp [generatorCount_eq]⟩, true)]

noncomputable def subElt : Sporadic.m12Presentation.Group :=
  PresentedGroup.mk _ (FreeGroup.mk subWord)

theorem subElt_pow_three : subElt ^ 3 = 1 := by
  have hmem : [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true)] ∈
      Sporadic.m12Presentation.relatorLetters := by
    rw [Sporadic.m12Presentation_relatorLetters]
    simp
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hmem
  obtain ⟨w, hw, hwe⟩ := hmem
  have hinj : Function.Injective (List.map fun letter :
      Fin Sporadic.m12Presentation.generatorCount × Bool => (letter.1.val, letter.2)) :=
    List.map_injective_iff.mpr fun x y hxy => by
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext (Fin.ext hxy.1) hxy.2
  have hw3 : w = subWord ++ subWord ++ subWord := hinj (hwe.trans rfl)
  have h1 := PresentedGroup.one_of_mem (relators_mem _ w hw)
  rw [hw3, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul] at h1
  rw [pow_three']
  exact h1

theorem index_le :
    (Subgroup.zpowers subElt).FiniteIndex ∧ (Subgroup.zpowers subElt).index ≤ 31680 := by
  have hc : codes [subWord] = [[3, 0]] := by decide
  have h := index_le_of_facts_presented (rels := Sporadic.m12Presentation.relatorSet)
    (H := Subgroup.zpowers subElt)
    (N := 41575) (F := 85775) (fx := M12Data.fx) (fc := M12Data.fc) (fy := M12Data.fy)
    (kind := M12Data.kind) (wi := M12Data.wi) (fs := M12Data.fs) (ft := M12Data.ft)
    (fo := M12Data.fo) (refs := M12Data.refs) (pl := M12Data.pl) (ffi := M12Data.ffi)
    (live := M12Data.live) Sporadic.m12Presentation.relators [subWord] M12Data.words
    (relators_mem _)
    (by
      intro w hw
      rw [List.mem_singleton] at hw
      subst hw
      exact Subgroup.mem_zpowers subElt)
    (by
      rw [codes_relators, Sporadic.m12Presentation_relatorLetters, generatorCount_eq]
      decide +kernel)
    M12Data.live_zero (by norm_num)
    (by rw [hc, generatorCount_eq]; exact M12Data.facts_all)
    (by rw [generatorCount_eq]; exact M12Data.cover_all)
  rw [M12Data.liveCount_eq] at h
  exact h

theorem finite_card_le :
    Finite Sporadic.m12Presentation.Group ∧ Nat.card Sporadic.m12Presentation.Group ≤ 95040 :=
  finite_card_le_of_zpowers subElt (k := 3) (n := 31680) (by norm_num) subElt_pow_three
    index_le.1 index_le.2

theorem tauCeti_finite_card_le :
    Finite SporadicName.M12.Group ∧ Nat.card SporadicName.M12.Group ≤ 95040 := by
  show Finite SporadicName.M12.presentation.Group ∧
    Nat.card SporadicName.M12.presentation.Group ≤ 95040
  rw [presentation_eq]
  exact finite_card_le

@[expose] def gen (i : ℕ) : Perm (Fin 12) :=
  if i = 0 then
    List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]
  else if i = 1 then
    List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
      List.formPerm [5, 9, 6]
  else 1

theorem gen_mem (i : ℕ) : gen i ∈ Blueprint.NativeSporadic.M12 := by
  unfold gen
  split
  · exact Subgroup.subset_closure (by simp)
  · split
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.one_mem _

theorem nativeWord_mem (w : List (ℕ × Bool)) : wordProd gen w ∈ Blueprint.NativeSporadic.M12 :=
  wordProd_mem gen_mem w

@[expose] def alpha : Perm (Fin 12) :=
  List.formPerm [0, 11, 3, 1, 2] * List.formPerm [4, 9, 10, 5, 6]

@[expose] def beta : Perm (Fin 12) :=
  List.formPerm [0, 1] * List.formPerm [2, 10, 3, 6, 8, 9] * List.formPerm [5, 11, 7]

theorem alpha_eq : alpha = wordProd gen
    [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, false), (0, true)] := by
  decide +kernel

theorem beta_eq : beta = wordProd gen
    [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, false)] := by
  decide +kernel

@[expose] def witnesses0 : List (Fin 12 × List (ℕ × Bool)) :=
  [(0, []),
    (3, [(0, true)]),
    (7, [(1, true)]),
    (8, [(1, false)]),
    (1, [(1, true), (0, true)]),
    (2, [(1, false), (0, true)]),
    (9, [(0, true), (1, false), (0, true)]),
    (5, [(1, false), (0, true), (1, false), (0, true)]),
    (6, [(1, true), (0, true), (1, false), (0, true)]),
    (11, [(0, true), (1, false), (0, true), (1, false), (0, true)]),
    (4, [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true)]),
    (10, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true)])]

@[expose] def witnesses1 : List (Fin 12 × List (ℕ × Bool)) :=
  [(1, []),
    (5, [(1, false), (0, true), (1, true)]),
    (7, [(1, true), (0, true), (1, false)]),
    (11, [(0, true), (1, false), (0, true), (1, true), (0, true)]),
    (4, [(0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true)]),
    (10, [(1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true)]),
    (6, [(1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true)]),
    (9, [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (0, true)]),
    (2, [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, false), (0, true), (1, true)]),
    (3, [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, true), (0, true)]),
    (8, [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true)])]

@[expose] def witnesses2 : List (Fin 12 × List (ℕ × Bool)) :=
  [(2, []),
    (8, [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)]),
    (5, [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, false), (0, true)]),
    (10, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)]),
    (6, [(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true)]),
    (7, [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
      (0, true)]),
    (11, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false)]),
    (3, [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, false)]),
    (9, [(0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (0, true)]),
    (4, [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, true), (0, true)])]

@[expose] def witnesses3 : List (Fin 12 × List (ℕ × Bool)) :=
  [(3, []),
    (4, [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]),
    (9, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, false)]),
    (7, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true)]),
    (11, [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false)]),
    (10, [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, false), (0, true), (1, false)]),
    (5, [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]),
    (6, [(1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false)]),
    (8, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false)])]

@[expose] def witnesses4 : List (Fin 12 × List (ℕ × Bool)) :=
  [(4, []),
    (6, [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (0, true), (1, true), (0, true)]),
    (9, [(0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, true), (0, true), (1, false), (0, true)]),
    (7, [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, true)]),
    (11, [(1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false), (0, true), (1, false), (0, true)]),
    (8, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]),
    (5, [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true),
      (1, true)]),
    (10, [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, false)])]

@[expose] noncomputable def stab1 : Subgroup (Perm (Fin 12)) :=
  Blueprint.NativeSporadic.M12 ⊓ MulAction.stabilizer (Perm (Fin 12)) (0 : Fin 12)
@[expose] noncomputable def stab2 : Subgroup (Perm (Fin 12)) :=
  stab1 ⊓ MulAction.stabilizer (Perm (Fin 12)) (1 : Fin 12)
@[expose] noncomputable def stab3 : Subgroup (Perm (Fin 12)) :=
  stab2 ⊓ MulAction.stabilizer (Perm (Fin 12)) (2 : Fin 12)
@[expose] noncomputable def stab4 : Subgroup (Perm (Fin 12)) :=
  stab3 ⊓ MulAction.stabilizer (Perm (Fin 12)) (3 : Fin 12)
@[expose] noncomputable def stab5 : Subgroup (Perm (Fin 12)) :=
  stab4 ⊓ MulAction.stabilizer (Perm (Fin 12)) (4 : Fin 12)

theorem witnesses_ok0 : ∀ x ∈ witnesses0, wordProd gen x.2 (0 : Fin 12) = x.1 := by
  decide +kernel
theorem witnesses_ok1 : ∀ x ∈ witnesses1,
    wordProd gen x.2 (0 : Fin 12) = 0 ∧ wordProd gen x.2 (1 : Fin 12) = x.1 := by
  decide +kernel
theorem witnesses_ok2 : ∀ x ∈ witnesses2, wordProd gen x.2 (0 : Fin 12) = 0 ∧
    wordProd gen x.2 (1 : Fin 12) = 1 ∧ wordProd gen x.2 (2 : Fin 12) = x.1 := by
  decide +kernel
theorem witnesses_ok3 : ∀ x ∈ witnesses3, wordProd gen x.2 (0 : Fin 12) = 0 ∧
    wordProd gen x.2 (1 : Fin 12) = 1 ∧ wordProd gen x.2 (2 : Fin 12) = 2 ∧
    wordProd gen x.2 (3 : Fin 12) = x.1 := by
  decide +kernel
theorem witnesses_ok4 : ∀ x ∈ witnesses4, wordProd gen x.2 (0 : Fin 12) = 0 ∧
    wordProd gen x.2 (1 : Fin 12) = 1 ∧ wordProd gen x.2 (2 : Fin 12) = 2 ∧
    wordProd gen x.2 (3 : Fin 12) = 3 ∧ wordProd gen x.2 (4 : Fin 12) = x.1 := by
  decide +kernel

theorem witnesses_nodup : (witnesses0.map Prod.fst).Nodup ∧ (witnesses1.map Prod.fst).Nodup ∧
    (witnesses2.map Prod.fst).Nodup ∧ (witnesses3.map Prod.fst).Nodup ∧
    (witnesses4.map Prod.fst).Nodup := by
  decide +kernel

theorem witnesses_length : witnesses0.length = 12 ∧ witnesses1.length = 11 ∧
    witnesses2.length = 10 ∧ witnesses3.length = 9 ∧ witnesses4.length = 8 := by
  decide +kernel

theorem le_card_native : 95040 ≤ Nat.card Blueprint.NativeSporadic.M12 := by
  have h0 := le_card_of_witnesses (K := Blueprint.NativeSporadic.M12) gen 0 witnesses0
    (fun x _ => nativeWord_mem x.2) (fun x hx => witnesses_ok0 x hx) witnesses_nodup.1
  have h1 := le_card_of_witnesses (K := stab1) gen 1 witnesses1
    (fun x hx => ⟨nativeWord_mem x.2, mem_stabilizer_iff_apply.mpr (witnesses_ok1 x hx).1⟩)
    (fun x hx => (witnesses_ok1 x hx).2) witnesses_nodup.2.1
  have h2 := le_card_of_witnesses (K := stab2) gen 2 witnesses2
    (fun x hx => ⟨⟨nativeWord_mem x.2, mem_stabilizer_iff_apply.mpr (witnesses_ok2 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok2 x hx).2.1⟩)
    (fun x hx => (witnesses_ok2 x hx).2.2) witnesses_nodup.2.2.1
  have h3 := le_card_of_witnesses (K := stab3) gen 3 witnesses3
    (fun x hx => ⟨⟨⟨nativeWord_mem x.2, mem_stabilizer_iff_apply.mpr (witnesses_ok3 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok3 x hx).2.1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok3 x hx).2.2.1⟩)
    (fun x hx => (witnesses_ok3 x hx).2.2.2) witnesses_nodup.2.2.2.1
  have h4 := le_card_of_witnesses (K := stab4) gen 4 witnesses4
    (fun x hx => ⟨⟨⟨⟨nativeWord_mem x.2, mem_stabilizer_iff_apply.mpr (witnesses_ok4 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok4 x hx).2.1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok4 x hx).2.2.1⟩,
      mem_stabilizer_iff_apply.mpr (witnesses_ok4 x hx).2.2.2.1⟩)
    (fun x hx => (witnesses_ok4 x hx).2.2.2.2) witnesses_nodup.2.2.2.2
  obtain ⟨l0, l1, l2, l3, l4⟩ := witnesses_length
  rw [l0] at h0; rw [l1] at h1; rw [l2] at h2; rw [l3] at h3; rw [l4] at h4
  have h5 : 1 ≤ Nat.card ↥stab5 := Nat.card_pos
  change 12 * Nat.card ↥stab1 ≤ Nat.card ↥Blueprint.NativeSporadic.M12 at h0
  change 11 * Nat.card ↥stab2 ≤ Nat.card ↥stab1 at h1
  change 10 * Nat.card ↥stab3 ≤ Nat.card ↥stab2 at h2
  change 9 * Nat.card ↥stab4 ≤ Nat.card ↥stab3 at h3
  change 8 * Nat.card ↥stab5 ≤ Nat.card ↥stab4 at h4
  omega

@[expose] noncomputable def img (i : ℕ) : ↥Blueprint.NativeSporadic.M12 :=
  if i = 0 then ⟨alpha, alpha_eq ▸ nativeWord_mem _⟩
  else if i = 1 then ⟨beta, beta_eq ▸ nativeWord_mem _⟩ else 1

theorem img_val (i : ℕ) : ((img i : ↥Blueprint.NativeSporadic.M12) : Perm (Fin 12)) =
    if i = 0 then alpha else if i = 1 then beta else 1 := by
  unfold img
  split
  · rfl
  · split <;> rfl

theorem relators_eval : ∀ v ∈ Sporadic.m12Presentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  apply Subtype.ext
  rw [coe_wordProd, Subgroup.coe_one]
  simp only [img_val]
  revert v
  rw [Sporadic.m12Presentation_relatorLetters]
  decide +kernel

noncomputable def toNative : Sporadic.m12Presentation.Group →* ↥Blueprint.NativeSporadic.M12 :=
  presHom _ img relators_eval

@[expose] def genWord (i : ℕ) : List (ℕ × Bool) :=
  if i = 0 then
    [(0, true), (1, true), (0, false), (1, false), (1, false), (0, true), (1, true), (0, true),
      (1, false), (0, true), (1, true), (1, true), (0, false), (1, false)]
  else
    [(0, true), (0, true), (1, true), (1, true), (0, false), (0, false), (1, true), (1, true),
      (0, false), (0, false), (1, true), (0, true), (1, true)]

theorem gen_eq_wordProd : ∀ i ∈ [0, 1],
    gen i = wordProd (fun j => (img j : Perm (Fin 12))) (genWord i) := by
  simp only [img_val]
  decide +kernel

theorem toNative_surjective : Function.Surjective toNative := by
  have hgen : ∀ i ∈ [0, 1], (⟨gen i, gen_mem i⟩ : ↥Blueprint.NativeSporadic.M12) ∈
      toNative.range := by
    intro i hi
    refine ⟨wordProd (presGen _) (genWord i), ?_⟩
    rw [toNative, presHom_wordProd _ img relators_eval (genWord i) (by
      rw [generatorCount_eq]
      rcases List.mem_pair.mp hi with rfl | rfl <;> decide)]
    exact Subtype.ext (by rw [coe_wordProd]; exact (gen_eq_wordProd i hi).symm)
  intro y
  obtain ⟨y, hy⟩ := y
  suffices H : ∀ z (hz : z ∈ Blueprint.NativeSporadic.M12),
      (⟨z, hz⟩ : ↥Blueprint.NativeSporadic.M12) ∈ toNative.range from H y hy
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | hz
    · exact hgen 0 (by simp)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hgen 1 (by simp)
  | one => exact toNative.range.one_mem
  | mul x y hx hy ihx ihy => exact toNative.range.mul_mem ihx ihy
  | inv x hx ih => exact toNative.range.inv_mem ih

theorem nonempty_mulEquiv :
    Nonempty (↥Blueprint.NativeSporadic.M12 ≃* SporadicName.M12.Group) := by
  obtain ⟨hfin, hcard⟩ := finite_card_le
  show Nonempty (↥Blueprint.NativeSporadic.M12 ≃* SporadicName.M12.presentation.Group)
  rw [presentation_eq]
  exact nonempty_mulEquiv_of_surjective toNative toNative_surjective hcard le_card_native

end CFSG.Sporadic.Bridge.M12
