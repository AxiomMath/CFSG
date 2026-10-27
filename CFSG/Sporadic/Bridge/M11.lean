module

public import CFSG.Sporadic.Bridge.M11Check
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Blueprint.NativeSporadic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Bridge.M11

open CFSG.Certificates CFSG.Certificates.CosetEnumeration TauCeti Equiv

theorem generatorCount_eq : Sporadic.m11Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

private theorem presentation_eq : SporadicName.M11.presentation = Sporadic.m11Presentation := rfl

theorem finite_card_le :
    Finite Sporadic.m11Presentation.Group ∧ Nat.card Sporadic.m11Presentation.Group ≤ 7920 := by
  have h := card_le_of_facts_presented (rels := Sporadic.m11Presentation.relatorSet)
    (N := 25648) (F := 56014) (fx := M11Data.fx) (fc := M11Data.fc) (fy := M11Data.fy)
    (kind := M11Data.kind) (wi := M11Data.wi) (fs := M11Data.fs) (ft := M11Data.ft)
    (fo := M11Data.fo) (refs := M11Data.refs) (pl := M11Data.pl) (ffi := M11Data.ffi)
    (live := M11Data.live) Sporadic.m11Presentation.relators M11Data.words
    (relators_mem _)
    (by
      rw [codes_relators, Sporadic.m11Presentation_relatorLetters, generatorCount_eq]
      decide +kernel)
    M11Data.live_zero (by norm_num)
    (by rw [generatorCount_eq]; exact M11Data.facts_all)
    (by rw [generatorCount_eq]; exact M11Data.cover_all)
  rw [M11Data.liveCount_eq] at h
  exact h

theorem tauCeti_finite_card_le :
    Finite SporadicName.M11.Group ∧ Nat.card SporadicName.M11.Group ≤ 7920 := by
  show Finite SporadicName.M11.presentation.Group ∧
    Nat.card SporadicName.M11.presentation.Group ≤ 7920
  rw [presentation_eq]
  exact finite_card_le

@[expose] def gen (i : ℕ) : Perm (Fin 11) :=
  if i = 0 then
    List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]
  else if i = 1 then List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8] else 1

theorem gen_mem (i : ℕ) : gen i ∈ Blueprint.NativeSporadic.M11 := by
  unfold gen
  split
  · exact Subgroup.subset_closure (by simp)
  · split
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.one_mem _

theorem nativeWord_mem (w : List (ℕ × Bool)) : wordProd gen w ∈ Blueprint.NativeSporadic.M11 :=
  wordProd_mem gen_mem w

@[expose] def alpha : Perm (Fin 11) := List.formPerm [0, 10, 4, 3, 5, 7, 6, 2, 8, 1, 9]

@[expose] def beta : Perm (Fin 11) := List.formPerm [0, 10, 8, 4, 9, 2, 6, 5, 1, 3, 7]

theorem alpha_eq : alpha = wordProd gen
    [(1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (0, false),
      (1, false), (0, false), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
      (1, false), (0, false), (1, false), (1, false), (0, false)] := by
  decide +kernel

theorem beta_eq : beta = wordProd gen
    [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (1, true),
      (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
      (1, true), (0, true), (1, true)] := by
  decide +kernel

@[expose] def witnesses0 : List (Fin 11 × List (ℕ × Bool)) :=
  [(0, []),
    (3, [(1, true)]),
    (10, [(0, false), (1, true)]),
    (2, [(1, false), (1, false)]),
    (7, [(1, false)]),
    (8, [(0, false), (1, false)]),
    (1, [(1, true), (0, true), (1, false)]),
    (9, [(0, false), (1, true), (0, false), (1, false)]),
    (4, [(1, true), (1, true), (0, true), (1, false)]),
    (6, [(0, false), (1, false), (1, false), (0, false), (1, false)]),
    (5, [(1, false), (0, true), (1, false)])]

@[expose] def witnesses1 : List (Fin 11 × List (ℕ × Bool)) :=
  [(1, []),
    (9, [(0, false)]),
    (2, [(1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false)]),
    (10, [(0, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)]),
    (3, [(1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false)]),
    (8, [(1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]),
    (7, [(0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)]),
    (4, [(0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]),
    (6, [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]),
    (5, [(0, false), (1, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)])]

@[expose] def witnesses2 : List (Fin 11 × List (ℕ × Bool)) :=
  [(2, []),
    (3, [(0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true)]),
    (10, [(1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false)]),
    (7, [(1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (1, false)]),
    (6, [(1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true)]),
    (8, [(0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (0, false), (1, false), (0, false), (1, true), (0, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false)]),
    (5, [(1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, false), (1, false), (1, false)]),
    (9, [(1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (0, true)]),
    (4, [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (1, false)])]

@[expose] def witnesses3 : List (Fin 11 × List (ℕ × Bool)) :=
  [(3, []),
    (4, [(1, true), (1, true), (0, true), (1, false), (1, false)]),
    (10, [(1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false)]),
    (7, [(1, true), (0, true), (1, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (1, false)]),
    (5, [(1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (1, true), (1, true), (0, true)]),
    (9, [(0, false), (1, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, false), (1, false), (0, false), (1, true), (0, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true)]),
    (6, [(0, false), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false)]),
    (8, [(1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true)])]

@[expose] noncomputable def stab1 : Subgroup (Perm (Fin 11)) :=
  Blueprint.NativeSporadic.M11 ⊓ MulAction.stabilizer (Perm (Fin 11)) (0 : Fin 11)
@[expose] noncomputable def stab2 : Subgroup (Perm (Fin 11)) :=
  stab1 ⊓ MulAction.stabilizer (Perm (Fin 11)) (1 : Fin 11)
@[expose] noncomputable def stab3 : Subgroup (Perm (Fin 11)) :=
  stab2 ⊓ MulAction.stabilizer (Perm (Fin 11)) (2 : Fin 11)
@[expose] noncomputable def stab4 : Subgroup (Perm (Fin 11)) :=
  stab3 ⊓ MulAction.stabilizer (Perm (Fin 11)) (3 : Fin 11)

theorem witnesses_ok0 : ∀ x ∈ witnesses0, wordProd gen x.2 (0 : Fin 11) = x.1 := by
  decide +kernel
theorem witnesses_ok1 : ∀ x ∈ witnesses1,
    wordProd gen x.2 (0 : Fin 11) = 0 ∧ wordProd gen x.2 (1 : Fin 11) = x.1 := by
  decide +kernel
theorem witnesses_ok2 : ∀ x ∈ witnesses2, wordProd gen x.2 (0 : Fin 11) = 0 ∧
    wordProd gen x.2 (1 : Fin 11) = 1 ∧ wordProd gen x.2 (2 : Fin 11) = x.1 := by
  decide +kernel
theorem witnesses_ok3 : ∀ x ∈ witnesses3, wordProd gen x.2 (0 : Fin 11) = 0 ∧
    wordProd gen x.2 (1 : Fin 11) = 1 ∧ wordProd gen x.2 (2 : Fin 11) = 2 ∧
    wordProd gen x.2 (3 : Fin 11) = x.1 := by
  decide +kernel

theorem witnesses_nodup : (witnesses0.map Prod.fst).Nodup ∧ (witnesses1.map Prod.fst).Nodup ∧
    (witnesses2.map Prod.fst).Nodup ∧ (witnesses3.map Prod.fst).Nodup := by
  decide +kernel

theorem witnesses_length : witnesses0.length = 11 ∧ witnesses1.length = 10 ∧
    witnesses2.length = 9 ∧ witnesses3.length = 8 := by
  decide +kernel

theorem le_card_native : 7920 ≤ Nat.card Blueprint.NativeSporadic.M11 := by
  have h0 := le_card_of_witnesses (K := Blueprint.NativeSporadic.M11) gen 0 witnesses0
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
    (fun x hx => (witnesses_ok3 x hx).2.2.2) witnesses_nodup.2.2.2
  obtain ⟨l0, l1, l2, l3⟩ := witnesses_length
  rw [l0] at h0; rw [l1] at h1; rw [l2] at h2; rw [l3] at h3
  have h4 : 1 ≤ Nat.card ↥stab4 := Nat.card_pos
  change 11 * Nat.card ↥stab1 ≤ Nat.card ↥Blueprint.NativeSporadic.M11 at h0
  change 10 * Nat.card ↥stab2 ≤ Nat.card ↥stab1 at h1
  change 9 * Nat.card ↥stab3 ≤ Nat.card ↥stab2 at h2
  change 8 * Nat.card ↥stab4 ≤ Nat.card ↥stab3 at h3
  omega

@[expose] noncomputable def img (i : ℕ) : ↥Blueprint.NativeSporadic.M11 :=
  if i = 0 then ⟨alpha, alpha_eq ▸ nativeWord_mem _⟩
  else if i = 1 then ⟨beta, beta_eq ▸ nativeWord_mem _⟩ else 1

theorem img_val (i : ℕ) : ((img i : ↥Blueprint.NativeSporadic.M11) : Perm (Fin 11)) =
    if i = 0 then alpha else if i = 1 then beta else 1 := by
  unfold img
  split
  · rfl
  · split <;> rfl

theorem relators_eval : ∀ v ∈ Sporadic.m11Presentation.relatorLetters, wordProd img v = 1 := by
  intro v hv
  apply Subtype.ext
  rw [coe_wordProd, Subgroup.coe_one]
  simp only [img_val]
  revert v
  rw [Sporadic.m11Presentation_relatorLetters]
  decide +kernel

noncomputable def toNative : Sporadic.m11Presentation.Group →* ↥Blueprint.NativeSporadic.M11 :=
  presHom _ img relators_eval

@[expose] def genWord (i : ℕ) : List (ℕ × Bool) :=
  if i = 0 then
    [(0, false), (1, false), (0, false), (1, true), (0, true), (1, true), (1, true), (0, true),
      (0, true), (0, true), (0, true)]
  else [(1, true), (0, true), (1, true), (0, true)]

theorem gen_eq_wordProd : ∀ i ∈ [0, 1],
    gen i = wordProd (fun j => (img j : Perm (Fin 11))) (genWord i) := by
  simp only [img_val]
  decide +kernel

theorem toNative_surjective : Function.Surjective toNative := by
  have hgen : ∀ i ∈ [0, 1], (⟨gen i, gen_mem i⟩ : ↥Blueprint.NativeSporadic.M11) ∈
      toNative.range := by
    intro i hi
    refine ⟨wordProd (presGen _) (genWord i), ?_⟩
    rw [toNative, presHom_wordProd _ img relators_eval (genWord i) (by
      rw [generatorCount_eq]
      rcases List.mem_pair.mp hi with rfl | rfl <;> decide)]
    exact Subtype.ext (by rw [coe_wordProd]; exact (gen_eq_wordProd i hi).symm)
  intro y
  obtain ⟨y, hy⟩ := y
  suffices H : ∀ z (hz : z ∈ Blueprint.NativeSporadic.M11),
      (⟨z, hz⟩ : ↥Blueprint.NativeSporadic.M11) ∈ toNative.range from H y hy
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
    Nonempty (↥Blueprint.NativeSporadic.M11 ≃* SporadicName.M11.Group) := by
  obtain ⟨hfin, hcard⟩ := finite_card_le
  show Nonempty (↥Blueprint.NativeSporadic.M11 ≃* SporadicName.M11.presentation.Group)
  rw [presentation_eq]
  exact nonempty_mulEquiv_of_surjective toNative toNative_surjective hcard le_card_native

end CFSG.Sporadic.Bridge.M11
