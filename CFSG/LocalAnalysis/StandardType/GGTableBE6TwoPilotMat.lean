module

public import CFSG.Monster.B.Classical.E6AdjointGroup
public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Monster.B.Classical.E6Adjoint

namespace E6TwoMat

@[expose] def colX (a b : ℕ) : ℕ :=
  (1 <<< b) ^^^ brMask a b ^^^ (if fbit a b then 1 <<< a else 0)

@[expose] def actX (a m : ℕ) : ℕ :=
  xorMap (fun b => if m.testBit b then colX a b else 0) (List.range 78)

@[expose] def actXF (a : ℕ) : ℕ → ℕ → ℕ
  | 0, m => actX a m
  | f + 1, m =>
    if m = 0 then 0
    else (if Nat.log2 m < 78 then colX a (Nat.log2 m) else 0) ^^^
      actXF a f (m ^^^ (1 <<< Nat.log2 m))

@[expose] def actW (w : List ℕ) (m : ℕ) : ℕ :=
  w.foldr (fun a m => actXF a 78 m) m

@[expose] def validWord (w : List ℕ) : Bool :=
  w.all fun a => decide (6 ≤ a) && decide (a < 78)

@[expose] def wordsAgree (w₁ w₂ : List ℕ) : Bool :=
  validWord w₁ && validWord w₂ &&
    (List.range 78).all fun b => actW w₁ (1 <<< b) == actW w₂ (1 <<< b)

@[expose] def rootOf (a : ℕ) : Fin Tag.E6.rank → ℤ :=
  e6Certificate.root (a - 6)

theorem sum_fin_eq_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ k : Fin n, g k = ((List.range n).map g).sum := by
  rw [Fin.sum_univ_eq_sum_range, Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range,
    Multiset.map_coe, Multiset.sum_coe]

theorem validWord_cons {a : ℕ} {w : List ℕ} (h : validWord (a :: w) = true) :
    (6 ≤ a ∧ a < 78) ∧ validWord w = true := by
  simp only [validWord, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, h.2⟩

@[expose] noncomputable def wordElt (K : Type) [Field K] (w : List ℕ) : ModGL .E6 K :=
  (w.map fun a => pinnedX .E6 K (rootOf a) 1).prod

theorem wordElt_nil (K : Type) [Field K] : wordElt K [] = 1 :=
  rfl

theorem wordElt_cons (K : Type) [Field K] (a : ℕ) (w : List ℕ) :
    wordElt K (a :: w) = pinnedX .E6 K (rootOf a) 1 * wordElt K w :=
  rfl

theorem wordElt_append (K : Type) [Field K] (w₁ w₂ : List ℕ) :
    wordElt K (w₁ ++ w₂) = wordElt K w₁ * wordElt K w₂ := by
  rw [wordElt, wordElt, wordElt, List.map_append, List.prod_append]

theorem isRoot_rootOf (a : Fin 78) (ha : 6 ≤ (a : ℕ)) : IsRoot Tag.E6 (rootOf a) :=
  isRoot_certRoot (by omega)

theorem rootVec_rootOf (K : Type) [Field K] (a : Fin 78) (ha : 6 ≤ (a : ℕ)) :
    rootVec Tag.E6 K (rootOf a) = Finsupp.single (lab a) 1 := by
  rw [lab_of_ge (by omega), rootOf, rootVec_eq_single (isRoot_certRoot (by omega))]

variable {K : Type} [Field K] [CharP K 2]

theorem pinnedX_single_lab (a b : Fin 78) (ha : 6 ≤ (a : ℕ)) :
    (pinnedX .E6 K (rootOf a) 1 : Module.End K (RootModule .E6 K)) (Finsupp.single (lab b) 1) =
      toVec K (colX a b) := by
  rw [pinnedX_eq (isRoot_rootOf a ha), rootVec_rootOf K a ha]
  simp only [one_smul, one_pow, LinearMap.add_apply, Module.End.one_apply, ad_apply,
    formTensor_apply]
  rw [bracket_lab, form_lab, colX, toVec_xor, toVec_xor, toVec_one_shiftLeft b, toVec_ite,
    toVec_one_shiftLeft a]

theorem pinnedX_toVec (a : Fin 78) (ha : 6 ≤ (a : ℕ)) (m : ℕ) :
    (pinnedX .E6 K (rootOf a) 1 : Module.End K (RootModule .E6 K)) (toVec K m) =
      toVec K (actX a m) := by
  rw [actX, toVec_xorMap, toVec, map_sum, ← sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : m.testBit k
  · simp only [hk, ↓reduceIte]
    exact pinnedX_single_lab a k ha
  · simp only [hk, Bool.false_eq_true, ↓reduceIte, map_zero, toVec_zero]

omit [CharP K 2]
  in
theorem toVec_one_shiftLeft_of_ge {k : ℕ} (hk : 78 ≤ k) : toVec K (1 <<< k) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have : (1 <<< k).testBit i = false := by
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    exact decide_eq_false (by omega)
  rw [this]
  rfl

theorem pinnedX_toVec_actXF (a : Fin 78) (ha : 6 ≤ (a : ℕ)) (f m : ℕ) :
    (pinnedX .E6 K (rootOf a) 1 : Module.End K (RootModule .E6 K)) (toVec K m) =
      toVec K (actXF a f m) := by
  induction f generalizing m with
  | zero => exact pinnedX_toVec a ha m
  | succ f ih =>
    by_cases hm : m = 0
    · subst hm
      simp only [actXF, ↓reduceIte, toVec_zero, map_zero]
    · simp only [actXF, hm, ↓reduceIte]
      rw [toVec_xor, ← ih]
      have e : m = (1 <<< Nat.log2 m) ^^^ (m ^^^ (1 <<< Nat.log2 m)) := by
        rw [Nat.xor_comm m, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      conv_lhs => rw [e, toVec_xor, map_add]
      congr 1
      by_cases hk : Nat.log2 m < 78
      · simp only [hk, ↓reduceIte]
        rw [toVec_one_shiftLeft' hk]
        exact pinnedX_single_lab a ⟨_, hk⟩ ha
      · simp only [hk, ↓reduceIte]
        rw [toVec_zero, toVec_one_shiftLeft_of_ge (by omega), map_zero]

theorem wordElt_toVec {w : List ℕ} (hw : validWord w = true) (m : ℕ) :
    (wordElt K w : Module.End K (RootModule .E6 K)) (toVec K m) = toVec K (actW w m) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨⟨ha6, ha78⟩, hw'⟩ := validWord_cons hw
    rw [wordElt_cons, Units.val_mul, Module.End.mul_apply, ih hw']
    exact pinnedX_toVec_actXF ⟨a, ha78⟩ ha6 78 _

theorem wordElt_eq_of_wordsAgree {w₁ w₂ : List ℕ} (h : wordsAgree w₁ w₂ = true) :
    wordElt K w₁ = wordElt K w₂ := by
  simp only [wordsAgree, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨h₁, h₂⟩, h⟩ := h
  apply Units.ext
  refine ext_lab fun b => ?_
  rw [← toVec_one_shiftLeft b, wordElt_toVec h₁, wordElt_toVec h₂, h b b.2]

end E6TwoMat

end CFSG.StandardType
