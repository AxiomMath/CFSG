module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelRefl36
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelOrbit

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private lemma evalWord_append {n : ℕ} (g : Fin n → Mat6) (l₁ l₂ : List (Fin n)) :
    evalWord g (l₁ ++ l₂) = evalWord g l₁ * evalWord g l₂ := by
  induction l₁ with
  | nil => simp [evalWord]
  | cons i l ih =>
      simp only [List.cons_append, evalWord, ih, mul_assoc]

private lemma evalWord_singleton (i : Fin 6) : evalWord gensL [i] = gensL i := by
  simp [evalWord]

private lemma evalWord_mem_closureL (l : List (Fin 6)) : evalWord gensL l ∈ closureL := by
  induction l with
  | nil => exact Submonoid.one_mem _
  | cons i l ih =>
      have hi : gensL i ∈ closureL :=
        Submonoid.subset_closure (show gensL i ∈ Set.range gensL from ⟨i, rfl⟩)
      exact Submonoid.mul_mem closureL hi ih

private lemma gensL_mul_self : ∀ i : Fin 6, gensL i * gensL i = 1 := by
  decide +kernel

private lemma evalWord_reverse_both (l : List (Fin 6)) :
    evalWord gensL l * evalWord gensL l.reverse = 1 ∧
      evalWord gensL l.reverse * evalWord gensL l = 1 := by
  induction l with
  | nil => simp [evalWord]
  | cons i l ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · calc
          evalWord gensL (i :: l) * evalWord gensL (i :: l).reverse
              = (gensL i * evalWord gensL l) * (evalWord gensL l.reverse * gensL i) := by
                  rw [List.reverse_cons, evalWord_append, evalWord_singleton]
                  rw [show evalWord gensL (i :: l) = gensL i * evalWord gensL l from rfl]
          _ = gensL i * (evalWord gensL l * evalWord gensL l.reverse) * gensL i := by
                  ac_rfl
          _ = 1 := by
                  rw [h1, mul_one, gensL_mul_self i]
      · calc
          evalWord gensL (i :: l).reverse * evalWord gensL (i :: l)
              = (evalWord gensL l.reverse * gensL i) * (gensL i * evalWord gensL l) := by
                  rw [List.reverse_cons, evalWord_append, evalWord_singleton]
                  rw [show evalWord gensL (i :: l) = gensL i * evalWord gensL l from rfl]
          _ = evalWord gensL l.reverse * (gensL i * gensL i) * evalWord gensL l := by
                  ac_rfl
          _ = 1 := by
                  rw [gensL_mul_self i, mul_one, h2]

private theorem closureL_fix_x {g : Mat6} (hg : g ∈ closureL) :
    g.mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    revert i
    decide +kernel
  | one => rw [Matrix.one_mulVec]
  | mul g h _ _ ihg ihh => rw [← Matrix.mulVec_mulVec, ihh, ihg]

theorem exists_word_of_mem_closureL {k : Mat6} (hk : k ∈ closureL) :
    ∃ word : List (Fin 6), evalWord gensL word = k := by
  induction hk using Submonoid.closure_induction with
  | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact ⟨[i], evalWord_singleton i⟩
  | one => exact ⟨[], rfl⟩
  | mul g h _ _ ihg ihh =>
      obtain ⟨w₁, hw₁⟩ := ihg
      obtain ⟨w₂, hw₂⟩ := ihh
      exact ⟨w₁ ++ w₂, by rw [evalWord_append, hw₁, hw₂]⟩

theorem evalWord_gensL_mem (word : List (Fin 6)) : evalWord gensL word ∈ closureL :=
  evalWord_mem_closureL word

theorem evalWord_gensL_mul_reverse (word : List (Fin 6)) :
    evalWord gensL word * evalWord gensL word.reverse = 1 ∧
      evalWord gensL word.reverse * evalWord gensL word = 1 :=
  evalWord_reverse_both word

theorem closureL_exists_inv {k : Mat6} (hk : k ∈ closureL) :
    ∃ k' ∈ closureL, k * k' = 1 ∧ k' * k = 1 := by
  obtain ⟨w, hw⟩ := exists_word_of_mem_closureL hk
  refine ⟨evalWord gensL w.reverse, evalWord_gensL_mem w.reverse, ?_, ?_⟩
  · rw [← hw]
    exact (evalWord_gensL_mul_reverse w).1
  · rw [← hw]
    exact (evalWord_gensL_mul_reverse w).2

theorem ggE6DepCoord_change {Bs L : Subgroup G} {x : G} {hxBs : x ∈ Bs}
    {ι : Additive ↥Bs ≃+ Vec6} (h : GGE6DepCoord Bs L x hxBs ι) {k : Mat6} (hk : k ∈ closureL) :
    ∃ ι' : Additive ↥Bs ≃+ Vec6,
      (∀ b : ↥Bs, ι' (Additive.ofMul b) = k.mulVec (ι (Additive.ofMul b))) ∧
        GGE6DepCoord Bs L x hxBs ι' := by
  obtain ⟨k', hk', hkk', hk'k⟩ := closureL_exists_inv hk
  obtain ⟨hιx, hιL, hActs, hSurj⟩ := h
  refine ⟨ι.trans
    { toFun := fun v => k.mulVec v
      invFun := fun v => k'.mulVec v
      left_inv := fun v => by
        show k'.mulVec (k.mulVec v) = v
        rw [Matrix.mulVec_mulVec, hk'k, Matrix.one_mulVec]
      right_inv := fun v => by
        show k.mulVec (k'.mulVec v) = v
        rw [Matrix.mulVec_mulVec, hkk', Matrix.one_mulVec]
      map_add' := fun v w => Matrix.mulVec_add k v w }, ?_, ?_⟩
  · intro b
    rw [AddEquiv.trans_apply]
    rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [AddEquiv.trans_apply]
      show k.mulVec (ι (Additive.ofMul ⟨x, hxBs⟩)) = Pi.single 5 1
      rw [hιx, closureL_fix_x hk]
    · intro b
      rw [AddEquiv.trans_apply]
      show (b : G) ∈ L ↔ (k.mulVec (ι (Additive.ofMul b))) 5 = 0
      rw [closureL_apply_five hk]
      exact hιL b
    · intro φ hφ
      obtain ⟨g, hg, hAct⟩ := hActs φ hφ
      refine ⟨k * g * k', Submonoid.mul_mem closureL (Submonoid.mul_mem closureL hk hg) hk', ?_⟩
      intro b
      rw [AddEquiv.trans_apply]
      show k.mulVec (ι (Additive.ofMul (φ b))) =
        (k * g * k').mulVec (k.mulVec (ι (Additive.ofMul b)))
      rw [hAct b]
      have hL : k.mulVec (g.mulVec (ι (Additive.ofMul b))) =
          (k * g).mulVec (ι (Additive.ofMul b)) := by
        rw [Matrix.mulVec_mulVec]
      have hR : (k * g * k').mulVec (k.mulVec (ι (Additive.ofMul b))) =
          (k * g).mulVec (ι (Additive.ofMul b)) := by
        have h1 : (k * g * k').mulVec (k.mulVec (ι (Additive.ofMul b))) =
            (k * g).mulVec (k'.mulVec (k.mulVec (ι (Additive.ofMul b)))) := by
          rw [← Matrix.mulVec_mulVec]
        rw [h1]
        have h2 : k'.mulVec (k.mulVec (ι (Additive.ofMul b))) =
            (k' * k).mulVec (ι (Additive.ofMul b)) := by
          rw [Matrix.mulVec_mulVec]
        rw [h2, hk'k, Matrix.one_mulVec]
      rw [hL, hR]
    · intro g hg
      have hg₀ : k' * g * k ∈ closureL :=
        Submonoid.mul_mem closureL (Submonoid.mul_mem closureL hk' hg) hk
      obtain ⟨φ, hφ, hAct⟩ := hSurj (k' * g * k) hg₀
      refine ⟨φ, hφ, ?_⟩
      intro b
      rw [AddEquiv.trans_apply]
      show k.mulVec (ι (Additive.ofMul (φ b))) =
        g.mulVec (k.mulVec (ι (Additive.ofMul b)))
      rw [hAct b]
      have hL : k.mulVec ((k' * g * k).mulVec (ι (Additive.ofMul b))) =
          g.mulVec (k.mulVec (ι (Additive.ofMul b))) := by
        rw [Matrix.mulVec_mulVec]
        have hm : k * (k' * g * k) = g * k := by
          calc
            k * (k' * g * k) = k * (k' * g) * k := (mul_assoc k (k' * g) k).symm
            _ = ((k * k') * g) * k := by rw [← mul_assoc]
            _ = (1 * g) * k := by rw [hkk']
            _ = g * k := by rw [one_mul]
        rw [hm, ← Matrix.mulVec_mulVec]
      rw [hL]

end E6Dep

end CFSG.StandardType

end
