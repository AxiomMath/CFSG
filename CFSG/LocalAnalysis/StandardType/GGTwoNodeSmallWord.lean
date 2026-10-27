module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSem
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma tnw_foldl_range_map (p D : ℕ) (F : ℕ → ℕ) :
    ((((List.range D).map F).foldl (· + ·) 0 : ℕ) : ZMod p)
      = ∑ i : Fin D, (F i.val : ZMod p) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [Nat.cast_add, ih, Fin.sum_univ_castSucc]
      simp

private lemma tnw_getD_range_map (D : ℕ) (F : ℕ → ℕ) (j : Fin D) :
    (((List.range D).map F).getD j.val 0) = F j.val := by
  have hlen : j.val < ((List.range D).map F).length := by simpa using j.isLt
  rw [List.getD_eq_getElem _ 0 hlen, List.getElem_map]
  have hr : (List.range D)[j.val] = j.val :=
    List.getElem_range (j := j.val) (by simpa using j.isLt)
  rw [hr]

private lemma tnw_cast_refl_coord (p a b : ℕ) (hp : 0 < p) :
    (((a + (p - b % p)) % p : ℕ) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (Nat.mod_lt b hp))]
  rw [ZMod.natCast_mod, ZMod.natCast_self]
  ring

private lemma tnw_dot_add (P : Pt) (f x y : P.V) :
    P.dot f (x + y) = P.dot f x + P.dot f y := by
  simp only [Pt.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma tnw_dot_sub (P : Pt) (f x y : P.V) :
    P.dot f (x - y) = P.dot f x - P.dot f y := by
  simp only [Pt.dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma tnw_dot_smul (P : Pt) (f x : P.V) (a : ZMod P.p) :
    P.dot f (a • x) = a * P.dot f x := by
  simp only [Pt.dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private noncomputable def tnw_reflLM (P : Pt) [Fact P.p.Prime] (r : Refl) :
    P.V →ₗ[ZMod P.p] P.V where
  toFun w := w - P.dot (P.vec r.f) w • P.vec r.h
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, tnw_dot_add]
    ring
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, RingHom.id_apply, tnw_dot_smul]
    ring

private lemma tnw_reflLM_involutive (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) :
    Function.Involutive (tnw_reflLM P r) := by
  intro w
  have hd : P.dot (P.vec r.f) (P.vec r.h) = 2 := hwf r hr
  have h2 : P.dot (P.vec r.f) (w - P.dot (P.vec r.f) w • P.vec r.h)
      = -(P.dot (P.vec r.f) w) := by
    rw [tnw_dot_sub, tnw_dot_smul, hd]
    ring
  show (w - P.dot (P.vec r.f) w • P.vec r.h)
      - P.dot (P.vec r.f) (w - P.dot (P.vec r.f) w • P.vec r.h) • P.vec r.h = w
  rw [h2, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem Pt.dotv_spec (P : Pt) [Fact P.p.Prime] (f v : Vec) :
    ((P.dotv f v : ℕ) : ZMod P.p) = P.dot (P.vec f) (P.vec v) := by
  simp only [Pt.dotv]
  rw [ZMod.natCast_mod, tnw_foldl_range_map]
  simp only [Pt.dot, Pt.vec, Nat.cast_mul]

theorem Pt.vec_applyRefl (P : Pt) [Fact P.p.Prime] (r : Refl) (v : Vec) :
    P.vec (P.applyRefl r v) = P.vec v - P.dot (P.vec r.f) (P.vec v) • P.vec r.h := by
  have hp : 0 < P.p := (Fact.out (p := P.p.Prime)).pos
  funext j
  rw [← Pt.dotv_spec P r.f v]
  simp only [Pt.vec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Pt.applyRefl]
  rw [tnw_getD_range_map]
  rw [tnw_cast_refl_coord P.p (v.getD j.val 0)
    (P.dotv r.f v * r.h.getD j.val 0) hp, Nat.cast_mul]

theorem Pt.vec_unit (P : Pt) [Fact P.p.Prime] (i : Fin P.D) :
    P.vec (P.unit i) = Pi.single i 1 := by
  funext j
  simp only [Pt.vec, Pt.unit]
  rw [tnw_getD_range_map]
  rw [Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · have hv : j.val ≠ i.val := fun hh => h (Fin.ext hh)
    rw [if_neg hv, if_neg h]
    simp

private lemma tnw_exists_genSet_of_wf (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl)
    (hr : r ∈ P.gens) :
    ∃ e ∈ P.genSet, ∀ v : Vec, e (P.vec v) = P.vec (P.applyRefl r v) := by
  refine ⟨LinearEquiv.ofInvolutive (tnw_reflLM P r) (tnw_reflLM_involutive P hwf r hr), ?_, ?_⟩
  · refine ⟨r, hr, fun w => ?_⟩
    rfl
  · intro v
    rw [Pt.vec_applyRefl]
    rfl

theorem Pt.applyWord_spec (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (w : Word)
    (hw : P.wordOK w = true) :
    ∃ γ ∈ P.group, ∀ v : Vec, γ (P.vec v) = P.vec (P.applyWord w v) := by
  revert hw
  induction w with
  | nil =>
      intro _
      refine ⟨1, P.group.one_mem, ?_⟩
      intro v
      simp only [Pt.applyWord, List.foldr_nil]
      rfl
  | cons i w ih =>
      intro hw
      have hw' : i < P.gens.length ∧ P.wordOK w = true := by
        simpa [Pt.wordOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] using hw
      obtain ⟨γw, hγw_mem, hγw⟩ := ih hw'.2
      obtain ⟨e, he_gen, he⟩ :=
        tnw_exists_genSet_of_wf P hwf (P.gens[i]'hw'.1) (List.getElem_mem hw'.1)
      refine ⟨e * γw, P.group.mul_mem (Subgroup.subset_closure he_gen) hγw_mem, ?_⟩
      intro v
      rw [LinearEquiv.mul_apply, hγw, he]
      have hword : P.applyWord (i :: w) v
          = P.applyRefl (P.gens[i]'hw'.1) (P.applyWord w v) := by
        simp only [Pt.applyWord, List.foldr_cons, List.getElem?_eq_getElem hw'.1]
      rw [hword]

theorem Pt.exists_genSet_of_wf (P : Pt) [Fact P.p.Prime] (hwf : P.WF) (r : Refl) (hr : r ∈ P.gens) :
    ∃ e ∈ P.genSet, ∀ v : Vec, e (P.vec v) = P.vec (P.applyRefl r v) :=
  tnw_exists_genSet_of_wf P hwf r hr

end CFSG.TwoNodeSmall
