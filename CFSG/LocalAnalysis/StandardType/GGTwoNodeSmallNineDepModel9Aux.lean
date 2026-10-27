module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.CFSGNative.TwoNodeSmall.Check

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma pk4_getD_append_zero (l : List ℕ) (j : ℕ) :
    (l ++ [0]).getD j 0 = l.getD j 0 := by
  induction l generalizing j with
  | nil => simp
  | cons a t ih =>
      cases j with
      | zero => simp
      | succ j => simpa using ih j

lemma pk4_allVecs_mem_of_lt : ∀ (l : List ℕ), (∀ x ∈ l, x < 3) → l ∈ allVecs l.length := by
  intro l
  induction l with
  | nil => intro _; simp [allVecs]
  | cons a t ih =>
      intro h
      have ha : a < 3 := h a (by simp)
      have ht : ∀ x ∈ t, x < 3 := fun x hx => h x (by simp [hx])
      rw [List.length_cons]
      simp only [allVecs]
      refine List.mem_flatMap.mpr ⟨t, ih ht, ?_⟩
      simp only [List.mem_map]
      refine ⟨a, ?_, rfl⟩
      interval_cases a <;> simp

private lemma pk4_foldl_cast (l : List (ℕ × ℕ)) (a : ℕ) :
    (((l.map (fun xy => xy.1 * xy.2)).foldl (· + ·) a : ℕ) : ZMod 3) =
      (l.map (fun xy => (xy.1 : ZMod 3) * xy.2)).foldl (· + ·) (a : ZMod 3) := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih (a + x.1 * x.2)]
      push_cast
      ring

private lemma pk4_foldl_range (n : ℕ) (g : ℕ → ZMod 3) :
    (((List.range n).map g).foldl (· + ·) 0) = ∑ i : Fin n, g i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.foldl_append, ih]
      rw [Fin.sum_univ_castSucc]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
        Fin.val_castAdd, Fin.val_castSucc, Fin.val_last]

lemma pk4_pi_single_expand (y : Fin 9 → ZMod 3) :
    y = ∑ j : Fin 9, y j • (Pi.single j 1 : Fin 9 → ZMod 3) := by
  ext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp [Pi.single_apply]
  · intro j _ hj
    simp only [Pi.single_apply]
    rw [if_neg (Ne.symm hj), mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma pk4_getD_eq_getElem (l : List ℕ) {i : ℕ} (h : i < l.length) :
    l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

lemma pk4_getD_append_left (l₁ l₂ : List ℕ) (i : ℕ) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by rw [List.length_append]; omega), List.getElem?_eq_getElem h]
  congr 1
  rw [List.getElem_append_left h]

lemma pk4_getD_append_right (l₁ l₂ : List ℕ) (i : ℕ) (h : l₁.length ≤ i)
    (hi : i < (l₁ ++ l₂).length) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by rw [List.length_append] at hi; omega)]
  congr 1
  rw [List.getElem_append_right h]

lemma pk4_dotv_cast (a b : Vec) (ha : a.length = 9) (hb : b.length = 9) :
    ((dotv a b : ℕ) : ZMod 3) =
      ∑ i : Fin 9, (a.getD i 0 : ZMod 3) * (b.getD i 0 : ZMod 3) := by
  have hzip : (a.zip b).map (fun xy => (xy.1 : ZMod 3) * xy.2) =
      (List.range 9).map (fun i => (a.getD i 0 : ZMod 3) * (b.getD i 0 : ZMod 3)) := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_map, List.getElem?_map]
    by_cases h : i < 9
    · have hia : i < a.length := by omega
      have hib : i < b.length := by omega
      have hai : a[i]? = some a[i] := List.getElem?_eq_getElem hia
      have hbi : b[i]? = some b[i] := List.getElem?_eq_getElem hib
      have hzi : (a.zip b)[i]? = some (a[i], b[i]) :=
        List.getElem?_zip_eq_some.mpr ⟨hai, hbi⟩
      have hga := pk4_getD_eq_getElem a hia
      have hgb := pk4_getD_eq_getElem b hib
      have hri : (List.range 9)[i]? = some i := List.getElem?_range h
      rw [hzi, hri]
      simp only [Option.map_some, hga, hgb]
    · have hzi : (a.zip b)[i]? = none := by
        rw [List.getElem?_eq_none_iff, List.length_zip]; omega
      have hri : (List.range 9)[i]? = none := by
        rw [List.getElem?_eq_none_iff, List.length_range]; omega
      rw [hzi, hri]; simp
  unfold dotv
  rw [ZMod.natCast_mod]
  rw [pk4_foldl_cast]
  rw [hzip]
  exact pk4_foldl_range 9 _

@[expose] def pk4_Tlm (c : Fin 9 → ZMod 3) (d : ZMod 3) :
    (Fin 9 → ZMod 3) →ₗ[ZMod 3] (Fin 9 → ZMod 3) where
  toFun y := fun j => if j = 8 then d⁻¹ * y 8 else y j - c j * d⁻¹ * y 8
  map_add' x y := by
    ext j; by_cases h : j = 8
    · simp only [Pi.add_apply, h, if_pos, mul_add]
    · simp only [Pi.add_apply, h, if_neg, not_false_eq_true]
      ring
  map_smul' a x := by
    ext j; by_cases h : j = 8
    · simp only [Pi.smul_apply, h, if_pos, smul_eq_mul, RingHom.id_apply]
      ring_nf
    · simp only [Pi.smul_apply, h, if_neg, not_false_eq_true, smul_eq_mul, RingHom.id_apply]
      ring_nf

@[expose] def pk4_Slm (c : Fin 9 → ZMod 3) (d : ZMod 3) :
    (Fin 9 → ZMod 3) →ₗ[ZMod 3] (Fin 9 → ZMod 3) where
  toFun y := fun j => if j = 8 then d * y 8 else y j + c j * y 8
  map_add' x y := by
    ext j; by_cases h : j = 8
    · simp only [Pi.add_apply, h, if_pos, mul_add]
    · simp only [Pi.add_apply, h, if_neg, not_false_eq_true]
      ring
  map_smul' a x := by
    ext j; by_cases h : j = 8
    · simp only [Pi.smul_apply, h, if_pos, smul_eq_mul, RingHom.id_apply]
      ring_nf
    · simp only [Pi.smul_apply, h, if_neg, not_false_eq_true, smul_eq_mul, RingHom.id_apply]
      ring_nf

lemma pk4_Tlm_apply (c : Fin 9 → ZMod 3) (d : ZMod 3) (y : Fin 9 → ZMod 3)
    (j : Fin 9) : pk4_Tlm c d y j = if j = 8 then d⁻¹ * y 8 else y j - c j * d⁻¹ * y 8 :=
  rfl

private lemma pk4_Slm_apply (c : Fin 9 → ZMod 3) (d : ZMod 3) (y : Fin 9 → ZMod 3)
    (j : Fin 9) : pk4_Slm c d y j = if j = 8 then d * y 8 else y j + c j * y 8 :=
  rfl

lemma pk4_Tlm_fix (c : Fin 9 → ZMod 3) (d : ZMod 3) (y : Fin 9 → ZMod 3)
    (hy : y 8 = 0) : pk4_Tlm c d y = y := by
  ext j
  rw [pk4_Tlm_apply]
  by_cases h : j = 8
  · subst h; rw [if_pos rfl, hy, mul_zero]
  · rw [if_neg h, hy, mul_zero, sub_zero]

lemma pk4_Tlm_Slm (c : Fin 9 → ZMod 3) (d : ZMod 3) (hd : d ≠ 0)
    (y : Fin 9 → ZMod 3) : pk4_Slm c d (pk4_Tlm c d y) = y := by
  ext j
  rw [pk4_Slm_apply]
  by_cases h : j = 8
  · subst h
    rw [if_pos rfl, pk4_Tlm_apply c d y (8 : Fin 9), if_pos rfl]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  · rw [if_neg h, pk4_Tlm_apply c d y j, pk4_Tlm_apply c d y (8 : Fin 9),
      if_neg h, if_pos (rfl : (8 : Fin 9) = 8)]
    ring

lemma pk4_Slm_Tlm (c : Fin 9 → ZMod 3) (d : ZMod 3) (hd : d ≠ 0)
    (y : Fin 9 → ZMod 3) : pk4_Tlm c d (pk4_Slm c d y) = y := by
  ext j
  rw [pk4_Tlm_apply]
  by_cases h : j = 8
  · subst h
    rw [if_pos rfl, pk4_Slm_apply c d y (8 : Fin 9), if_pos rfl]
    rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  · have hz : c j * d⁻¹ * (d * y 8) = c j * y 8 := by
      rw [mul_assoc (c j) d⁻¹ (d * y 8), ← mul_assoc d⁻¹ d (y 8),
        inv_mul_cancel₀ hd, one_mul]
    rw [if_neg h, pk4_Slm_apply c d y j, pk4_Slm_apply c d y (8 : Fin 9),
      if_neg h, if_pos (rfl : (8 : Fin 9) = 8), hz]
    ring

lemma pk4_hvec8_length (k : ℕ) : (hvec8 k).length = 8 := by
  unfold hvec8
  split <;> simp

@[expose] def pk4_nonJ (e : ℕ) : List ℕ := (List.range 8).filter fun k => !(embJ e).contains k

@[expose] def pk4_uc (e : ℕ) (o : ℕ × ℕ × ℕ) (us : Vec) : Vec :=
  (List.range 8).map fun k =>
    match (embJ e).zipIdx.find? (fun jj => jj.1 == k) with
    | some jj => (if jj.2 = o.1 then o.2.1 else 0)
    | none => us.getD (((pk4_nonJ e).zipIdx.find? (fun bb => bb.1 == k)).map (·.2) |>.getD 0) 0

lemma pk4_val_cast (x : ZMod 3) : ((x.val : ℕ) : ZMod 3) = x :=
  ZMod.natCast_zmod_val x

private lemma pk4_val_hH {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (α : Fin 8 → Module.Dual (ZMod 3) V) (ha : V) (s : ℕ) (o : ℕ × ℕ × ℕ)
    (ho1 : o.2.1 < 3)
    (hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3))
    (j : Fin 8) (h1 : s ≤ (j : ℕ)) (h2 : (j : ℕ) < s + 6) :
    (α j ha).val = (if (j : ℕ) - s = o.1 then o.2.1 else 0) := by
  rw [hH j h1 h2]
  rw [ZMod.val_cast_of_lt]
  split <;> omega

private lemma pk4_val_hA {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (αa : Module.Dual (ZMod 3) V) (h : Fin 8 → V) (s : ℕ) (o : ℕ × ℕ × ℕ)
    (ho2 : o.2.2 < 3)
    (hA : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod 3))
    (j : Fin 8) (h1 : s ≤ (j : ℕ)) (h2 : (j : ℕ) < s + 6) :
    (αa (h j)).val = (if (j : ℕ) - s = o.1 then o.2.2 else 0) := by
  rw [hA j h1 h2]
  rw [ZMod.val_cast_of_lt]
  split <;> omega

lemma pk4_hjj_mem (s : ℕ) (jj : ℕ × ℕ) (h : jj ∈ (embJ s).zipIdx) :
    jj.1 = s + jj.2 ∧ jj.2 < 6 := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  rw [embJ, List.getElem?_map] at h
  by_cases hlt : jj.2 < 6
  · rw [List.getElem?_range hlt] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨by omega, hlt⟩
  · have hnone : (List.range 6)[jj.2]? = none := by
      rw [List.getElem?_eq_none_iff, List.length_range]; omega
    rw [hnone] at h
    simp at h

@[expose] def pk4_alphaNat {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (α : Fin 8 → Module.Dual (ZMod 3) V) (ha : V) (k : ℕ) : ZMod 3 :=
  if h : k < 8 then α ⟨k, h⟩ ha else 0

private lemma pk4_alphaNat_val_hH {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (α : Fin 8 → Module.Dual (ZMod 3) V) (ha : V) (s : ℕ) (o : ℕ × ℕ × ℕ)
    (ho1 : o.2.1 < 3)
    (hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3))
    (k : ℕ) (hk : k < 8) (h1 : s ≤ k) (h2 : k < s + 6) :
    (pk4_alphaNat α ha k).val = (if k - s = o.1 then o.2.1 else 0) := by
  rw [pk4_alphaNat, dif_pos hk]
  exact pk4_val_hH α ha s o ho1 hH ⟨k, hk⟩ h1 h2

lemma pk4_u_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (α : Fin 8 → Module.Dual (ZMod 3) V) (ha : V) (s : ℕ) (hs : s ≤ 2) (o : ℕ × ℕ × ℕ)
    (ho1 : o.2.1 < 3)
    (hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3)) :
    pk4_uc s o ((pk4_nonJ s).map (fun k => (pk4_alphaNat α ha k).val)) =
      (List.range 8).map (fun k => (pk4_alphaNat α ha k).val) := by
  interval_cases s
  · have hJ : (embJ 0).zipIdx = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)] := by decide
    have hNJ : pk4_nonJ 0 = [6, 7] := by decide
    apply List.ext_getElem
    · simp [pk4_uc, List.length_map, List.length_range]
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1 h2
      interval_cases i <;>
        simp [pk4_uc, hJ, hNJ, List.getElem_map, List.getElem_range,
          List.find?, List.find?_cons_of_pos, List.find?_cons_of_neg, List.find?_nil,
          pk4_alphaNat, pk4_val_hH α ha 0 o ho1 hH]
  · have hJ : (embJ 1).zipIdx = [(1, 0), (2, 1), (3, 2), (4, 3), (5, 4), (6, 5)] := by decide
    have hNJ : pk4_nonJ 1 = [0, 7] := by decide
    apply List.ext_getElem
    · simp [pk4_uc, List.length_map, List.length_range]
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1 h2
      interval_cases i <;>
        simp [pk4_uc, hJ, hNJ, List.getElem_map, List.getElem_range,
          List.find?, List.find?_cons_of_pos, List.find?_cons_of_neg, List.find?_nil,
          pk4_alphaNat, pk4_val_hH α ha 1 o ho1 hH]
  · have hJ : (embJ 2).zipIdx = [(2, 0), (3, 1), (4, 2), (5, 3), (6, 4), (7, 5)] := by decide
    have hNJ : pk4_nonJ 2 = [0, 1] := by decide
    apply List.ext_getElem
    · simp [pk4_uc, List.length_map, List.length_range]
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1 h2
      interval_cases i <;>
        simp [pk4_uc, hJ, hNJ, List.getElem_map, List.getElem_range,
          List.find?, List.find?_cons_of_pos, List.find?_cons_of_neg, List.find?_nil,
          pk4_alphaNat, pk4_val_hH α ha 2 o ho1 hH]

lemma pk4_hvec8_getD_lt (k : ℕ) (hk : k < 7) (t : ℕ) :
    (hvec8 k).getD t 0 = if t = k then 1 else 0 := by
  rw [hvec8, if_pos hk]
  by_cases ht : t < 8
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
    simp
  · have hnone : (List.range 8)[t]? = none := by
      rw [List.getElem?_eq_none_iff, List.length_range]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hnone]
    simp only [Option.map_none, Option.getD_none]
    rw [if_neg (by omega : ¬ t = k)]

lemma pk4_alpha8_getD_seven (k : ℕ) : (alpha8 k).getD 7 0 = 0 := by
  unfold alpha8
  rw [pk4_getD_append_right ((List.range 7).map (fun j => cl k j)) [0] 7
    (by simp) (by simp)]
  simp

end CFSG.TwoNodeSmall
