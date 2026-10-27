module

public import TauCeti.GroupTheory.Coxeter.Dihedral
public import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] (cs : CoxeterSystem M W)

theorem leftInvSeq_append (α β : List ι) :
    cs.leftInvSeq (α ++ β) =
      cs.leftInvSeq α ++ (cs.leftInvSeq β).map (MulAut.conj (cs.wordProd α)) := by
  induction α with
  | nil =>
    simp only [List.nil_append, leftInvSeq_nil, cs.wordProd_nil, map_one]
    exact (List.map_id' _).symm
  | cons i α ih =>
    simp only [List.cons_append, leftInvSeq, ih, List.map_append, List.map_map,
      List.cons_append, List.cons.injEq, true_and, List.append_cancel_left_eq]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, MulAut.conj_apply, cs.wordProd_cons, mul_inv_rev,
      mul_assoc]

theorem length_inv_mul_add_length_of_forall {J : Set ι} {m : W}
    (hm : ∀ t ∈ cs.parabolic J, cs.IsReflection t → cs.length (t * m) < cs.length m)
    {x : W} (hx : x ∈ cs.parabolic J) : cs.length (x⁻¹ * m) + cs.length x = cs.length m := by
  obtain ⟨ω, hred, hJ, rfl⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hx
  clear hx
  induction ω using List.reverseRecOn with
  | nil => simp
  | append_singleton ω i ih =>
    have hred' : cs.IsReduced ω := by simpa using hred.take ω.length
    have hJ' : ∀ j ∈ ω, j ∈ J := fun j hj => hJ j (by simp [hj])
    have hi : i ∈ J := hJ i (by simp)
    have IH := ih hred' hJ'
    have hx' : cs.wordProd ω ∈ cs.parabolic J := cs.wordProd_mem_parabolic hJ'
    have hlen : cs.length (cs.wordProd (ω ++ [i])) = ω.length + 1 := by
      simpa using hred.eq
    have hprod : cs.wordProd (ω ++ [i]) = cs.wordProd ω * cs.simple i := by
      rw [cs.wordProd_append, cs.wordProd_singleton]
    set x' := cs.wordProd ω with hx'def
    set y := x'⁻¹ * m with hy
    have hxy : x' * y = m := by rw [hy, mul_inv_cancel_left]
    set t := x' * cs.simple i * x'⁻¹ with ht
    have htJ : t ∈ cs.parabolic J :=
      mul_mem (mul_mem hx' (cs.simple_mem_parabolic hi)) (inv_mem hx')
    have htr : cs.IsReflection t := ⟨x', i, rfl⟩
    have htm := hm t htJ htr
    obtain ⟨β, hβ, hβy⟩ := cs.exists_isReduced y
    have hcat : cs.IsReduced (ω ++ β) := by
      change cs.length (cs.wordProd (ω ++ β)) = (ω ++ β).length
      rw [cs.wordProd_append, ← hβy, hxy, List.length_append, ← hred'.eq, ← hx'def,
        ← hβ.eq, ← hβy, ← IH, add_comm]
    have hmem : t ∈ cs.leftInvSeq (ω ++ β) := by
      rw [cs.mem_leftInvSeq_iff_isLeftInversion hcat, cs.wordProd_append, ← hβy, hxy]
      exact ⟨htr, htm⟩
    rw [leftInvSeq_append, List.mem_append] at hmem
    rcases hmem with h1 | h2
    · exfalso
      have hinv := cs.isLeftInversion_of_mem_leftInvSeq hred' h1
      have htx : t * x' = cs.wordProd (ω ++ [i]) := by
        rw [hprod, ht, inv_mul_cancel_right]
      have := hinv.2
      rw [← hx'def, htx, hlen, hred'.eq] at this
      omega
    · obtain ⟨r, hr, hrt⟩ := List.mem_map.mp h2
      have hr' : r = cs.simple i := by
        rw [MulAut.conj_apply, ← hx'def, ht] at hrt
        simpa using hrt
      rw [hr'] at hr
      have hinv := cs.isLeftInversion_of_mem_leftInvSeq hβ hr
      rw [← hβy] at hinv
      have hdesc : cs.length (cs.simple i * y) + 1 = cs.length y := by
        rcases cs.length_simple_mul y i with h | h
        · have := hinv.2
          omega
        · exact h
      have hxm : (cs.wordProd (ω ++ [i]))⁻¹ * m = cs.simple i * y := by
        rw [hprod, hy, mul_inv_rev, cs.inv_simple, mul_assoc]
      rw [hxm, hlen, ← hred'.eq, ← hx'def]
      omega

@[expose] def IsLongest (J : Set ι) (w : W) : Prop :=
  w ∈ cs.parabolic J ∧ ∀ v ∈ cs.parabolic J, cs.length v ≤ cs.length w

variable {cs}

theorem IsLongest.length_mul_lt {J : Set ι} {w : W} (hw : IsLongest cs J w) {t : W}
    (htJ : t ∈ cs.parabolic J) (ht : cs.IsReflection t) : cs.length (t * w) < cs.length w :=
  lt_of_le_of_ne (hw.2 _ (mul_mem htJ hw.1)) (ht.length_mul_right_ne w)

theorem IsLongest.length_inv_mul {J : Set ι} {w : W} (hw : IsLongest cs J w) {x : W}
    (hx : x ∈ cs.parabolic J) : cs.length (x⁻¹ * w) + cs.length x = cs.length w :=
  length_inv_mul_add_length_of_forall cs (fun _ htJ ht => hw.length_mul_lt htJ ht) hx

theorem IsLongest.unique {J : Set ι} {w w' : W} (hw : IsLongest cs J w)
    (hw' : IsLongest cs J w') : w = w' := by
  have h := hw'.length_inv_mul hw.1
  have h1 := hw.2 _ hw'.1
  have h2 := hw'.2 _ hw.1
  have h0 : cs.length (w⁻¹ * w') = 0 := by omega
  rw [cs.length_eq_zero_iff] at h0
  exact (inv_mul_eq_one.mp h0)

theorem IsLongest.inv {J : Set ι} {w : W} (hw : IsLongest cs J w) : IsLongest cs J w⁻¹ :=
  ⟨inv_mem hw.1, fun v hv => by rw [cs.length_inv]; exact hw.2 v hv⟩

theorem IsLongest.inv_eq {J : Set ι} {w : W} (hw : IsLongest cs J w) : w⁻¹ = w :=
  hw.inv.unique hw

theorem IsLongest.mul_self {J : Set ι} {w : W} (hw : IsLongest cs J w) : w * w = 1 := by
  have h := mul_inv_cancel w
  rwa [hw.inv_eq] at h

theorem IsLongest.length_mul {J : Set ι} {w : W} (hw : IsLongest cs J w) {x : W}
    (hx : x ∈ cs.parabolic J) : cs.length (w * x) + cs.length x = cs.length w := by
  have h := hw.length_inv_mul hx
  rwa [← cs.length_inv (x⁻¹ * w), mul_inv_rev, inv_inv, hw.inv_eq] at h

theorem IsLongest.length_mul_left {J : Set ι} {w : W} (hw : IsLongest cs J w) {x : W}
    (hx : x ∈ cs.parabolic J) : cs.length (x * w) + cs.length x = cs.length w := by
  have h := hw.length_inv_mul (inv_mem hx)
  rwa [inv_inv, cs.length_inv] at h

theorem IsLongest.isLeftDescent {J : Set ι} {w : W} (hw : IsLongest cs J w) {i : ι}
    (hi : i ∈ J) : cs.IsLeftDescent w i :=
  hw.length_mul_lt (cs.simple_mem_parabolic hi) (cs.isReflection_simple i)

theorem IsLongest.isRightDescent {J : Set ι} {w : W} (hw : IsLongest cs J w) {i : ι}
    (hi : i ∈ J) : cs.IsRightDescent w i := by
  have h := hw.inv.isLeftDescent hi
  rwa [cs.isLeftDescent_inv_iff] at h

theorem exists_isLongest (J : Set ι) [Finite (cs.parabolic J)] : ∃ w, IsLongest cs J w := by
  obtain ⟨⟨w, hw⟩, hmax⟩ := Finite.exists_max fun v : cs.parabolic J => cs.length v.1
  exact ⟨w, hw, fun v hv => hmax ⟨v, hv⟩⟩

theorem isLongest_of_forall_isLeftDescent {J : Set ι} [Finite (cs.parabolic J)] {x : W}
    (hx : x ∈ cs.parabolic J) (hd : ∀ i ∈ J, cs.IsLeftDescent x i) : IsLongest cs J x := by
  obtain ⟨m, hm⟩ := exists_isLongest (cs := cs) J
  suffices h : m * x⁻¹ = 1 by
    rw [mul_inv_eq_one] at h
    exact h ▸ hm
  by_contra hne
  have hz : m * x⁻¹ ∈ cs.parabolic J := mul_mem hm.1 (inv_mem hx)
  obtain ⟨i, hi, hdesc⟩ := cs.exists_rightDescent_mem_of_mem_parabolic_of_ne_one hz hne
  have h1 := hm.length_mul (inv_mem hx)
  rw [cs.length_inv] at h1
  have h2 := cs.isRightDescent_iff.mp hdesc
  have h3 := cs.isLeftDescent_iff.mp (hd i hi)
  have h4 := cs.length_mul_le (m * x⁻¹ * cs.simple i) (cs.simple i * x)
  have h5 : m * x⁻¹ * cs.simple i * (cs.simple i * x) = m := by
    rw [mul_assoc (m * x⁻¹), cs.simple_mul_simple_cancel_left, inv_mul_cancel_right]
  rw [h5] at h4
  omega

theorem length_longest_mul_of_forall_isLeftDescent {J : Set ι} [Finite (cs.parabolic J)]
    {m : W} (hm : IsLongest cs J m) {w : W} (hd : ∀ i ∈ J, cs.IsLeftDescent w i) :
    cs.length (m * w) + cs.length m = cs.length w := by
  obtain ⟨⟨x, u⟩, ⟨hx, hu, rfl⟩, -⟩ := cs.existsUnique_mem_parabolic_mul J w
  dsimp only at hx hu hd ⊢
  have hadd : ∀ y ∈ cs.parabolic J, cs.length (y * u) = cs.length y + cs.length u :=
    fun y hy => cs.length_mul_of_forall_not_isLeftDescent hy hu
  have hdx : ∀ i ∈ J, cs.IsLeftDescent x i := by
    intro i hi
    have h := hd i hi
    rw [IsLeftDescent, ← mul_assoc, hadd _ (mul_mem (cs.simple_mem_parabolic hi) hx),
      hadd x hx] at h
    rw [IsLeftDescent]
    omega
  have hxm : x = m := (isLongest_of_forall_isLeftDescent hx hdx).unique hm
  subst hxm
  rw [← mul_assoc, hm.mul_self, one_mul, hadd x hx]
  omega

variable (cs) in
open _root_.Classical in
@[expose] noncomputable def longest (J : Set ι) : W :=
  if h : ∃ w, IsLongest cs J w then h.choose else 1

theorem isLongest_longest (J : Set ι) [Finite (cs.parabolic J)] :
    IsLongest cs J (longest cs J) := by
  have h := exists_isLongest (cs := cs) J
  rw [longest, dite_eq_left h]
  exact h.choose_spec

theorem IsLongest.eq_longest {J : Set ι} [Finite (cs.parabolic J)] {w : W}
    (hw : IsLongest cs J w) : w = longest cs J :=
  hw.unique (isLongest_longest J)

variable (cs) in
theorem simple_mem_parabolic_iff {J : Set ι} {i : ι} :
    cs.simple i ∈ cs.parabolic J ↔ i ∈ J := by
  refine ⟨fun h => ?_, cs.simple_mem_parabolic⟩
  obtain ⟨ω, hred, hJ, hω⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic h
  have hlen : ω.length = 1 := by rw [← hred.eq, hω, cs.length_simple]
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
  rw [cs.wordProd_singleton] at hω
  rw [← cs.simple_injective hω]
  exact hJ j (by simp)

variable (cs) in
theorem mem_of_isReduced_of_mem_parabolic {J : Set ι} {ω : List ι} (hω : cs.IsReduced ω)
    (h : cs.wordProd ω ∈ cs.parabolic J) {i : ι} (hi : i ∈ ω) : i ∈ J :=
  (simple_mem_parabolic_iff cs).mp (cs.simple_mem_parabolic_of_isReduced ω hω h i hi)

variable (cs) in
theorem parabolic_inter (J K : Set ι) :
    cs.parabolic J ⊓ cs.parabolic K = cs.parabolic (J ∩ K) := by
  refine le_antisymm (fun w hw => ?_) (le_inf (cs.parabolic_mono Set.inter_subset_left)
    (cs.parabolic_mono Set.inter_subset_right))
  obtain ⟨ω, hred, hJ, rfl⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hw.1
  exact cs.wordProd_mem_parabolic fun i hi =>
    ⟨hJ i hi, mem_of_isReduced_of_mem_parabolic cs hred hw.2 hi⟩

variable (cs) in
theorem mem_parabolic_iff_of_isReduced {J : Set ι} {ω : List ι} (hω : cs.IsReduced ω) :
    cs.wordProd ω ∈ cs.parabolic J ↔ ∀ i ∈ ω, i ∈ J :=
  ⟨fun h _ hi => mem_of_isReduced_of_mem_parabolic cs hω h hi, cs.wordProd_mem_parabolic⟩

variable (cs) in
theorem length_le_of_mem_parabolic_pair {i j : ι} (hM : M i j ≠ 0) {w : W}
    (hw : w ∈ cs.parabolic {i, j}) : cs.length w ≤ M i j := by
  rcases cs.wordProd_alternatingWord_eq_of_mem_parabolic_pair hw with h | h
  · by_contra hlt
    have hred : cs.IsReduced (alternatingWord i j (cs.length w)) := by
      rw [CoxeterSystem.IsReduced, h, length_alternatingWord]
    exact cs.not_isReduced_alternatingWord i j hM (by omega) hred
  · by_contra hlt
    have hred : cs.IsReduced (alternatingWord j i (cs.length w)) := by
      rw [CoxeterSystem.IsReduced, h, length_alternatingWord]
    rw [M.symmetric] at hM
    exact cs.not_isReduced_alternatingWord j i hM (by rw [M.symmetric]; omega) hred

theorem finite_parabolic_pair {i j : ι} (hM : M i j ≠ 0) : Finite (cs.parabolic {i, j}) := by
  classical
  let f : Bool × Fin (M i j + 1) → W := fun p =>
    if p.1 then cs.wordProd (alternatingWord i j p.2) else cs.wordProd (alternatingWord j i p.2)
  have hsurj : ∀ w ∈ cs.parabolic {i, j}, ∃ p, f p = w := by
    intro w hw
    have hle := length_le_of_mem_parabolic_pair cs hM hw
    rcases cs.wordProd_alternatingWord_eq_of_mem_parabolic_pair hw with h | h
    · exact ⟨(true, ⟨cs.length w, by omega⟩), by simpa [f] using h⟩
    · exact ⟨(false, ⟨cs.length w, by omega⟩), by simpa [f] using h⟩
  have : Set.Finite (cs.parabolic {i, j} : Set W) :=
    (Set.finite_range f).subset fun w hw => hsurj w hw
  exact this.to_subtype

theorem isLongest_braidWord {i j : ι} (hij : i ≠ j) (hM : M i j ≠ 0) :
    IsLongest cs {i, j} (cs.wordProd (braidWord M i j)) ∧
      cs.IsReduced (braidWord M i j) ∧ cs.length (cs.wordProd (braidWord M i j)) = M i j := by
  have := finite_parabolic_pair (cs := cs) hM
  obtain ⟨m, hm⟩ := exists_isLongest (cs := cs) ({i, j} : Set ι)
  have hdi := hm.isLeftDescent (show i ∈ ({i, j} : Set ι) by simp)
  have hdj := hm.isLeftDescent (show j ∈ ({i, j} : Set ι) by simp)
  have hlen := cs.length_eq_orderOf_of_isLeftDescent_pair hij hm.1 hdi hdj
  rw [cs.orderOf_simple_mul_simple] at hlen
  have h := (cs.wordProd_alternatingWord_eq_of_isLeftDescent_pair hij hm.1 hdi hdj).1
  rw [hlen] at h
  have hb : cs.wordProd (braidWord M i j) = m := h
  refine ⟨hb ▸ hm, ?_, by rw [hb, hlen]⟩
  rw [CoxeterSystem.IsReduced, hb, hlen, braidWord, length_alternatingWord]

end CFSG.Monster.B.Geometry
