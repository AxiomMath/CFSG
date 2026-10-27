module

public import CFSG.Sporadic.Co1Patterson.GraphFixDimInputs
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.Sporadic.Co1Patterson

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1Patterson.Native Matrix

@[expose] def xorSpan : List ℕ → Finset ℕ
  | [] => {0}
  | v :: t => xorSpan t ∪ (xorSpan t).image (· ^^^ v)

theorem xorSpan_lt {k : ℕ} : ∀ L : List ℕ, (∀ v ∈ L, v < 2 ^ k) → ∀ x ∈ xorSpan L, x < 2 ^ k
  | [], _, x, hx => by
    simp only [xorSpan, Finset.mem_singleton] at hx
    subst hx
    exact Nat.two_pow_pos k
  | v :: t, h, x, hx => by
    simp only [xorSpan, Finset.mem_union, Finset.mem_image] at hx
    have ht := xorSpan_lt t (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ht x hx
    · exact Nat.xor_lt_two_pow (ht y hy) (h v List.mem_cons_self)

theorem xorSpan_subset (A : Set ℕ) (h0 : (0 : ℕ) ∈ A)
    (hA : ∀ x y, x ∈ A → y ∈ A → x ^^^ y ∈ A) :
    ∀ L : List ℕ, (∀ v ∈ L, v ∈ A) → ∀ x ∈ xorSpan L, x ∈ A
  | [], _, x, hx => by
    simp only [xorSpan, Finset.mem_singleton] at hx
    exact hx ▸ h0
  | v :: t, h, x, hx => by
    simp only [xorSpan, Finset.mem_union, Finset.mem_image] at hx
    have ht := xorSpan_subset A h0 hA t (fun w hw => h w (List.mem_cons_of_mem _ hw))
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ht x hx
    · exact hA _ _ (ht y hy) (h v List.mem_cons_self)

theorem echelonOK_log2_lt : ∀ {v : ℕ} {t : List ℕ}, echelonOK (v :: t) = true →
    ∀ w ∈ t, w.log2 < v.log2
  | _, [], _, _, hw => absurd hw List.not_mem_nil
  | v, w :: t, h, u, hu => by
    simp only [echelonOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨-, -⟩, hwv⟩, ht⟩ := h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hwv
    · exact (echelonOK_log2_lt ht u hu).trans hwv

theorem echelonOK_tail : ∀ {v : ℕ} {t : List ℕ}, echelonOK (v :: t) = true → echelonOK t = true
  | _, [], _ => rfl
  | v, w :: t, h => by
    simp only [echelonOK, Bool.and_eq_true] at h
    exact h.2

theorem echelonOK_mem : ∀ {L : List ℕ}, echelonOK L = true → ∀ v ∈ L, 0 < v ∧ v < 2 ^ 24
  | [], _, _, hv => absurd hv List.not_mem_nil
  | [w], h, v, hv => by
    simp only [echelonOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.mem_singleton] at hv
    exact hv ▸ h
  | w :: u :: t, h, v, hv => by
    have h' := h
    simp only [echelonOK, Bool.and_eq_true, decide_eq_true_eq] at h'
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ⟨h'.1.1.1, h'.1.1.2⟩
    · exact echelonOK_mem h'.2 v hv

theorem card_xorSpan : ∀ L : List ℕ, echelonOK L = true → (xorSpan L).card = 2 ^ L.length
  | [], _ => rfl
  | v :: t, h => by
    have ht := card_xorSpan t (echelonOK_tail h)
    have hv := echelonOK_mem h v List.mem_cons_self
    set k := v.log2
    have hvne : v ≠ 0 := by omega
    have hlt : ∀ x ∈ xorSpan t, x < 2 ^ k := by
      refine xorSpan_lt t fun w hw => ?_
      have hw0 := (echelonOK_mem h w (List.mem_cons_of_mem _ hw)).1
      exact (Nat.log2_lt (by omega)).1 (echelonOK_log2_lt h w hw)
    have hbit : ∀ x ∈ xorSpan t, (x ^^^ v).testBit k = true := by
      intro x hx
      rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (hlt x hx), Nat.testBit_log2 hvne]
      rfl
    have hdisj : Disjoint (xorSpan t) ((xorSpan t).image (· ^^^ v)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx'
      have h1 := hbit y hy
      rw [Nat.testBit_lt_two_pow (hlt _ hx)] at h1
      exact Bool.false_ne_true h1
    have hinj : Set.InjOn (· ^^^ v) (xorSpan t : Set ℕ) := fun x _ y _ hxy => by
      simpa using congrArg (· ^^^ v) hxy
    simp only [xorSpan, List.length_cons]
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj, ht, pow_succ]
    ring

theorem rowsMatrix_add (X Y : Rows) :
    rowsMatrix 24 (add X Y) = rowsMatrix 24 X + rowsMatrix 24 Y := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold CFSG.Sporadic.Co1Schreier.Native.add
  rw [Array.getElem?_ofFn]
  simp only [i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor, Pi.add_apply]

theorem rowsMatrix_mulVec_toVecD (N : Rows) (v : ℕ) :
    rowsMatrix 24 N *ᵥ toVecD 24 v = toVecD 24 (act N v) :=
  rowsMatrix_mulVec 24 N v

theorem card_le_ncard_of_xorSpan (S : AddSubgroup (Fin 24 → ZMod 2)) (L : List ℕ)
    (hL : echelonOK L = true) (hS : ∀ v ∈ L, toVecD 24 v ∈ S) :
    2 ^ L.length ≤ Nat.card S := by
  have hmem : ∀ x ∈ xorSpan L, x < 2 ^ 24 ∧ toVecD 24 x ∈ S := by
    refine xorSpan_subset {x | x < 2 ^ 24 ∧ toVecD 24 x ∈ S} ⟨Nat.two_pow_pos 24, ?_⟩ ?_ L ?_
    · rw [toVecD_zero]; exact S.zero_mem
    · rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
      exact ⟨Nat.xor_lt_two_pow hx hy, by rw [toVecD_xor]; exact S.add_mem hx' hy'⟩
    · intro v hv
      exact ⟨(echelonOK_mem hL v hv).2, hS v hv⟩
  classical
  have hsub : (((xorSpan L).image (toVecD 24) : Finset (Fin 24 → ZMod 2)) :
      Set (Fin 24 → ZMod 2)) ⊆ (S : Set (Fin 24 → ZMod 2)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact (hmem x hx).2
  have hcard : ((xorSpan L).image (toVecD 24)).card = (xorSpan L).card :=
    Finset.card_image_of_injOn fun x hx y hy hxy =>
      toVecD_injective (hmem x hx).1 (hmem y hy).1 hxy
  have hS' : Nat.card S = (S : Set (Fin 24 → ZMod 2)).ncard := Nat.card_coe_set_eq _
  rw [← card_xorSpan L hL, ← hcard, ← Set.ncard_coe_finset, hS']
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem neg_vec_eq (w : Fin 24 → ZMod 2) : -w = w := by
  funext i
  have : ∀ x : ZMod 2, -x = x := by decide
  exact this (w i)

theorem fixDimIs_parts {M : Rows} {d : ℕ} (h : fixDimIs M d = true) :
    (echelonize (kerIm (add M one)).2).length = d ∧ (kerIm (add M one)).1.length + d = 24 ∧
    (∀ v ∈ echelonize (kerIm (add M one)).2, act (add M one) v = 0) ∧
    echelonOK (echelonize (kerIm (add M one)).2) = true ∧
    (∀ p ∈ (kerIm (add M one)).1, act (add M one) p.2 = p.1) ∧
    echelonOK ((kerIm (add M one)).1.map Prod.fst) = true := by
  unfold fixDimIs at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hKl, hIl⟩, hK⟩, hKe⟩, hI⟩, hIe⟩ := h
  exact ⟨hKl, hIl, hK, hKe, fun p hp => (hI p hp).2, hIe⟩

@[expose] noncomputable def mulVecHom (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    (Fin 24 → ZMod 2) →+ (Fin 24 → ZMod 2) :=
  (Matrix.mulVecLin A).toAddMonoidHom

theorem mulVecHom_apply (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) (v : Fin 24 → ZMod 2) :
    mulVecHom A v = A *ᵥ v := rfl

theorem card_ker_mul_card_range (A : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    Nat.card (mulVecHom A).ker * Nat.card (mulVecHom A).range = 2 ^ 24 := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem eq_two_pow_of_mul {k r d : ℕ} (hd : d ≤ 24) (hk : 2 ^ d ≤ k) (hr : 2 ^ (24 - d) ≤ r)
    (h : k * r = 2 ^ 24) : k = 2 ^ d := by
  refine le_antisymm ?_ hk
  by_contra hlt
  have hlt' : 2 ^ d + 1 ≤ k := by omega
  have h1 : (2 ^ d + 1) * 2 ^ (24 - d) ≤ k * r := Nat.mul_le_mul hlt' hr
  have h2 : 2 ^ d * 2 ^ (24 - d) = 2 ^ 24 := by rw [← pow_add]; congr 1; omega
  have h3 : 0 < 2 ^ (24 - d) := Nat.two_pow_pos _
  rw [h, add_mul, one_mul, h2] at h1
  omega

theorem ncard_fix_of_fixDimIs {M : Rows} {d : ℕ} (h : fixDimIs M d = true) :
    {v : Fin 24 → ZMod 2 | rowsMatrix 24 M *ᵥ v = v}.ncard = 2 ^ d := by
  have hNmat : rowsMatrix 24 (add M one) = rowsMatrix 24 M + 1 := by
    rw [rowsMatrix_add, show rowsMatrix 24 one = 1 from rowsMatrix_idRows 24]
  obtain ⟨hKl, hIl, hK, hKe, hI, hIe⟩ := fixDimIs_parts h
  have hfix : {v : Fin 24 → ZMod 2 | rowsMatrix 24 M *ᵥ v = v} =
      ((mulVecHom (rowsMatrix 24 (add M one))).ker : Set _) := by
    ext v
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, AddMonoidHom.mem_ker, mulVecHom_apply]
    rw [hNmat, Matrix.add_mulVec, Matrix.one_mulVec, add_eq_zero_iff_eq_neg]
    have hv : -v = v := neg_vec_eq v
    exact ⟨fun h => h.trans hv.symm, fun h => h.trans hv⟩
  have hker : 2 ^ d ≤ Nat.card (mulVecHom (rowsMatrix 24 (add M one))).ker := by
    rw [← hKl]
    refine card_le_ncard_of_xorSpan _ _ hKe fun v hv => ?_
    rw [AddMonoidHom.mem_ker, mulVecHom_apply, rowsMatrix_mulVec_toVecD, hK v hv, toVecD_zero]
  have hd : d ≤ 24 := by omega
  have hrange : 2 ^ (24 - d) ≤ Nat.card (mulVecHom (rowsMatrix 24 (add M one))).range := by
    have hlen : ((kerIm (add M one)).1.map Prod.fst).length = 24 - d := by
      rw [List.length_map]; omega
    rw [← hlen]
    refine card_le_ncard_of_xorSpan _ _ hIe fun w hw => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    exact ⟨toVecD 24 p.2, by rw [mulVecHom_apply, rowsMatrix_mulVec_toVecD, hI p hp]⟩
  rw [hfix, ← Nat.card_coe_set_eq]
  exact eq_two_pow_of_mul hd hker hrange (card_ker_mul_card_range _)

end CFSG.Sporadic.Co1Patterson
