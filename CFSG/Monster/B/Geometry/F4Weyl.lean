module

public import CFSG.Monster.B.Geometry.F4WeylData
public import CFSG.LieType.Chevalley.BraidWalk
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.GroupActions.ExchangeMatsumoto

public section

namespace CFSG.Monster.B.Geometry

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk
open CFSG.GroupActions.Exchange

@[expose] def f4Get (l : List (List ℕ)) (k : ℕ) : ℕ := (l.getD (k / 34) []).getD (k % 34) 0

@[expose] def f4Digit (c j : ℕ) : ℕ := c / 64 ^ j % 64

@[expose] def f4Act (i : Fin Tag.F4.rank) (c : ℕ) : ℕ :=
  Tag.F4.rootCertificate.image (f4Digit c 0) i +
    64 * Tag.F4.rootCertificate.image (f4Digit c 1) i +
    4096 * Tag.F4.rootCertificate.image (f4Digit c 2) i +
    262144 * Tag.F4.rootCertificate.image (f4Digit c 3) i

@[expose] def f4Gen (n : ℕ) : Fin Tag.F4.rank := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

@[expose] def f4Code (k : ℕ) : ℕ := f4Get f4Codes k

@[expose] def f4DistOf (k : ℕ) : ℕ := f4Get f4Dist k

@[expose] def f4Parent (k : ℕ) : ℕ := f4Get f4Par k / 4

@[expose] def f4Next (k : ℕ) (i : Fin Tag.F4.rank) : ℕ := f4Get f4Clos k / 2048 ^ (i : ℕ) % 2048

@[expose] def f4CheckBase : Bool := f4Code 0 == 794688 && f4DistOf 0 == 0

theorem f4CheckBase_eq : f4CheckBase = true := by decide +kernel

@[expose] def f4CheckParents : Bool :=
  (List.range 1152).all fun k =>
    k == 0 || (decide (f4Parent k < k) &&
      f4Code k == f4Act (f4Gen (f4Get f4Par k)) (f4Code (f4Parent k)) &&
      f4DistOf k == f4DistOf (f4Parent k) + 1)

theorem f4CheckParents_eq : f4CheckParents = true := by decide +kernel

@[expose] def f4CheckClosure : Bool :=
  (List.range 1152).all fun k => (List.finRange Tag.F4.rank).all fun i =>
    decide (f4Next k i < 1152) && f4Code (f4Next k i) == f4Act i (f4Code k) &&
      decide (f4DistOf (f4Next k i) ≤ f4DistOf k + 1)

theorem f4CheckClosure_eq : f4CheckClosure = true := by decide +kernel

@[expose] def f4CheckCodes : Bool :=
  (List.range 1152).all fun k => decide (f4Code k < 64 ^ 4) &&
    ((List.range 4).all fun j => decide (f4Digit (f4Code k) j < 48)) &&
    (f4Code k == f4Codes.flatten.getD k 0)

theorem f4CheckCodes_eq : f4CheckCodes = true := by decide +kernel

theorem f4Codes_nodup : f4Codes.flatten.Nodup := by decide +kernel

theorem f4Codes_length : f4Codes.flatten.length = 1152 := by decide +kernel

theorem f4_roots_length : Tag.F4.rootCertificate.roots.length = 48 := by decide +kernel

theorem f4Code_zero : f4Code 0 = 794688 := by
  have h := f4CheckBase_eq
  simp only [f4CheckBase, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem f4DistOf_zero : f4DistOf 0 = 0 := by
  have h := f4CheckBase_eq
  simp only [f4CheckBase, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem f4_parent {k : ℕ} (hk : k < 1152) (hk0 : k ≠ 0) :
    f4Parent k < k ∧ f4Code k = f4Act (f4Gen (f4Get f4Par k)) (f4Code (f4Parent k)) ∧
      f4DistOf k = f4DistOf (f4Parent k) + 1 := by
  have h := f4CheckParents_eq
  simp only [f4CheckParents, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h k hk with h | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h hk0
  · exact ⟨h1, h2, h3⟩

theorem f4_next {k : ℕ} (hk : k < 1152) (i : Fin Tag.F4.rank) :
    f4Next k i < 1152 ∧ f4Code (f4Next k i) = f4Act i (f4Code k) ∧
      f4DistOf (f4Next k i) ≤ f4DistOf k + 1 := by
  have h := f4CheckClosure_eq
  simp only [f4CheckClosure, List.all_eq_true, List.mem_range, List.mem_finRange,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, true_implies] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk i
  exact ⟨h1, h2, h3⟩

theorem f4_code {k : ℕ} (hk : k < 1152) :
    f4Code k < 64 ^ 4 ∧ (∀ j < 4, f4Digit (f4Code k) j < 48) ∧
      f4Code k = f4Codes.flatten.getD k 0 := by
  have h := f4CheckCodes_eq
  simp only [f4CheckCodes, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h k hk
  exact ⟨h1, h2, h3⟩

theorem f4Digit_pack {a b c d : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64) :
    f4Digit (a + 64 * b + 4096 * c + 262144 * d) 0 = a ∧
      f4Digit (a + 64 * b + 4096 * c + 262144 * d) 1 = b ∧
      f4Digit (a + 64 * b + 4096 * c + 262144 * d) 2 = c ∧
      f4Digit (a + 64 * b + 4096 * c + 262144 * d) 3 = d := by
  simp only [f4Digit]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> omega

theorem eq_of_f4Digit_eq {c c' : ℕ} (hc : c < 64 ^ 4) (hc' : c' < 64 ^ 4)
    (h : ∀ j < 4, f4Digit c j = f4Digit c' j) : c = c' := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  simp only [f4Digit] at h0 h1 h2 h3
  norm_num at hc hc' h0 h1 h2 h3
  omega

theorem f4Digit_act
    (i : Fin Tag.F4.rank) {c : ℕ} (hc : ∀ j < 4, f4Digit c j < 48) {j : ℕ}
    (hj : j < 4) :
    f4Digit (f4Act i c) j = Tag.F4.rootCertificate.image (f4Digit c j) i := by
  have himg : ∀ j < 4, Tag.F4.rootCertificate.image (f4Digit c j) i < 64 := fun j hj => by
    have := rootCertificate_image_lt (τ := .F4) (by rw [f4_roots_length]; exact hc j hj) i
    rw [f4_roots_length] at this
    omega
  obtain ⟨e0, e1, e2, e3⟩ := f4Digit_pack (himg 0 (by norm_num)) (himg 1 (by norm_num))
    (himg 2 (by norm_num)) (himg 3 (by norm_num))
  unfold f4Act
  interval_cases j
  · exact e0
  · exact e1
  · exact e2
  · exact e3

@[expose] def F4Realizes
    (w : WeylGroup .F4) (c : ℕ) : Prop :=
  ∀ j : Fin Tag.F4.rank, f4Digit c j < 48 ∧
    w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = Tag.F4.rootCertificate.root (f4Digit c j)

theorem f4Realizes_one :
    F4Realizes 1 794688 := by
  intro j
  have hd : f4Digit 794688 j = j := by
    fin_cases j <;> decide
  rw [hd, one_smul, (rootCertificate_basis_table (τ := .F4)).2.1 j]
  exact ⟨by fin_cases j <;> decide, rfl⟩

theorem F4Realizes.digit_lt
    {w : WeylGroup .F4} {c : ℕ} (h : F4Realizes w c) :
    ∀ j < 4, f4Digit c j < 48 := fun j hj => (h ⟨j, hj⟩).1

theorem F4Realizes.simple_mul
    {w : WeylGroup .F4} {c : ℕ} (h : F4Realizes w c)
    (i : Fin Tag.F4.rank) : F4Realizes (simple .F4 i * w) (f4Act i c) := by
  intro j
  have hj : (j : ℕ) < 4 := j.2
  rw [f4Digit_act i h.digit_lt hj]
  have hlt : f4Digit c j < Tag.F4.rootCertificate.roots.length := by
    rw [f4_roots_length]; exact (h j).1
  refine ⟨?_, ?_⟩
  · have := rootCertificate_image_lt hlt i
    rwa [f4_roots_length] at this
  · rw [mul_smul, (h j).2, simple_smul, rootCertificate_root_image hlt]

theorem F4Realizes.eq
    {w w' : WeylGroup .F4} {c : ℕ} (h : F4Realizes w c)
    (h' : F4Realizes w' c) : w = w' :=
  ext_single fun j => (h j).2.trans (h' j).2.symm

theorem F4Realizes.code_eq
    {w : WeylGroup .F4} {c c' : ℕ} (h : F4Realizes w c)
    (h' : F4Realizes w c') (hc : c < 64 ^ 4) (hc' : c' < 64 ^ 4) : c = c' := by
  refine eq_of_f4Digit_eq hc hc' fun j hj => ?_
  have e := (h ⟨j, hj⟩).2.symm.trans (h' ⟨j, hj⟩).2
  exact rootCertificate_root_injOn (by rw [f4_roots_length]; exact (h ⟨j, hj⟩).1)
    (by rw [f4_roots_length]; exact (h' ⟨j, hj⟩).1) e

@[expose] def f4WordAux : ℕ → ℕ → List (Fin Tag.F4.rank)
  | 0, _ => []
  | n + 1, k => if k = 0 then [] else f4Gen (f4Get f4Par k) :: f4WordAux n (f4Parent k)

@[expose] def f4Word (k : ℕ) : List (Fin Tag.F4.rank) := f4WordAux (f4DistOf k) k

@[expose] noncomputable def f4Elem
    (k : ℕ) : WeylGroup .F4 :=
  (coxeterSystem .F4).wordProd (f4Word k)

theorem f4DistOf_pos {k : ℕ} (hk : k < 1152) (hk0 : k ≠ 0) : 0 < f4DistOf k := by
  have := (f4_parent hk hk0).2.2
  omega

theorem f4Realizes_wordAux :
    ∀ n k, k < 1152 → f4DistOf k = n →
    F4Realizes ((coxeterSystem .F4).wordProd (f4WordAux n k)) (f4Code k) ∧
      (f4WordAux n k).length = n := by
  intro n
  induction n with
  | zero =>
    intro k hk hd
    have hk0 : k = 0 := by
      by_contra hne
      have := f4DistOf_pos hk hne
      omega
    subst hk0
    rw [f4Code_zero]
    exact ⟨by simpa [f4WordAux] using f4Realizes_one, rfl⟩
  | succ n ih =>
    intro k hk hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [f4DistOf_zero] at hd
      omega
    obtain ⟨hp, hc, hdp⟩ := f4_parent hk hk0
    have IH := ih (f4Parent k) (by omega) (by omega)
    simp only [f4WordAux, hk0, ite_false, List.length_cons]
    refine ⟨?_, by rw [IH.2]⟩
    rw [CoxeterSystem.wordProd_cons]
    rw [hc]
    exact IH.1.simple_mul _

theorem f4Realizes_elem
    {k : ℕ} (hk : k < 1152) : F4Realizes (f4Elem k) (f4Code k) :=
  (f4Realizes_wordAux _ k hk rfl).1

theorem length_f4Word
    (k : ℕ) (hk : k < 1152) : (f4Word k).length = f4DistOf k :=
  (f4Realizes_wordAux _ k hk rfl).2

theorem exists_entry
    (w : WeylGroup .F4) :
    ∃ k < 1152, F4Realizes w (f4Code k) ∧ f4DistOf k ≤ (coxeterSystem .F4).length w := by
  induction h : (coxeterSystem .F4).length w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases hw : w = 1
    · subst hw
      exact ⟨0, by norm_num, by rw [f4Code_zero]; exact f4Realizes_one,
        by rw [f4DistOf_zero]; omega⟩
    obtain ⟨i, hi⟩ := (coxeterSystem .F4).exists_leftDescent_of_ne_one hw
    have hl := (coxeterSystem .F4).isLeftDescent_iff.mp hi
    obtain ⟨k', hk', hr, hd⟩ := ih _ (by omega) ((coxeterSystem .F4).simple i * w) rfl
    obtain ⟨hn, hc, hdn⟩ := f4_next hk' i
    refine ⟨f4Next k' i, hn, ?_, by omega⟩
    rw [hc]
    have := hr.simple_mul i
    rwa [← mul_assoc, (coxeterSystem .F4).simple_mul_simple_self, one_mul] at this

theorem f4Code_injOn {k k' : ℕ} (hk : k < 1152) (hk' : k' < 1152) (h : f4Code k = f4Code k') :
    k = k' := by
  rw [(f4_code hk).2.2, (f4_code hk').2.2] at h
  rw [List.getD_eq_getElem _ _ (by rw [f4Codes_length]; exact hk),
    List.getD_eq_getElem _ _ (by rw [f4Codes_length]; exact hk')] at h
  exact (f4Codes_nodup.getElem_inj_iff).mp h

theorem f4Elem_bijective :
    Function.Bijective fun k : Fin 1152 => f4Elem k := by
  refine ⟨fun k k' h => Fin.ext ?_, fun w => ?_⟩
  · have h1 := f4Realizes_elem k.2
    have h2 := f4Realizes_elem k'.2
    have h' : f4Elem k = f4Elem k' := h
    have h1' : F4Realizes (f4Elem k') (f4Code k) := h' ▸ h1
    exact f4Code_injOn k.2 k'.2 (h1'.code_eq h2 (f4_code k.2).1 (f4_code k'.2).1)
  · obtain ⟨k, hk, hr, -⟩ := exists_entry w
    exact ⟨⟨k, hk⟩, (f4Realizes_elem hk).eq hr⟩

theorem card_f4WeylGroup :
    Nat.card (WeylGroup .F4) = 1152 := by
  rw [← Nat.card_eq_of_bijective _ f4Elem_bijective, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isReduced_f4Word
    {k : ℕ} (hk : k < 1152) : (coxeterSystem .F4).IsReduced (f4Word k) := by
  obtain ⟨k', hk', hr, hd⟩ := exists_entry (f4Elem k)
  have hkk : k' = k := f4Code_injOn hk' hk
    (hr.code_eq (f4Realizes_elem hk) (f4_code hk').1 (f4_code hk).1)
  subst hkk
  have hle := (coxeterSystem .F4).length_wordProd_le (f4Word k')
  rw [CoxeterSystem.IsReduced]
  change (coxeterSystem .F4).length (f4Elem k') = _
  rw [length_f4Word k' hk] at hle ⊢
  exact le_antisymm hle hd

theorem sum_f4
    {β : Type*} [AddCommMonoid β] (f : WeylGroup .F4 → β) :
    ∑ᶠ w, f w = ∑ k : Fin 1152, f (f4Elem k) := by
  rw [← finsum_eq_sum_of_fintype]
  exact (finsum_comp_equiv (Equiv.ofBijective _ f4Elem_bijective)).symm

end CFSG.Monster.B.Geometry
