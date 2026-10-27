module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Str

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.Quasithin CFSG.Open
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def fixSet (A : Subgroup (Equiv.Perm (Fin 42))) (lo hi : ℕ) : Set (Fin 42) :=
  {p | lo ≤ p.val ∧ p.val < hi ∧ ∀ a ∈ A, a p = p}

private def w183finL34Good (r : Equiv.Perm (Fin 42)) : Prop :=
  ((∀ p : Fin 42, p.val < 21 → (r p).val < 21) ∧
      (∀ p : Fin 42, 21 ≤ p.val → 21 ≤ (r p).val)) ∨
    ((∀ p : Fin 42, p.val < 21 → 21 ≤ (r p).val) ∧
      (∀ p : Fin 42, 21 ≤ p.val → (r p).val < 21))

private theorem w183finL34Good_rho (A : GL (Fin 3) F4) : w183finL34Good (rho A) := by
  left
  constructor
  · intro p hp
    have h := vIdx_lt (Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) F4) (vecOf p))
    rw [rho_apply]
    unfold rhoFun
    rw [if_pos hp]
    exact h
  · intro p hp
    have h := vIdx_lt (Matrix.mulVec
      (Matrix.transpose ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) (vecOf p))
    rw [rho_apply]
    unfold rhoFun
    rw [if_neg (by omega)]
    change 21 ≤ 21 + vIdx (Matrix.mulVec
      (Matrix.transpose ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) (vecOf p))
    omega

private theorem w183finL34Good_g5 : w183finL34Good g₅ := by
  left
  constructor
  · intro p hp
    have h : p.val / 21 = 0 := by omega
    have h2 := vIdx_lt (fun k => vecOf p k ^ 2)
    change (g5Fun p).val < 21
    simp only [g5Fun, Fin.val_mk, h, mul_zero, zero_add]
    exact h2
  · intro p hp
    have h : p.val / 21 = 1 := by omega
    have h2 := vIdx_lt (fun k => vecOf p k ^ 2)
    change 21 ≤ (g5Fun p).val
    simp only [g5Fun, Fin.val_mk, h, mul_one]
    omega

private theorem w183finL34Good_g6 : w183finL34Good g₆ := by
  right
  constructor
  · intro p hp
    change 21 ≤ (g6Fun p).val
    simp only [g6Fun, dif_pos hp, Fin.val_mk]
    omega
  · intro p hp
    change (g6Fun p).val < 21
    have hnot : ¬ p.val < 21 := by omega
    simp only [g6Fun, dif_neg hnot, Fin.val_mk]
    omega

private def w183finL34BlockSubgroup : Subgroup (Equiv.Perm (Fin 42)) where
  carrier := {r | w183finL34Good r}
  one_mem' := by
    left
    exact ⟨fun p hp => hp, fun p hp => hp⟩
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨ha0, ha1⟩ | ⟨ha0, ha1⟩ <;> rcases hb with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · left
      exact ⟨fun p hp => by rw [Equiv.Perm.mul_apply]; exact ha0 _ (hb0 p hp),
        fun p hp => by rw [Equiv.Perm.mul_apply]; exact ha1 _ (hb1 p hp)⟩
    · right
      exact ⟨fun p hp => by rw [Equiv.Perm.mul_apply]; exact ha1 _ (hb0 p hp),
        fun p hp => by rw [Equiv.Perm.mul_apply]; exact ha0 _ (hb1 p hp)⟩
    · right
      exact ⟨fun p hp => by rw [Equiv.Perm.mul_apply]; exact ha0 _ (hb0 p hp),
        fun p hp => by rw [Equiv.Perm.mul_apply]; exact ha1 _ (hb1 p hp)⟩
    · left
      exact ⟨fun p hp => by rw [Equiv.Perm.mul_apply]; exact ha1 _ (hb0 p hp),
        fun p hp => by rw [Equiv.Perm.mul_apply]; exact ha0 _ (hb1 p hp)⟩
  inv_mem' := by
    intro a ha
    rcases ha with ⟨ha0, ha1⟩ | ⟨ha0, ha1⟩
    · left
      constructor
      · intro p hp
        by_contra hcon
        have hge : 21 ≤ (a⁻¹ p).val := by omega
        have h1 := ha1 _ hge
        have h2 : a (a⁻¹ p) = p := by simp
        rw [h2] at h1
        omega
      · intro p hp
        by_contra hcon
        have hlt : (a⁻¹ p).val < 21 := by omega
        have h1 := ha0 _ hlt
        have h2 : a (a⁻¹ p) = p := by simp
        rw [h2] at h1
        omega
    · right
      constructor
      · intro p hp
        by_contra hcon
        have hlt : (a⁻¹ p).val < 21 := by omega
        have h1 := ha0 _ hlt
        have h2 : a (a⁻¹ p) = p := by simp
        rw [h2] at h1
        omega
      · intro p hp
        by_contra hcon
        have hge : 21 ≤ (a⁻¹ p).val := by omega
        have h1 := ha1 _ hge
        have h2 : a (a⁻¹ p) = p := by simp
        rw [h2] at h1
        omega

private theorem w183finL34Good_of_mem_R {r : Equiv.Perm (Fin 42)} (hr : r ∈ R) :
    w183finL34Good r := by
  have hsub : ({g₁, g₂, g₃, g₄, g₅, g₆} : Set (Equiv.Perm (Fin 42))) ⊆
      (w183finL34BlockSubgroup : Set (Equiv.Perm (Fin 42))) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact w183finL34Good_rho aGL
    · exact w183finL34Good_rho bGL
    · exact w183finL34Good_rho cGL
    · exact w183finL34Good_rho dGL
    · exact w183finL34Good_g5
    · exact w183finL34Good_g6
  exact (Subgroup.closure_le w183finL34BlockSubgroup).2 hsub hr

private theorem w183finL34_testBit_foldl_ite (p : ℕ → Bool) (L : List ℕ) (a i : ℕ) :
    (L.foldl (fun acc j => if p j then acc ||| (1 <<< j) else acc) a).testBit i = true ↔
      a.testBit i = true ∨ (i ∈ L ∧ p i = true) := by
  induction L generalizing a with
  | nil => simp
  | cons j L ih =>
    rw [List.foldl_cons, ih]
    split_ifs with hp
    · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h | rfl) | ⟨h1, h2⟩) <;> simp_all
      · rintro (h | ⟨rfl | h1, h2⟩) <;> simp_all
    · simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2⟩) <;> simp_all
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact Or.inl h
        · simp_all
        · exact Or.inr ⟨h1, h2⟩

private theorem w183finL34_testBit_fixMask (x j : ℕ) :
    (fixMask x).testBit j = true ↔ j < 42 ∧ getN x j = j := by
  unfold fixMask
  rw [w183finL34_testBit_foldl_ite]
  simp [Nat.zero_testBit, List.mem_range, beq_iff_eq]

private theorem w183finL34_testBit_foldl_and (L : List ℕ) (a c : ℕ) :
    (L.foldl (fun acc x => acc &&& fixMask x) a).testBit c = true ↔
      a.testBit c = true ∧ ∀ x ∈ L, (fixMask x).testBit c = true := by
  induction L generalizing a with
  | nil => simp
  | cons j L ih =>
    rw [List.foldl_cons, ih, Nat.testBit_and]
    simp only [Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    tauto

private theorem w183finL34_card_filter_range (mask lo : ℕ) (hlo : lo + 21 ≤ 42) :
    ((Finset.univ : Finset (Fin 42)).filter
        (fun p => lo ≤ p.val ∧ p.val < lo + 21 ∧ mask.testBit p.val)).card =
      ((List.range 21).filter (fun i => mask.testBit (lo + i))).length := by
  rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range),
    List.toFinset_filter, List.toFinset_range]
  symm
  refine Finset.card_bij'
    (s := (Finset.range 21).filter (fun i => mask.testBit (lo + i)))
    (t := (Finset.univ : Finset (Fin 42)).filter
      (fun p => lo ≤ p.val ∧ p.val < lo + 21 ∧ mask.testBit p.val))
    (fun i hi => (⟨lo + i, by
      have hi21 : i < 21 := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
      omega⟩ : Fin 42))
    (fun p _ => p.val - lo) ?_ ?_ ?_ ?_
  · intro i hi
    have hi21 : i < 21 := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    have hbit : mask.testBit (lo + i) = true := (Finset.mem_filter.1 hi).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_mk]
    exact ⟨by omega, by omega, hbit⟩
  · intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := (Finset.mem_filter.1 hp).2
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have : lo + (p.val - lo) = p.val := by omega
    rw [this]
    exact hp3
  · intro i hi
    have hi21 : i < 21 := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    simp only [Fin.val_mk]
    omega
  · intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := (Finset.mem_filter.1 hp).2
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

private theorem w183finL34_ncard_fixSet {A : Subgroup (Equiv.Perm (Fin 42))} {mask : ℕ}
    (lo : ℕ) (hlo : lo + 21 ≤ 42)
    (hfix : ∀ p : Fin 42, p ∈ fixSet A lo (lo + 21) ↔
      lo ≤ p.val ∧ p.val < lo + 21 ∧ mask.testBit p.val = true) :
    (fixSet A lo (lo + 21)).ncard = blockCount mask lo := by
  rw [blockCount]
  have hset : fixSet A lo (lo + 21) =
      (((Finset.univ : Finset (Fin 42)).filter
        (fun p => lo ≤ p.val ∧ p.val < lo + 21 ∧ mask.testBit p.val)) : Set (Fin 42)) := by
    ext p
    rw [hfix p]
    simp
  rw [hset, Set.ncard_coe_finset,
    w183finL34_card_filter_range mask lo hlo]

private theorem w183finL34_c1N_getD {k : ℕ} (hk : k < 64) :
    c1N.getD k 0 = wN (c1W.getD k []) := by
  have hkN : k < (c1W.map wN).length := by rw [List.length_map, c1W_length]; exact hk
  rw [c1N, List.getD_eq_getElem (l := c1W.map wN) (d := 0) (n := k) hkN, List.getElem_map,
    List.getD_eq_getElem (l := c1W) (d := ([] : List ℕ)) (n := k)
      (by rw [c1W_length]; exact hk)]

private theorem w183finL34_invI_lt (i : ℕ) : invI.getD i 0 < 64 := by
  by_cases hi : i < invI.length
  · have hmem : invI[i] ∈ invI := List.getElem_mem _
    have hlt : invI[i] < 64 := List.mem_range.1 (List.mem_filter.1 hmem).1
    rwa [List.getD_eq_getElem (l := invI) (d := 0) (n := i) hi]
  · rw [List.getD_eq_default (l := invI) (d := 0) (n := i) (by omega)]
    decide

private theorem w183finL34_getD_map (f : ℕ → ℕ) {l : List ℕ} {n : ℕ} (hn : n < l.length) :
    (l.map f).getD n 0 = f (l.getD n 0) := by
  rw [List.getD_eq_getElem (l := l.map f) (d := 0) (n := n)
      (by rw [List.length_map]; exact hn),
    List.getElem_map, ← List.getD_eq_getElem (l := l) (d := 0) (n := n) hn]

private theorem w183finL34_invN_getD {i : ℕ} (hi : i < invI.length) :
    invN.getD i 0 = wN (c1W.getD (invI.getD i 0) []) := by
  have h1 : invN.getD i 0 = c1N.getD (invI.getD i 0) 0 := by
    rw [invN]
    exact w183finL34_getD_map (fun j => c1N.getD j 0) hi
  rw [h1]
  exact w183finL34_c1N_getD (w183finL34_invI_lt i)

private theorem w183finL34_repN_invP (i : ℕ) (hi : i < 27) : RepN (invN.getD i 0) (invP i) := by
  have hi' : i < invI.length := by rw [invI_length]; exact hi
  rw [w183finL34_invN_getD hi', invP]
  exact repN_wN _

private theorem w183finL34_fixM_testBit {i : ℕ} (hi : i < 27) (p : Fin 42) :
    (fixM.getD i 0).testBit p.val = true ↔ (invP i) p = p := by
  have hiN : i < invN.length := by rw [invN, List.length_map]; rw [invI_length]; exact hi
  have h1 : fixM.getD i 0 = fixMask (invN.getD i 0) := by
    rw [fixM]
    exact w183finL34_getD_map fixMask hiN
  rw [h1, w183finL34_testBit_fixMask]
  constructor
  · rintro ⟨-, hget⟩
    apply Fin.ext
    rw [← w183finL34_repN_invP i hi p]
    exact hget
  · intro hp
    refine ⟨p.isLt, ?_⟩
    rw [w183finL34_repN_invP i hi p, congrArg Fin.val hp]

private theorem w183finL34_fixOK_of_triple {i j k : ℕ} (hi : i < 27) (hj : j < 27) (hk : k < 27)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hcij : cm i j = true) (hcik : cm i k = true)
    (hcjk : cm j k = true) (hprod : ((prodM.getD i []).getD j 0 != invN.getD k 0) = true) :
    fixOK (fixM.getD i 0 &&& fixM.getD j 0 &&& fixM.getD k 0) = true := by
  have h1 := List.all_eq_true.1 fix_triples i (List.mem_range.2 hi)
  have h2 := List.all_eq_true.1 h1 j (List.mem_range.2 hj)
  rw [show (i != j && cm i j) = true by simp [hij, hcij]] at h2
  simp only [Bool.not_true, Bool.false_or] at h2
  have h3 := List.all_eq_true.1 h2 k (List.mem_range.2 hk)
  have hcond2 : (k != i && k != j && cm i k && cm j k &&
      ((prodM.getD i []).getD j 0 != invN.getD k 0)) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨by simpa using hki, by simpa using hkj⟩, hcik⟩, hcjk⟩, hprod⟩
  rw [hcond2] at h3
  simpa using h3

private theorem w183finL34_mem_span3_fix {x y z : Equiv.Perm (Fin 42)} {p : Fin 42} :
    (∀ a ∈ span3 x y z, a p = p) ↔ x p = p ∧ y p = p ∧ z p = p := by
  constructor
  · intro h
    exact ⟨h x (by simp [span3]), h y (by simp [span3]), h z (by simp [span3])⟩
  · rintro ⟨hx, hy, hz⟩ a ha
    simp only [span3, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact hx
    · exact hy
    · exact hz
    · rw [Equiv.Perm.mul_apply, hy, hx]
    · rw [Equiv.Perm.mul_apply, hz, hx]
    · rw [Equiv.Perm.mul_apply, hz, hy]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hz, hy, hx]

private theorem w183finL34_e16N_length : e16N.length = 2 := by decide +kernel

private theorem w183finL34_e16N_getD_zero :
    e16N.getD 0 [] = (e16Idx.getD 0 []).map (fun i => c1N.getD i 0) := by decide +kernel

private theorem w183finL34_e16N_getD_one :
    e16N.getD 1 [] = (e16Idx.getD 1 []).map (fun i => c1N.getD i 0) := by decide +kernel

private theorem w183finL34_e16N_getD (m : ℕ) (hm : m < 2) :
    e16N.getD m [] = (e16Idx.getD m []).map (fun i => c1N.getD i 0) := by
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
  · exact w183finL34_e16N_getD_zero
  · exact w183finL34_e16N_getD_one

private theorem w183finL34_e16Idx_lt {m i : ℕ} (hm : m < 2) (hi : i ∈ e16Idx.getD m []) :
    i < 64 := by
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
  · have h : (e16Idx.getD 0 []).all (fun i => decide (i < 64)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.1 h i hi)
  · have h : (e16Idx.getD 1 []).all (fun i => decide (i < 64)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.1 h i hi)

theorem fix_counts {A : Subgroup (Equiv.Perm (Fin 42))}
    (hAC : A ≤ C₁) (hel : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A) :
    ((fixSet A 0 21).ncard = 5 ∧ (fixSet A 21 42).ncard = 1) ∨
      ((fixSet A 0 21).ncard = 1 ∧ (fixSet A 21 42).ncard = 5) := by
  rcases card_eight_or_sixteen hAC hel h8 with h8c | h16c
  ·
    obtain ⟨i, hi, j, hj, k, hk, hij, hki, hkj, hcij, hcik, hcjk, hprod, hAeq⟩ :=
      exists_triple hAC hel h8c
    have hOK : fixOK (fixM.getD i 0 &&& fixM.getD j 0 &&& fixM.getD k 0) = true :=
      w183finL34_fixOK_of_triple hi hj hk hij hki hkj hcij hcik hcjk hprod
    have hmask : ∀ p : Fin 42,
        (fixM.getD i 0 &&& fixM.getD j 0 &&& fixM.getD k 0).testBit p.val = true ↔
          ((invP i) p = p ∧ (invP j) p = p ∧ (invP k) p = p) := by
      intro p
      constructor
      · intro h
        rw [Nat.testBit_and, Nat.testBit_and] at h
        simp only [Bool.and_eq_true] at h
        exact ⟨(w183finL34_fixM_testBit hi p).1 h.1.1,
          (w183finL34_fixM_testBit hj p).1 h.1.2, (w183finL34_fixM_testBit hk p).1 h.2⟩
      · rintro ⟨h1, h2, h3⟩
        rw [Nat.testBit_and, Nat.testBit_and]
        simp only [Bool.and_eq_true]
        exact ⟨⟨(w183finL34_fixM_testBit hi p).2 h1,
          (w183finL34_fixM_testBit hj p).2 h2⟩, (w183finL34_fixM_testBit hk p).2 h3⟩
    have hfixgen : ∀ (lo : ℕ), lo + 21 ≤ 42 → ∀ p : Fin 42,
        p ∈ fixSet A lo (lo + 21) ↔ lo ≤ p.val ∧ p.val < lo + 21 ∧
          (fixM.getD i 0 &&& fixM.getD j 0 &&& fixM.getD k 0).testBit p.val = true := by
      have hmemA : ∀ a : Equiv.Perm (Fin 42), a ∈ A ↔
          a ∈ span3 (invP i) (invP j) (invP k) := fun a => Set.ext_iff.mp hAeq a
      intro lo hlo p
      rw [fixSet]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have h3' : ∀ a ∈ span3 (invP i) (invP j) (invP k), a p = p :=
          fun a ha => h3 a ((hmemA a).mpr ha)
        exact ⟨h1, h2, (hmask p).2 ((w183finL34_mem_span3_fix).1 h3')⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, ?_⟩
        intro a ha
        exact (w183finL34_mem_span3_fix).2 ((hmask p).1 h3) a ((hmemA a).mp ha)
    have h0n := w183finL34_ncard_fixSet (A := A)
      (mask := fixM.getD i 0 &&& fixM.getD j 0 &&& fixM.getD k 0) 0 (by omega)
      (hfixgen 0 (by omega))
    have h21n := w183finL34_ncard_fixSet (A := A)
      (mask := fixM.getD i 0 &&& fixM.getD j 0 &&& fixM.getD k 0) 21 (by omega)
      (hfixgen 21 (by omega))
    rw [fixOK] at hOK
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hOK
    rcases hOK with ⟨h0c, h21c⟩ | ⟨h0c, h21c⟩
    · left
      exact ⟨by rw [h0n, h0c], by rw [h21n, h21c]⟩
    · right
      exact ⟨by rw [h0n, h0c], by rw [h21n, h21c]⟩
  ·
    obtain ⟨m, hm2, hAeq⟩ := eq_e16_of_card hAC hel h16c
    have hlen : m < e16N.length := by rw [w183finL34_e16N_length]; exact hm2
    have hQmem : e16N.getD m [] ∈ e16N := by
      rw [List.getD_eq_getElem (l := e16N) (d := ([] : List ℕ)) (n := m) hlen]
      exact List.getElem_mem _
    have hOK : fixOK ((e16N.getD m []).foldl (fun m x => m &&& fixMask x) (2 ^ 42 - 1)) =
        true := List.all_eq_true.1 fix_e16 (e16N.getD m []) hQmem
    have hmemA : ∀ a : Equiv.Perm (Fin 42), a ∈ A ↔ a ∈ e16Set m :=
      fun a => Set.ext_iff.mp hAeq a
    have hfixA : ∀ p : Fin 42, (∀ a ∈ A, a p = p) ↔
        ∀ x ∈ (e16N.getD m []), getN x p.val = p.val := by
      intro p
      constructor
      · intro h x hx
        rw [w183finL34_e16N_getD m hm2] at hx
        obtain ⟨i, hi, hix⟩ := List.mem_map.1 hx
        have hi64 := w183finL34_e16Idx_lt hm2 hi
        have hxw : x = wN (c1W.getD i []) := by rw [← hix, w183finL34_c1N_getD hi64]
        have hmem : wordPerm (c1W.getD i []) ∈ e16Set m := ⟨i, hi, rfl⟩
        have hp' := h _ ((hmemA _).mpr hmem)
        rw [hxw]
        rw [repN_wN (c1W.getD i []) p]
        exact congrArg Fin.val hp'
      · intro h a ha
        obtain ⟨i, hi, hia⟩ := (hmemA a).mp ha
        have hi64 := w183finL34_e16Idx_lt hm2 hi
        have hxmem : c1N.getD i 0 ∈ e16N.getD m [] := by
          rw [w183finL34_e16N_getD m hm2]
          exact List.mem_map.mpr ⟨i, hi, rfl⟩
        have hget := h (c1N.getD i 0) hxmem
        rw [w183finL34_c1N_getD hi64] at hget
        rw [repN_wN (c1W.getD i []) p] at hget
        rw [← hia]
        exact Fin.ext hget
    have hmask : ∀ p : Fin 42,
        ((e16N.getD m []).foldl (fun m x => m &&& fixMask x) (2 ^ 42 - 1)).testBit p.val = true ↔
          ∀ x ∈ e16N.getD m [], getN x p.val = p.val := by
      intro p
      rw [w183finL34_testBit_foldl_and]
      constructor
      · rintro ⟨-, hall⟩ x hx
        have h := hall x hx
        rw [w183finL34_testBit_fixMask] at h
        exact h.2
      · intro hall
        refine ⟨?_, fun x hx => ?_⟩
        · rw [Nat.testBit_two_pow_sub_one]
          simp [p.isLt]
        · rw [w183finL34_testBit_fixMask]
          exact ⟨p.isLt, hall x hx⟩
    have hfixgen : ∀ (lo : ℕ), lo + 21 ≤ 42 → ∀ p : Fin 42,
        p ∈ fixSet A lo (lo + 21) ↔ lo ≤ p.val ∧ p.val < lo + 21 ∧
          ((e16N.getD m []).foldl (fun m x => m &&& fixMask x) (2 ^ 42 - 1)).testBit p.val =
            true := by
      intro lo hlo p
      rw [fixSet]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (hmask p).2 ((hfixA p).1 h3)⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (hfixA p).2 ((hmask p).1 h3)⟩
    have h0n := w183finL34_ncard_fixSet (A := A)
      (mask := (e16N.getD m []).foldl (fun m x => m &&& fixMask x) (2 ^ 42 - 1)) 0 (by omega)
      (hfixgen 0 (by omega))
    have h21n := w183finL34_ncard_fixSet (A := A)
      (mask := (e16N.getD m []).foldl (fun m x => m &&& fixMask x) (2 ^ 42 - 1)) 21 (by omega)
      (hfixgen 21 (by omega))
    rw [fixOK] at hOK
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hOK
    rcases hOK with ⟨h0c, h21c⟩ | ⟨h0c, h21c⟩
    · left
      exact ⟨by rw [h0n, h0c], by rw [h21n, h21c]⟩
    · right
      exact ⟨by rw [h0n, h0c], by rw [h21n, h21c]⟩

private theorem w183finL34_normalizer_fixes {A : Subgroup (Equiv.Perm (Fin 42))}
    {τ : Equiv.Perm (Fin 42)}
    (hτA : τ ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42))))
    {p : Fin 42} (hp : ∀ a ∈ A, a p = p) : ∀ a ∈ A, a (τ p) = τ p := by
  intro a ha
  have hτinv : τ⁻¹ ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42))) :=
    Subgroup.inv_mem _ hτA
  have hmem : τ⁻¹ * a * τ ∈ A := by
    have h := (Subgroup.mem_normalizer_iff.1 hτinv a).mp ha
    simpa using h
  have hfix := hp (τ⁻¹ * a * τ) hmem
  calc a (τ p) = τ ((τ⁻¹ * a * τ) p) := by
        simp [Equiv.Perm.mul_apply]
      _ = τ p := by rw [hfix]

theorem preserves_block_of_normalizes
    {A : Subgroup (Equiv.Perm (Fin 42))} (hAC : A ≤ C₁) (hel : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) {τ : Equiv.Perm (Fin 42)} (hτR : τ ∈ R)
    (hτA : τ ∈ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 42)))) :
    ∀ p : Fin 42, p.val < 21 → (τ p).val < 21 := by
  rcases w183finL34Good_of_mem_R hτR with ⟨h0, _⟩ | ⟨hsw0, hsw1⟩
  · exact h0
  · exfalso
    rcases fix_counts hAC hel h8 with ⟨h0c, h1c⟩ | ⟨h0c, h1c⟩
    · have hmap : τ '' fixSet A 0 21 ⊆ fixSet A 21 42 := by
        rintro _ ⟨p, hp, rfl⟩
        simp only [fixSet, Set.mem_setOf_eq] at hp
        obtain ⟨hp0, hp21, hpf⟩ := hp
        exact ⟨hsw0 p hp21, (τ p).isLt, w183finL34_normalizer_fixes hτA hpf⟩
      have hle := Set.ncard_le_ncard hmap
      rw [Set.ncard_image_of_injective _ τ.injective] at hle
      omega
    · have hmap : τ '' fixSet A 21 42 ⊆ fixSet A 0 21 := by
        rintro _ ⟨p, hp, rfl⟩
        simp only [fixSet, Set.mem_setOf_eq] at hp
        obtain ⟨hp21, hp42, hpf⟩ := hp
        exact ⟨Nat.zero_le _, hsw1 p hp21, w183finL34_normalizer_fixes hτA hpf⟩
      have hle := Set.ncard_le_ncard hmap
      rw [Set.ncard_image_of_injective _ τ.injective] at hle
      omega

end CFSG.LocalAnalysis.WeakClosure81.W183L34
