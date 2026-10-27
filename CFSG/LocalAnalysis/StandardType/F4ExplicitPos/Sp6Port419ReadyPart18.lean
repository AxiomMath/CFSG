module

public import CFSG.LieType.Steinberg.Adjoint.Ops

@[expose] public section

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

variable {τ : Tag}

theorem sum_zipWith_mul_without117 (v w : List ℤ) :
    (List.zipWith (· * ·) v w).sum = ∑ j ∈ Finset.range w.length, v.getD j 0 * w.getD j 0 := by
  induction v generalizing w with
  | nil => simp
  | cons a v ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [List.zipWith_cons_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp [add_comm]

theorem getD_range_map_without117 (n : ℕ) (f : ℕ → ℤ) {j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_map_mul_without117 (v : List ℤ) (s : ℤ) (j : ℕ) : (v.map (s * ·)).getD j 0 = s *
    v.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases v[j]? <;> simp

theorem getD_zipWith_sub_without117 {v w : List ℤ} {n j : ℕ} (hv : v.length = n) (hw : w.length = n)
    (hj : j < n) : (List.zipWith (· - ·) v w).getD j 0 = v.getD j 0 - w.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, hv, hw, hj]

theorem getD_eq_zero_of_forall_without117 {v : List ℤ} (h : ∀ x ∈ v,
    x = 0) (j : ℕ) : v.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : v[j]? with
  | none => rfl
  | some x => exact h x (List.mem_of_getElem? hv)

theorem rootVec_of_isRoot'_without117 {R : Type*} [CommRing R] {β : Fin τ.rank →
    ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem rootVec_of_not_isRoot'_without117 {R : Type*} [CommRing R] {β : Fin τ.rank → ℤ}
    (hβ : ¬IsRoot τ β) : rootVec τ R β = 0 :=
  dite_eq_right hβ

theorem pos_lt_without117 (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    pos α < τ.rootCertificate.roots.length :=
  (RootCertificate.exists_root_eq τ.rootCertificate_check α.2).choose_spec.1

theorem root_pos_without117 (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    τ.rootCertificate.root (pos α) = α.1 :=
  (RootCertificate.exists_root_eq τ.rootCertificate_check α.2).choose_spec.2

theorem pos_root_without117
    {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    pos ⟨τ.rootCertificate.root k, isRoot_rootCertificate_root hk⟩ = k :=
  rootCertificate_root_injOn (pos_lt_without117 _) hk (root_pos_without117 _)

theorem pos_eq_iff_without117
    {α : {v : Fin τ.rank → ℤ // IsRoot τ v}} {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) :
    pos α = k ↔ τ.rootCertificate.root k = α.1 := by
  constructor
  · rintro rfl
    exact root_pos_without117 α
  · intro h
    exact rootCertificate_root_injOn (pos_lt_without117 α) hk ((root_pos_without117 α).trans h.symm)

theorem root_simple_without117
    (j : Fin τ.rank) : τ.rootCertificate.root j = Pi.single j 1 :=
  rootCertificate_basis_table.2.1 j

namespace AVec

variable (τ) (R : Type*) [CommRing R]

variable {τ R}

@[simp] theorem interp_zero_without117 : interp τ R zero = 0 := rfl

@[simp] theorem interp_root_without117 (m : ℕ) (c : ℤ) :
    interp τ R (root m c) = (c : R) • rootVec τ R (τ.rootCertificate.root m) := rfl

@[simp] theorem interp_hvec_without117 (v : List ℤ) :
    interp τ R (hvec v) = ∑ j : Fin τ.rank, (v.getD j 0 : R) • hVec τ R j := rfl

theorem interp_hvec_of_forall_without117 {v : List ℤ} (h : ∀ x ∈ v,
    x = 0) : interp τ R (hvec v) = 0 := by
  rw [interp_hvec_without117]
  exact Finset.sum_eq_zero fun j _
      => by rw [getD_eq_zero_of_forall_without117 h, Int.cast_zero, zero_smul]

theorem interp_norm_without117 (u : AVec) : interp τ R u.norm = interp τ R u := by
  cases u with
  | zero => rfl
  | root m c =>
    simp only [norm]
    split_ifs with h
    · rw [h, interp_zero_without117, interp_root_without117, Int.cast_zero, zero_smul]
    · rfl
  | hvec v =>
    simp only [norm]
    split_ifs with h
    · rw [interp_zero_without117, interp_hvec_of_forall_without117]
      simpa using h
    · rfl

theorem interp_smul_without117 (s : ℤ) (u : AVec) : interp τ R (u.smul s) = (s : R) • interp τ R
    u := by
  cases u with
  | zero => simp [smul]
  | root m c => simp [smul, interp_norm_without117, mul_smul]
  | hvec v =>
    simp only [smul, interp_norm_without117, interp_hvec_without117, getD_map_mul_without117,
        Finset.smul_sum, Int.cast_mul,
      smul_smul]

theorem beq_iff_without117 {u v : AVec} : u.beq v = true ↔ u = v := by
  cases u <;> cases v <;> simp [beq]

theorem obeq_some_iff_without117 {u v : AVec} : obeq (some u) (some v) = true ↔ u = v := by
  simp [obeq, beq_iff_without117]

theorem interp_of_sub_without117 {u v w : AVec} (hu : u.WF τ) (hv : v.WF τ) (h : u.sub v = some w) :
    interp τ R w = interp τ R u - interp τ R v := by
  cases u with
  | zero =>
    simp only [sub, Option.some.injEq] at h
    rw [← h, interp_smul_without117, interp_zero_without117]
    simp
  | root m c =>
    cases v with
    | zero =>
      simp only [sub, Option.some.injEq] at h
      rw [← h, interp_zero_without117, sub_zero]
    | root m' c' =>
      simp only [sub] at h
      split_ifs at h with hm
      simp only [Option.some.injEq] at h
      rw [← h, interp_norm_without117, interp_root_without117, interp_root_without117,
          interp_root_without117, hm, Int.cast_sub, sub_smul]
    | hvec w' => simp [sub] at h
  | hvec v' =>
    cases v with
    | zero =>
      simp only [sub, Option.some.injEq] at h
      rw [← h, interp_zero_without117, sub_zero]
    | root m' c' => simp [sub] at h
    | hvec w' =>
      simp only [sub, Option.some.injEq] at h
      simp only [WF] at hu hv
      rw [← h, interp_norm_without117, interp_hvec_without117, interp_hvec_without117,
          interp_hvec_without117, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [getD_zipWith_sub_without117 hu hv j.2, Int.cast_sub, sub_smul]

theorem WF.norm_without117 {u : AVec} (hu : u.WF τ) : u.norm.WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    simp only [AVec.norm]
    split_ifs
    · trivial
    · exact hu
  | hvec v =>
    simp only [AVec.norm]
    split_ifs
    · trivial
    · exact hu

theorem WF.smul_without117 {u : AVec} (hu : u.WF τ) (s : ℤ) : (u.smul s).WF τ := by
  cases u with
  | zero => trivial
  | root m c =>
    simp only [AVec.smul]
    refine WF.norm_without117 ?_
    rcases hu with rfl | hm
    · exact Or.inl (mul_zero s)
    · exact Or.inr hm
  | hvec v =>
    simp only [AVec.smul]
    refine WF.norm_without117 ?_
    simp only [WF, List.length_map] at hu ⊢
    exact hu

end AVec

open AVec

theorem hUnit_length_without117 (j : Fin τ.rank) : (AdjData.hUnit j).length = τ.rank := by
  simp [AdjData.hUnit]

theorem hUnit_getD_without117 (j : Fin τ.rank) (m : Fin τ.rank) :
    (AdjData.hUnit j).getD m 0 = if m = j then 1 else 0 := by
  rw [AdjData.hUnit, getD_range_map_without117 _ _ m.2]
  simp only [Fin.val_inj]

theorem ofLabel_wf_without117 (b : Label τ) : (ofLabel b).WF τ := by
  rcases b with j | α
  · exact hUnit_length_without117 j
  · exact Or.inr (pos_lt_without117 α)

theorem interp_ofLabel_without117
    (R : Type*) [CommRing R] (b : Label τ) :
    (ofLabel b).interp τ R = Finsupp.single b 1 := by
  rcases b with j | ⟨α, hα⟩
  · simp only [ofLabel, interp_hvec_without117, hUnit_getD_without117]
    simp [hVec]
  · simp only [ofLabel, interp_root_without117, Int.cast_one, one_smul]
    rw [root_pos_without117, rootVec_of_isRoot'_without117 hα]

theorem ofLabel_mem_basis_without117
    (b : Label τ) : ofLabel b ∈ AdjData.basis τ := by
  rcases b with j | α
  · exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)
  · exact List.mem_append_left _ (List.mem_map.2 ⟨pos α, List.mem_range.2 (pos_lt_without117 α),
      rfl⟩)

namespace AdjData

variable (D : AdjData τ) (R : Type*) [CommRing R]

variable {R}

theorem recOp_single_without117 (k : ℕ) (b : Label τ) :
    D.recOp R k (Finsupp.single b 1) = (D.act k (ofLabel b)).interp τ R := by
  rw [recOp, Finsupp.linearCombination_single, one_smul]

theorem act_eq_without117 (k : ℕ) (u : AVec) : D.act k u = D.actM (D.opNat k) k u := rfl

theorem actM_root_interp_without117 (M k b : ℕ) (c : ℤ) :
    (D.actM M k (.root b c)).interp τ R = (c : R) • (D.actM M k (.root b 1)).interp τ R := by
  simp only [actM]
  split_ifs
  · simp only [interp_norm_without117, interp_hvec_without117, getD_map_mul_without117,
      Int.cast_mul, one_mul, Finset.smul_sum,
      smul_smul, List.map_id']
  · simp
  · simp only [interp_norm_without117, interp_root_without117, Int.cast_mul, one_mul, mul_smul]

theorem hpart_length_without117 (k : ℕ) : (D.hpart k).length = τ.rank := by
  simp [hpart]

end AdjData
end CFSG.LieType.Steinberg.Adjoint

end
