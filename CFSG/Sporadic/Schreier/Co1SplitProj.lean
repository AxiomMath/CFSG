module

public import CFSG.Sporadic.Schreier.Co1SplitMono
public import Certificates.Certificate16013
public import CFSG.Sporadic.Schreier.Co1SignedCover

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (rowsMatrix)
open ElemThree Matrix

theorem split_data :
    (∀ i < 6, ∀ j < 12, (Native.msSearch (Native.aRows i) j).1 = j ∧
      Native.msSgn (Native.aRows i) j = 1) ∧
    (∀ i < 2, ∀ j < 12, (Native.msSearch (Native.gRows i) j).1 =
        (Data.liftPerms.getD i []).getD j 0 ∧
      Native.msSgn (Native.gRows i) j = (Data.liftSigns.getD i []).getD j 0) ∧
    ∀ j < 12, (Native.msSearch (Native.gRows 2) j).1 = j ∧ Native.msSgn (Native.gRows 2) j = 2 := by
  have h := split_data_check
  simp only [Native.splitDataCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem msData_rows
    {X : Native.Rows} (h : Native.msOK X = true) :
    msData (rowsMatrix 24 X) = (fun j => Fin.ofNat 12 (Native.msSearch X j.val).1,
      fun j => ((Native.msSearch X j.val).2.1 : ZMod 3),
      fun j => (Native.msSgn X j.val : ZMod 3)) :=
  msData_eq (MS.of_msOK h).2 (MS.of_msOK h).1

theorem msOK_a
    (i : Fin 6) : Native.msOK (Native.aRows i.val) = true :=
  (split_parts.2.2.2.2 _ (List.mem_append_left _
    (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩))).1.2

theorem msOK_g
    (i : Fin 3) : Native.msOK (Native.gRows i.val) = true :=
  (split_parts.2.2.2.2 _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩))).1.2

theorem msData_a
    (i : Fin 6) :
    (msData ((a i : GL24) : Mat24)).1 = id ∧ (msData ((a i : GL24) : Mat24)).2.2 = 1 := by
  rw [(a_rep i).val_eq, msData_rows (msOK_a i)]
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · have := (split_data.1 i.val i.isLt j.val j.isLt).1
    apply Fin.ext
    change (Native.msSearch (Native.aRows i.val) j.val).1 % 12 = j.val
    rw [this, Nat.mod_eq_of_lt j.isLt]
  · have := (split_data.1 i.val i.isLt j.val j.isLt).2
    change ((Native.msSgn (Native.aRows i.val) j.val : ℕ) : ZMod 3) = 1
    rw [this, Nat.cast_one]

theorem msData_g
    (i : Fin 2) :
    (msData ((g i.castSucc : GL24) : Mat24)).1 = liftPerm i ∧
      (msData ((g i.castSucc : GL24) : Mat24)).2.2 = liftSign i := by
  rw [(g_rep i.castSucc).val_eq, msData_rows (msOK_g i.castSucc)]
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · have := (split_data.2.1 i.val i.isLt j.val j.isLt).1
    change Fin.ofNat 12 (Native.msSearch (Native.gRows i.val) j.val).1 = liftPerm i j
    rw [this]
    rfl
  · have := (split_data.2.1 i.val i.isLt j.val j.isLt).2
    change ((Native.msSgn (Native.gRows i.val) j.val : ℕ) : ZMod 3) = liftSign i j
    rw [this]
    rfl

theorem msData_r :
    (msData ((r : GL24) : Mat24)).1 = id ∧ (msData ((r : GL24) : Mat24)).2.2 = fun _ => 2 := by
  rw [← g_two, (g_rep 2).val_eq, msData_rows (msOK_g 2)]
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · have := (split_data.2.2 j.val j.isLt).1
    apply Fin.ext
    change (Native.msSearch (Native.gRows 2) j.val).1 % 12 = j.val
    rw [this, Nat.mod_eq_of_lt j.isLt]
  · have := (split_data.2.2 j.val j.isLt).2
    change ((Native.msSgn (Native.gRows 2) j.val : ℕ) : ZMod 3) = 2
    rw [this]
    rfl

@[expose] noncomputable def projMat :
    A →* Mat12 where
  toFun x := signedMatrix (msData ((x : GL24) : Mat24)).1 (msData ((x : GL24) : Mat24)).2.2
  map_one' := by
    rw [OneMemClass.coe_one, Units.val_one, msData_eq (fun _ => one_ne_zero) MS.one]
    exact signedMatrix_id_one
  map_mul' x y := by
    obtain ⟨hsx, hx⟩ := msData_spec (A_isMS x x.2)
    obtain ⟨hsy, hy⟩ := msData_spec (A_isMS y y.2)
    rw [Subgroup.coe_mul, Units.val_mul,
      msData_eq (fun j => mul_ne_zero (hsx _) (hsy j)) (hx.mul hy), signedMatrix_mul]

@[expose] noncomputable def proj :
    A →* GL12 := projMat.toHomUnits

theorem proj_val
    (x : A) : ((proj x : GL12) : Mat12) =
    signedMatrix (msData ((x : GL24) : Mat24)).1 (msData ((x : GL24) : Mat24)).2.2 := rfl

theorem a_mem_A (i : Fin 6) : a i ∈ A :=
  Subgroup.subset_closure (Or.inl (a_mem_E i))

theorem E_le_A : E ≤ A := fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem g_mem_A (i : Fin 2) : g i.castSucc ∈ A := by
  apply Subgroup.subset_closure
  right
  fin_cases i
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem r_mem_A : r ∈ A :=
  Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

theorem proj_a
    (i : Fin 6) : proj ⟨a i, a_mem_A i⟩ = 1 := by
  apply Units.ext
  rw [proj_val, Units.val_one]
  change signedMatrix (msData ((a i : GL24) : Mat24)).1 (msData ((a i : GL24) : Mat24)).2.2 = 1
  rw [(msData_a i).1, (msData_a i).2]
  exact signedMatrix_id_one

theorem proj_g
    (i : Fin 2) : proj ⟨g i.castSucc, g_mem_A i⟩ = σ i := by
  apply Units.ext
  rw [proj_val]
  change signedMatrix (msData ((g i.castSucc : GL24) : Mat24)).1
    (msData ((g i.castSucc : GL24) : Mat24)).2.2 = σMat i
  rw [(msData_g i).1, (msData_g i).2]
  rfl

theorem signedMatrix_two : signedMatrix id (fun _ => 2) = -1 :=
  Certificates.certificate16013

theorem proj_r :
    proj ⟨r, r_mem_A⟩ = -1 := by
  apply Units.ext
  rw [proj_val, neg_one_val]
  change signedMatrix (msData ((r : GL24) : Mat24)).1 (msData ((r : GL24) : Mat24)).2.2 = -1
  rw [msData_r.1, msData_r.2]
  exact signedMatrix_two

theorem signedMatrix_eq_one {p : Fin 12 → Fin 12} {ε : Fin 12 → ZMod 3} (hε : ∀ j, ε j ≠ 0)
    (h : signedMatrix p ε = 1) : p = id ∧ ε = 1 := by
  have key : ∀ j, p j = j ∧ ε j = 1 := by
    intro j
    have := congrFun (congrFun h (p j)) j
    simp only [signedMatrix, Matrix.of_apply, ↓reduceIte, Matrix.one_apply] at this
    by_cases hj : p j = j
    · simp only [hj, ↓reduceIte] at this
      exact ⟨hj, this⟩
    · simp only [hj, ↓reduceIte] at this
      exact absurd this (hε j)
  exact ⟨funext fun j => (key j).1, funext fun j => (key j).2⟩

theorem proj_eq_one_iff
    (x : A) : proj x = 1 ↔
    (msData ((x : GL24) : Mat24)).1 = id ∧ (msData ((x : GL24) : Mat24)).2.2 = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun u : GL12 => (u : Mat12)) h
    simp only [proj_val, Units.val_one] at h'
    exact signedMatrix_eq_one (msData_spec (A_isMS x x.2)).1 h'
  · rintro ⟨h1, h2⟩
    apply Units.ext
    rw [proj_val, h1, h2, Units.val_one]
    exact signedMatrix_id_one

theorem ker_MS
    {x : A} (hx : x ∈ proj.ker) :
    MS ((x : GL24) : Mat24) id (msData ((x : GL24) : Mat24)).2.1 1 := by
  have h := (proj_eq_one_iff x).mp (MonoidHom.mem_ker.mp hx)
  have := (msData_spec (A_isMS x x.2)).2
  rwa [h.1, h.2] at this

theorem MS.ext'
    {g h : Mat24} {p p' : Fin 12 → Fin 12} {a s a' s' : Fin 12 → ZMod 3}
    (hg : MS g p a s) (hh : MS h p' a' s') (hp : p = p') (ha : a = a') (hs : s = s') : g = h := by
  subst hp ha hs
  exact hg.ext hh

theorem A_ext {x y : A} (h : ((x : GL24) : Mat24) = ((y : GL24) : Mat24)) : x = y :=
  Subtype.ext (Units.ext h)

theorem ker_comm :
    ∀ x ∈ proj.ker, ∀ y ∈ proj.ker, x * y = y * x := by
  intro x hx y hy
  apply A_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  refine MS.ext' ((ker_MS hx).mul (ker_MS hy)) ((ker_MS hy).mul (ker_MS hx)) rfl
    (funext fun j => ?_) rfl
  simp only [id, Pi.one_apply, one_mul]
  ring

theorem ker_pow_three :
    ∀ x ∈ proj.ker, x ^ 3 = 1 := by
  intro x hx
  apply A_ext
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, Units.val_pow_eq_pow_val, Units.val_one,
    pow_three]
  refine MS.ext' ((ker_MS hx).mul ((ker_MS hx).mul (ker_MS hx))) MS.one rfl
    (funext fun j => ?_) (funext fun j => ?_)
  · simp only [id, Function.comp_apply, Pi.one_apply, one_mul, Pi.zero_apply]
    have h3 : (3 : ZMod 3) = 0 := by decide
    linear_combination (msData ((x : GL24) : Mat24)).2.1 j * h3
  · simp only [Pi.one_apply, one_mul]

theorem r_sq : r ^ 2 = 1 := by
  have h := split_conj_check
  simp only [Native.splitConjCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  have h1 : MRep (Native.mul (Native.gRows 2) (Native.gRows 2)) (g 2 * g 2) :=
    (g_rep 2).mul (g_rep 2)
  rw [h.1.2] at h1
  rw [pow_two]
  exact h1.eq MRep.one

theorem r_ne_one :
    r ≠ 1 := by
  intro hr
  have h1 : (⟨r, r_mem_A⟩ : A) = 1 := Subtype.ext hr
  have := proj_r
  rw [h1, map_one] at this
  exact one_ne_neg_one this

theorem r_inv_ker :
    ∀ x ∈ proj.ker, (⟨r, r_mem_A⟩ : A) * x * (⟨r, r_mem_A⟩ : A)⁻¹ = x⁻¹ := by
  intro x hx
  have hr2 : (⟨r, r_mem_A⟩ : A)⁻¹ = ⟨r, r_mem_A⟩ := by
    rw [inv_eq_iff_mul_eq_one]
    apply A_ext
    rw [Subgroup.coe_mul, OneMemClass.coe_one, ← pow_two]
    exact congrArg Units.val r_sq
  rw [hr2]
  apply eq_inv_of_mul_eq_one_left
  have hrMS := (msData_spec (A_isMS _ r_mem_A)).2
  rw [msData_r.1, msData_r.2] at hrMS
  apply A_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    Units.val_mul, OneMemClass.coe_one, Units.val_one]
  refine MS.ext' (((hrMS.mul (ker_MS hx)).mul hrMS).mul (ker_MS hx)) MS.one rfl
    (funext fun j => ?_) (funext fun j => ?_)
  · simp only [id, Pi.one_apply, Pi.zero_apply]
    have h3 : (3 : ZMod 3) = 0 := by decide
    linear_combination ((msData ((r : GL24) : Mat24)).2.1 j +
      2 * (msData (((x : A) : GL24) : Mat24)).2.1 j) * h3
  · simp only [Pi.one_apply]
    decide

end CFSG.Sporadic.Co1Schreier
