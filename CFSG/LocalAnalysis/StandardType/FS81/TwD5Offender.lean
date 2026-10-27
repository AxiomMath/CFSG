module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Mat
public import Certificates.Certificate709610

public section

namespace CFSG.StandardType.FrameRoute.FS81

open Certificates.WE6Offender
open scoped Matrix Pointwise

def s0Mat : Mat6 := spMat (Equiv.swap 1 2) 1

def s1Mat : Mat6 := spMat (Equiv.swap 4 5) 1

def s2Mat : Mat6 := spMat (Equiv.swap 2 3) 1

def s3Mat : Mat6 := spMat (Equiv.swap 3 4) 1

def s4Sign : Fin 6 → ZMod 3 := fun i => if i = 4 ∨ i = 5 then -1 else 1

def s4Mat : Mat6 := spMat (Equiv.swap 4 5) s4Sign

def s5Mat : Mat6 := rE6 1

def s0 : GL (Fin 6) (ZMod 3) := ⟨s0Mat, s0Mat, by decide, by decide⟩

def s1 : GL (Fin 6) (ZMod 3) := ⟨s1Mat, s1Mat, by decide, by decide⟩

def s2 : GL (Fin 6) (ZMod 3) := ⟨s2Mat, s2Mat, by decide, by decide⟩

def s3 : GL (Fin 6) (ZMod 3) := ⟨s3Mat, s3Mat, by decide, by decide⟩

def s4 : GL (Fin 6) (ZMod 3) := ⟨s4Mat, s4Mat, by decide, by decide⟩

def s5 : GL (Fin 6) (ZMod 3) := ⟨s5Mat, s5Mat, by decide, by decide⟩

theorem spMat_mem_evenFix0 {σ : Equiv.Perm (Fin 6)} {s : Fin 6 → ZMod 3} (hσ : σ 0 = 0)
    (hs0 : s 0 = 1) (hsign : IsSign s) (hprod : ∏ i : Fin 5, s i.succ = 1) :
    spMat σ s ∈ evenFix0 5 :=
  ⟨σ, s, hsign, ⟨hσ, hs0, hprod⟩, rfl⟩

theorem s0Mat_mem : s0Mat ∈ evenFix0 5 :=
  spMat_mem_evenFix0 (by decide) rfl (fun _ => Or.inl rfl) (by simp)

theorem s1Mat_mem : s1Mat ∈ evenFix0 5 :=
  spMat_mem_evenFix0 (by decide) rfl (fun _ => Or.inl rfl) (by simp)

theorem s2Mat_mem : s2Mat ∈ evenFix0 5 :=
  spMat_mem_evenFix0 (by decide) rfl (fun _ => Or.inl rfl) (by simp)

theorem s3Mat_mem : s3Mat ∈ evenFix0 5 :=
  spMat_mem_evenFix0 (by decide) rfl (fun _ => Or.inl rfl) (by simp)

theorem s4Mat_mem : s4Mat ∈ evenFix0 5 := by
  refine spMat_mem_evenFix0 (by decide) (by decide) (fun i => ?_) (by decide)
  unfold s4Sign
  by_cases h : i = 4 ∨ i = 5
  · rw [if_pos h]; exact Or.inr rfl
  · rw [if_neg h]; exact Or.inl rfl

theorem s0_mem : s0 ∈ wE6 1 := Subgroup.subset_closure (Or.inl s0Mat_mem)

theorem s1_mem : s1 ∈ wE6 1 := Subgroup.subset_closure (Or.inl s1Mat_mem)

theorem s2_mem : s2 ∈ wE6 1 := Subgroup.subset_closure (Or.inl s2Mat_mem)

theorem s3_mem : s3 ∈ wE6 1 := Subgroup.subset_closure (Or.inl s3Mat_mem)

theorem s4_mem : s4 ∈ wE6 1 := Subgroup.subset_closure (Or.inl s4Mat_mem)

theorem s5_mem : s5 ∈ wE6 1 := Subgroup.subset_closure (Or.inr rfl)

def g1u : GL (Fin 6) (ZMod 3) :=
  s2 * s1 * s4 * s3 * s2 * s0 * s2 * s3 * s1 * s4 * s3 * s2

def g2u : GL (Fin 6) (ZMod 3) := s2 * s5 * s4 * s0

theorem g1u_val : (g1u : Mat6) = g1 := by
  unfold g1u
  simp only [Units.val_mul]
  show s2Mat * s1Mat * s4Mat * s3Mat * s2Mat * s0Mat * s2Mat * s3Mat * s1Mat * s4Mat *
    s3Mat * s2Mat = g1
  unfold Certificates.WE6Offender.g1
  decide +kernel

theorem g2u_val : (g2u : Mat6) = g2 := by
  unfold g2u
  simp only [Units.val_mul]
  show s2Mat * s5Mat * s4Mat * s0Mat = g2
  unfold Certificates.WE6Offender.g2
  decide +kernel

theorem g1u_mem : g1u ∈ wE6 1 := by
  unfold g1u
  repeat' apply Subgroup.mul_mem
  all_goals first
    | exact s0_mem | exact s1_mem | exact s2_mem
    | exact s3_mem | exact s4_mem

theorem g2u_mem : g2u ∈ wE6 1 := by
  unfold g2u
  repeat' apply Subgroup.mul_mem
  all_goals first
    | exact s0_mem | exact s1_mem | exact s2_mem
    | exact s3_mem | exact s4_mem | exact s5_mem

theorem evenFix0_row_zero {A : Mat6} (hA : A ∈ evenFix0 5) :
    A 0 0 = 1 ∧ ∀ j : Fin 6, j ≠ 0 → A 0 j = 0 := by
  obtain ⟨σ, s, hsign, ⟨hσ, hs, hprod⟩, rfl⟩ := hA
  constructor
  · simp [spMat, hσ, hs]
  · intro j hj
    simp only [spMat]
    have hne : σ j ≠ 0 := by
      intro h
      exact hj (σ.injective (h.trans hσ.symm))
    exact if_neg (Ne.symm hne)

theorem rE6_row_zero (ε : ZMod 3) :
    rE6 ε 0 0 = 1 ∧ ∀ j : Fin 6, j ≠ 0 → rE6 ε 0 j = 0 := by
  have h : rE6 ε = 1 + Matrix.vecMulVec ![0, 1, 1, 1, 1, ε] ![1, -1, -1, -1, -1, -ε] := rfl
  rw [h]
  constructor
  · simp [Matrix.vecMulVec]
  · intro j hj
    have h0 : ¬ (0 : Fin 6) = j := fun h => hj h.symm
    simp [Matrix.vecMulVec, h0]

theorem row_mul {x y : GL (Fin 6) (ZMod 3)}
    (hx0 : (x : Mat6) 0 0 = 1) (hxj : ∀ j : Fin 6, j ≠ 0 → (x : Mat6) 0 j = 0)
    (hy0 : (y : Mat6) 0 0 = 1) (hyj : ∀ j : Fin 6, j ≠ 0 → (y : Mat6) 0 j = 0) :
    ((x * y : GL (Fin 6) (ZMod 3)) : Mat6) 0 0 = 1 ∧
      ∀ j : Fin 6, j ≠ 0 → ((x * y : GL (Fin 6) (ZMod 3)) : Mat6) 0 j = 0 := by
  constructor
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hx0, hy0, one_mul]
    · intro k _ hk
      rw [hxj k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin 6)) h
  · intro j hj
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hx0, one_mul]
      exact hyj j hj
    · intro k _ hk
      rw [hxj k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin 6)) h

theorem row_inv {x : GL (Fin 6) (ZMod 3)}
    (hx0 : (x : Mat6) 0 0 = 1) (hxj : ∀ j : Fin 6, j ≠ 0 → (x : Mat6) 0 j = 0) :
    ((x⁻¹ : GL (Fin 6) (ZMod 3)) : Mat6) 0 0 = 1 ∧
      ∀ j : Fin 6, j ≠ 0 → ((x⁻¹ : GL (Fin 6) (ZMod 3)) : Mat6) 0 j = 0 := by
  have hxunit : (x : Mat6) * (((x⁻¹ : GL (Fin 6) (ZMod 3))) : Mat6) = 1 :=
    (Units.val_mul x x⁻¹).symm.trans (by rw [mul_inv_cancel, Units.val_one])
  constructor
  · have h := congrFun (congrFun hxunit 0) 0
    rw [Matrix.mul_apply, Finset.sum_eq_single 0, Matrix.one_apply_eq] at h
    · rw [hx0, one_mul] at h
      exact h
    · intro k _ hk
      rw [hxj k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin 6)) h
  · intro j hj
    have h := congrFun (congrFun hxunit 0) j
    rw [Matrix.mul_apply, Finset.sum_eq_single 0, Matrix.one_apply_ne (Ne.symm hj)] at h
    · rw [hx0, one_mul] at h
      exact h
    · intro k _ hk
      rw [hxj k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin 6)) h

theorem wE6_row_zero (ε : ZMod 3) {u : GL (Fin 6) (ZMod 3)} (hu : u ∈ wE6 ε) :
    (u : Mat6) 0 0 = 1 ∧ ∀ j : Fin 6, j ≠ 0 → (u : Mat6) 0 j = 0 := by
  have key : ∀ x ∈ wE6 ε, (x : Mat6) 0 0 = 1 ∧ ∀ j : Fin 6, j ≠ 0 → (x : Mat6) 0 j = 0 := by
    intro x hx
    refine Subgroup.closure_induction (k := {A : GL (Fin 6) (ZMod 3) |
      (A : Mat6) ∈ evenFix0 5 ∨ (A : Mat6) = rE6 ε}) (p := fun x _ =>
      (x : Mat6) 0 0 = 1 ∧ ∀ j : Fin 6, j ≠ 0 → (x : Mat6) 0 j = 0) ?_ ?_ ?_ ?_ hx
    · rintro A (hA | hA)
      · exact evenFix0_row_zero hA
      · rw [hA]
        exact rE6_row_zero ε
    · exact ⟨by simp, fun j hj => Matrix.one_apply_ne (Ne.symm hj)⟩
    · rintro x y _ _ ⟨hx0, hxj⟩ ⟨hy0, hyj⟩
      exact row_mul hx0 hxj hy0 hyj
    · rintro x _ ⟨hx0, hxj⟩
      exact row_inv hx0 hxj
  exact key u hu

def P : Subgroup (GL (Fin 6) (ZMod 3)) := Subgroup.closure {g1u, g2u}

theorem P_le_wE6 : P ≤ wE6 1 := by
  rw [P, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact g1u_mem
  · exact g2u_mem

theorem check_LAt_zero (hc : check () = true) : LAt 0 = 1 :=
  of_decide_eq_true (check_of_mem hc (b := decide (LAt 0 = 1)) (by
    rw [checkParts]; exact List.mem_cons_self))

theorem check_nodup (hc : check () = true) : L.Nodup :=
  of_decide_eq_true (check_of_mem hc (b := decide L.Nodup) (by
    rw [checkParts]
    exact List.mem_cons_of_mem _ List.mem_cons_self))

theorem check_mul_g1 (hc : check () = true) :
    ∀ i : Fin 81, ∃ j : Fin 81, LAt j = LAt i * g1 :=
  of_decide_eq_true (check_of_mem hc
    (b := decide (∀ i : Fin 81, ∃ j : Fin 81, LAt j = LAt i * g1)) (by
      rw [checkParts]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))))

theorem check_mul_g2 (hc : check () = true) :
    ∀ i : Fin 81, ∃ j : Fin 81, LAt j = LAt i * g2 :=
  of_decide_eq_true (check_of_mem hc
    (b := decide (∀ i : Fin 81, ∃ j : Fin 81, LAt j = LAt i * g2)) (by
      rw [checkParts]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))))

theorem check_noncomm (hc : check () = true) : g1 * g2 ≠ g2 * g1 :=
  of_decide_eq_true (check_of_mem hc (b := decide (g1 * g2 ≠ g2 * g1)) (by
    rw [checkParts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))))

theorem LAt_injective (hc : check () = true) : Function.Injective LAt := by
  intro i j hij
  have hnd := check_nodup hc
  have h1 : (⟨i.val, by rw [L_length]; exact i.isLt⟩ : Fin L.length) =
      ⟨j.val, by rw [L_length]; exact j.isLt⟩ := hnd.get_inj_iff.mp hij
  have h2 := congrArg (fun k : Fin L.length => k.val) h1
  exact Fin.ext h2

theorem exists_LAt_of_mem {z : Mat6} (hz : z ∈ L) : ∃ i : Fin 81, LAt i = z := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
  have hi' : i.val < 81 := by rw [← L_length]; exact i.isLt
  refine ⟨⟨i.val, hi'⟩, ?_⟩
  have h2 : LAt ⟨i.val, hi'⟩ = L.get i := rfl
  rw [h2, hi]

theorem LAt_zero_eq_one (hc : check () = true) {h : 0 < 81} : LAt ⟨0, h⟩ = 1 := by
  rw [show (⟨0, h⟩ : Fin 81) = 0 from Fin.ext rfl]
  exact check_LAt_zero hc

theorem LAt_one_eq_g1 : LAt 1 = g1 := by decide +kernel

theorem LAt_two_eq_g2 : LAt 2 = g2 := by decide +kernel

theorem submonoid_inv_mem {G : Type*} [Group G] [Finite G] (M : Submonoid G) {x : G}
    (hx : x ∈ M) : x⁻¹ ∈ M := by
  have hpos : 0 < orderOf x := orderOf_pos x
  have h1 : x * x ^ (orderOf x - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have h2 : x⁻¹ = x ^ (orderOf x - 1) := (eq_inv_of_mul_eq_one_right h1).symm
  rw [h2]
  exact Submonoid.pow_mem M hx _

def M : Submonoid (GL (Fin 6) (ZMod 3)) := Submonoid.closure {g1u, g2u}

theorem M_mul_mem_L (hc : check () = true) :
    ∀ x ∈ M, ∀ z : Mat6, z ∈ L → z * (x : Mat6) ∈ L := by
  intro x hx
  change x ∈ Submonoid.closure ({g1u, g2u} : Set (GL (Fin 6) (ZMod 3))) at hx
  refine Submonoid.closure_induction
    (s := ({g1u, g2u} : Set (GL (Fin 6) (ZMod 3))))
    (motive := fun x _ => ∀ z : Mat6, z ∈ L → z * (x : Mat6) ∈ L) ?_ ?_ ?_ hx
  · intro y hy z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [g1u_val]
      obtain ⟨i, hi⟩ := exists_LAt_of_mem hz
      obtain ⟨j, hj⟩ := check_mul_g1 hc i
      rw [← hi, ← hj]
      exact List.get_mem L _
    · rw [g2u_val]
      obtain ⟨i, hi⟩ := exists_LAt_of_mem hz
      obtain ⟨j, hj⟩ := check_mul_g2 hc i
      rw [← hi, ← hj]
      exact List.get_mem L _
  · intro z hz
    simpa using hz
  · intro x y hx hy ihx ihy z hz
    rw [Units.val_mul, ← mul_assoc]
    exact ihy _ (ihx z hz)

def Msub : Subgroup (GL (Fin 6) (ZMod 3)) where
  toSubmonoid := M
  inv_mem' := fun {_x} hx => submonoid_inv_mem M hx

theorem P_le_Msub : P ≤ Msub := by
  rw [P, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Submonoid.subset_closure (by simp)
  · exact Submonoid.subset_closure (by simp)

theorem P_mat_mem_L (hc : check () = true) : ∀ x ∈ P, (x : Mat6) ∈ L := by
  intro x hx
  have hxM : x ∈ M := P_le_Msub hx
  have h1 : (1 : Mat6) ∈ L := by
    rw [← check_LAt_zero hc]
    exact List.get_mem L _
  simpa using M_mul_mem_L hc x hxM 1 h1

theorem P_card_le (hc : check () = true) : Nat.card P ≤ 81 := by
  have hex : ∀ x : P, ∃ i : Fin 81, LAt i = (((x : P) : GL (Fin 6) (ZMod 3)) : Mat6) := by
    intro x
    exact exists_LAt_of_mem (P_mat_mem_L hc x x.2)
  let f : P → Fin 81 := fun x => Classical.choose (hex x)
  have hf : Function.Injective f := by
    intro x y hxy
    have hx := Classical.choose_spec (hex x)
    have hy := Classical.choose_spec (hex y)
    apply Subtype.ext
    apply Units.ext
    rw [← hx, ← hy]
    exact congrArg LAt hxy
  have := Nat.card_le_card_of_injective f hf
  simpa using this

def bfsParent : List ℕ :=
[
  0, 0, 0, 1, 1, 2, 2, 3, 4, 4, 5, 5, 6, 7, 7,
  8, 8, 9, 10, 11, 11, 12, 12, 13, 13, 14, 15, 16, 16, 17,
  17, 18, 18, 19, 19, 21, 22, 23, 24, 24, 25, 25, 26, 26, 27,
  27, 29, 30, 31, 31, 33, 34, 35, 37, 37, 38, 38, 40, 41, 42,
  42, 44, 45, 46, 48, 49, 50, 53, 53, 55, 56, 57, 59, 60, 61,
  64, 67, 68, 69, 72, 76]

def bfsGen : List ℕ :=
[
  0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
  1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0,
  1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0,
  1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1]

theorem bfsParent_lt : ∀ k : Fin 81, bfsParent.getD k.val 0 < 81 := by decide

theorem bfsParent_lt_self : ∀ k : Fin 81, k.val ≠ 0 → bfsParent.getD k.val 0 < k.val := by
  decide

def bfsParentAt (k : Fin 81) : Fin 81 := ⟨bfsParent.getD k.val 0, bfsParent_lt k⟩

theorem P_noncomm (hc : check () = true) : (g1u : GL (Fin 6) (ZMod 3)) * g2u ≠ g2u * g1u := by
  intro h
  refine check_noncomm hc ?_
  have h' := congrArg (fun u : GL (Fin 6) (ZMod 3) => (u : Mat6)) h
  simpa only [Units.val_mul, g1u_val, g2u_val] using h'

theorem bfs_all : ((List.range' 1 80).map (fun n => Fin.ofNat 81 n)).all (fun k => decide (
    LAt k = LAt (bfsParentAt k) * (if bfsGen.getD k.val 0 = 0 then g1 else g2))) = true := by
  decide +kernel

theorem bfs_step (k : Fin 81) (hk : k.val ≠ 0) :
    LAt k = LAt (bfsParentAt k) * (if bfsGen.getD k.val 0 = 0 then g1 else g2) := by
  have hall := bfs_all
  rw [List.all_eq_true] at hall
  have hk1 : 1 ≤ k.val := by omega
  have hk80 : k.val - 1 < 80 := by omega
  have hmem : k ∈ (List.range' 1 80).map (fun n => Fin.ofNat 81 n) := by
    rw [List.mem_map]
    refine ⟨k.val, List.mem_range'.mpr ⟨k.val - 1, hk80, by omega⟩, ?_⟩
    exact Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt k.isLt])
  exact of_decide_eq_true (hall k hmem)

theorem exists_mem_P_of_LAt (hc : check () = true) (k : Fin 81) :
    ∃ u : GL (Fin 6) (ZMod 3), u ∈ P ∧ (u : Mat6) = LAt k := by
  have key : ∀ n (hn : n < 81), ∃ u : GL (Fin 6) (ZMod 3), u ∈ P ∧ (u : Mat6) = LAt ⟨n, hn⟩ := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases h0 : n = 0
      · subst h0
        exact ⟨1, Subgroup.one_mem _, by rw [Units.val_one, LAt_zero_eq_one hc]⟩
      · have hlt : bfsParent.getD n 0 < n := bfsParent_lt_self ⟨n, hn⟩ h0
        obtain ⟨u, huP, hu⟩ := ih (bfsParent.getD n 0) hlt (Nat.lt_trans hlt hn)
        refine ⟨u * (if bfsGen.getD n 0 = 0 then g1u else g2u), Subgroup.mul_mem _ huP ?_, ?_⟩
        · split_ifs
          · exact Subgroup.subset_closure (Or.inl rfl)
          · exact Subgroup.subset_closure (Or.inr rfl)
        · rw [Units.val_mul, hu, bfs_step ⟨n, hn⟩ h0]
          split_ifs with hg
          · rw [g1u_val]
            rfl
          · rw [g2u_val]
            rfl
  exact key k.val k.isLt

theorem P_card_ge (hc : check () = true) : 81 ≤ Nat.card P := by
  have hex : ∀ i : Fin 81, ∃ u : P, (((u : P) : GL (Fin 6) (ZMod 3)) : Mat6) = LAt i := by
    intro i
    obtain ⟨u, huP, hu⟩ := exists_mem_P_of_LAt hc i
    exact ⟨⟨u, huP⟩, hu⟩
  choose g hg using hex
  have hg' : Function.Injective g := by
    intro i j hij
    have h1 : ((g i : P) : GL (Fin 6) (ZMod 3)) = ((g j : P) : GL (Fin 6) (ZMod 3)) :=
      congrArg Subtype.val hij
    have h2 : ((((g i : P) : GL (Fin 6) (ZMod 3))) : Mat6) =
        ((((g j : P) : GL (Fin 6) (ZMod 3))) : Mat6) :=
      congrArg (fun u : GL (Fin 6) (ZMod 3) => (u : Mat6)) h1
    rw [hg i, hg j] at h2
    exact LAt_injective hc h2
  have hle := Nat.card_le_card_of_injective g hg'
  simpa using hle

theorem P_card (hc : check () = true) : Nat.card P = 81 :=
  le_antisymm (P_card_le hc) (P_card_ge hc)

def Psub : Subgroup ↥(wE6 1) := P.subgroupOf (wE6 1)

theorem Psub_card (hc : check () = true) : Nat.card Psub = 81 := by
  have hmap : Nat.card (Psub.map (Subgroup.subtype (wE6 1))) = Nat.card Psub :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (wE6 1))
  rw [Psub, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr P_le_wE6, P_card hc] at hmap
  exact hmap.symm

theorem Psub_isPGroup (hc : check () = true) : IsPGroup 3 Psub := by
  apply IsPGroup.of_card (n := 4)
  rw [Psub_card hc]
  norm_num

theorem three_not_dvd_index (hc : check () = true) (hdvd : Nat.card (wE6 1) ∣ 51840) :
    ¬ 3 ∣ Psub.index := by
  intro h3
  have hcard : Nat.card ↥(wE6 1) = 81 * Psub.index := by
    rw [← Psub_card hc, Subgroup.card_mul_index]
  have hdvd' : 81 * Psub.index ∣ 81 * 640 := by
    have h1 : (81 * 640 : ℕ) = 51840 := by norm_num
    rw [h1, ← hcard]
    exact hdvd
  have h640 : Psub.index ∣ 640 := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 81)).mp hdvd'
  have h3' : 3 ∣ 640 := dvd_trans h3 h640
  norm_num at h3'

def Psyl (hc : check () = true) (hdvd : Nat.card (wE6 1) ∣ 51840) : Sylow 3 ↥(wE6 1) :=
  (Psub_isPGroup hc).toSylow (three_not_dvd_index hc hdvd)

theorem Asub_isPGroup {A : Subgroup (GL (Fin 6) (ZMod 3))} (_hA : A ≤ wE6 1)
    (hAe : CFSG.Open.IsElemAbelian 3 A) : IsPGroup 3 (A.subgroupOf (wE6 1)) := by
  intro x
  refine ⟨1, ?_⟩
  show x ^ (3 ^ 1) = 1
  rw [pow_one]
  apply Subtype.ext
  apply Subtype.ext
  show (x : GL (Fin 6) (ZMod 3)) ^ 3 = 1
  exact hAe.2 _ (Subgroup.mem_subgroupOf.mp x.2)

theorem exists_conj_le_P (hc : check () = true) (hdvd : Nat.card (wE6 1) ∣ 51840)
    {A : Subgroup (GL (Fin 6) (ZMod 3))} (hA : A ≤ wE6 1) (hAe : CFSG.Open.IsElemAbelian 3 A) :
    ∃ u : GL (Fin 6) (ZMod 3), u ∈ wE6 1 ∧ A ≤ P.map (MulAut.conj u) := by
  obtain ⟨Q, hAQ⟩ := (Asub_isPGroup hA hAe).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(wE6 1)) (Psyl hc hdvd) Q
  refine ⟨(g : GL (Fin 6) (ZMod 3)), g.2, ?_⟩
  intro a ha
  have hmem : (⟨a, hA ha⟩ : ↥(wE6 1)) ∈ (g • Psyl hc hdvd : Sylow 3 ↥(wE6 1)) := by
    rw [hg]
    exact hAQ (Subgroup.mem_subgroupOf.mpr ha)
  have hmem2 : (⟨a, hA ha⟩ : ↥(wE6 1)) ∈
      (MulAut.conj g • (Psyl hc hdvd : Subgroup ↥(wE6 1))) := by
    rw [← Sylow.coe_subgroup_smul]
    exact hmem
  obtain ⟨s, hs, hconj⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hmem2
  refine ⟨(s : GL (Fin 6) (ZMod 3)), Subgroup.mem_subgroupOf.mp hs, ?_⟩
  have h2 := congrArg (fun z : ↥(wE6 1) => (z : GL (Fin 6) (ZMod 3))) hconj
  exact h2

theorem check_true : check () = true :=
  Certificates.certificate709610

theorem mulVec_zero_of_mem_wE6 {ε : ZMod 3} {g : GL (Fin 6) (ZMod 3)}
    (hg : g ∈ wE6 ε) {v : Vec6} (hv : v 0 = 0) : ((g : Mat6) *ᵥ v) 0 = 0 := by
  obtain ⟨h0, hj⟩ := wE6_row_zero ε hg
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_eq_single 0]
  · rw [h0, hv, one_mul]
  · intro k _ hk
    rw [hj k hk, zero_mul]
  · exact fun h => absurd (Finset.mem_univ (0 : Fin 6)) h

theorem card_fixedB1_matrix (M : Mat6) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ M *ᵥ v = v} = (fixedB1 M).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem inv_mulVec_mulVec_six (g : GL (Fin 6) (ZMod 3)) (v : Vec6) :
    ((g.inv : Mat6) *ᵥ ((g : Mat6) *ᵥ v)) = v := by
  rw [Matrix.mulVec_mulVec, g.inv_val, Matrix.one_mulVec]

theorem mulVec_inv_mulVec_six (g : GL (Fin 6) (ZMod 3)) (v : Vec6) :
    ((g : Mat6) *ᵥ ((g.inv : Mat6) *ᵥ v)) = v := by
  rw [Matrix.mulVec_mulVec, g.val_inv, Matrix.one_mulVec]

theorem mulVec_conj_fixed (g a : GL (Fin 6) (ZMod 3)) (v : Vec6)
    (hv : (a : Mat6) *ᵥ v = v) :
    ((MulAut.conj g a : GL (Fin 6) (ZMod 3)) : Mat6) *ᵥ ((g : Mat6) *ᵥ v) =
      (g : Mat6) *ᵥ v := by
  have hval : ((MulAut.conj g a : GL (Fin 6) (ZMod 3)) : Mat6) =
      (g : Mat6) * (a : Mat6) * (g.inv : Mat6) := by
    rw [MulAut.conj_apply]
    rfl
  rw [hval]
  calc ((g : Mat6) * (a : Mat6) * (g.inv : Mat6)) *ᵥ ((g : Mat6) *ᵥ v)
      = ((g : Mat6) * (a : Mat6)) *ᵥ ((g.inv : Mat6) *ᵥ ((g : Mat6) *ᵥ v)) := by
          rw [← Matrix.mulVec_mulVec]
    _ = ((g : Mat6) * (a : Mat6)) *ᵥ v := by rw [inv_mulVec_mulVec_six]
    _ = (g : Mat6) *ᵥ ((a : Mat6) *ᵥ v) := by rw [← Matrix.mulVec_mulVec]
    _ = (g : Mat6) *ᵥ v := by rw [hv]

noncomputable def fixedConjEquiv (g : GL (Fin 6) (ZMod 3))
    (hg : ∀ v : Vec6, v 0 = 0 → ((g : Mat6) *ᵥ v) 0 = 0)
    (hgi : ∀ v : Vec6, v 0 = 0 → ((g.inv : Mat6) *ᵥ v) 0 = 0)
    (A : Subgroup (GL (Fin 6) (ZMod 3))) :
    {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ A, (a : Mat6) *ᵥ v = v} ≃
      {v : Vec6 // v 0 = 0 ∧
        ∀ a ∈ A.map (MulAut.conj g : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)),
          ((a : GL (Fin 6) (ZMod 3)) : Mat6) *ᵥ v = v} where
  toFun v := ⟨(g : Mat6) *ᵥ v, hg v v.2.1, by
    rintro a ⟨b, hb, rfl⟩
    exact mulVec_conj_fixed g b v.1 (v.2.2 b hb)⟩
  invFun v := ⟨(g.inv : Mat6) *ᵥ v, hgi v v.2.1, by
    intro a ha
    have hb : MulAut.conj g a ∈
        A.map (MulAut.conj g : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)) :=
      Subgroup.mem_map_of_mem _ ha
    have hfix : ((MulAut.conj g a : GL (Fin 6) (ZMod 3)) : Mat6) *ᵥ v.1 = v.1 :=
      v.2.2 _ hb
    have hval : ((MulAut.conj g a : GL (Fin 6) (ZMod 3)) : Mat6) =
        (g : Mat6) * (a : Mat6) * (g.inv : Mat6) := by
      rw [MulAut.conj_apply]
      rfl
    rw [hval] at hfix
    rw [Matrix.mulVec_mulVec]
    calc ((a : Mat6) * (g.inv : Mat6)) *ᵥ v.1
        = ((g.inv : Mat6) * ((g : Mat6) * (a : Mat6) * (g.inv : Mat6))) *ᵥ v.1 := by
            congr 1
            rw [← Matrix.mul_assoc (g.inv : Mat6) ((g : Mat6) * (a : Mat6)) (g.inv : Mat6),
              ← Matrix.mul_assoc (g.inv : Mat6) (g : Mat6) (a : Mat6),
              g.inv_val, Matrix.one_mul]
      _ = (g.inv : Mat6) *ᵥ (((g : Mat6) * (a : Mat6) * (g.inv : Mat6)) *ᵥ v.1) := by
            rw [Matrix.mulVec_mulVec]
      _ = (g.inv : Mat6) *ᵥ v.1 := by rw [hfix]⟩
  left_inv v := by
    apply Subtype.ext
    exact inv_mulVec_mulVec_six g v.1
  right_inv v := by
    apply Subtype.ext
    exact mulVec_inv_mulVec_six g v.1

@[expose] def dSign : Fin 6 → ZMod 3 := fun i => if i = 5 then -1 else 1

@[expose] def dMat : Mat6 := spMat 1 dSign

@[expose] def wE6SignGL : GL (Fin 6) (ZMod 3) := ⟨dMat, dMat, by decide, by decide⟩

theorem wE6SignGL_mul_self : wE6SignGL * wE6SignGL = 1 := by
  apply Units.ext
  show dMat * dMat = 1
  decide

theorem dGL_inv : wE6SignGL⁻¹ = wE6SignGL :=
  inv_eq_of_mul_eq_one_right wE6SignGL_mul_self

theorem dGL_mulVec_zero {v : Vec6} (hv : v 0 = 0) :
    ((wE6SignGL : Mat6) *ᵥ v) 0 = 0 := by
  show (dMat *ᵥ v) 0 = 0
  rw [dMat, spMat_mulVec]
  simp only [Equiv.Perm.one_symm, Equiv.Perm.one_apply]
  simp [dSign, hv]

theorem conj_dGL_mem_evenFix0 {A : GL (Fin 6) (ZMod 3)}
    (hA : (A : Mat6) ∈ evenFix0 5) :
    ((MulAut.conj wE6SignGL A : GL (Fin 6) (ZMod 3)) : Mat6) ∈ evenFix0 5 := by
  obtain ⟨σ, s, hs, ⟨hσ, hs0, hprod⟩, hAeq⟩ := hA
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, dGL_inv, hAeq]
  let s' : Fin 6 → ZMod 3 := fun j => dSign (σ j) * s j * dSign j
  have hfull : ∏ j : Fin 6, s j = 1 := by
    rw [Fin.prod_univ_succ, hs0, one_mul, hprod]
  have hfull' : ∏ j : Fin 6, s' j = 1 := by
    have hcomp : ∏ j : Fin 6, dSign (σ j) = ∏ j : Fin 6, dSign j :=
      Equiv.prod_comp σ dSign
    have hsq : (∏ j : Fin 6, dSign j) * (∏ j : Fin 6, dSign j) = 1 := by
      rw [Fin.prod_univ_succ]
      decide +kernel
    calc ∏ j, s' j = (∏ j, dSign (σ j)) * (∏ j, s j) * (∏ j, dSign j) := by
          simp [s', Finset.prod_mul_distrib]
      _ = 1 := by rw [hcomp, hfull, mul_one, hsq]
  refine ⟨σ, s', ?_, ⟨hσ, ?_, ?_⟩, ?_⟩
  · intro j
    have hd : ∀ i, dSign i = 1 ∨ dSign i = -1 := by
      intro i
      by_cases h : i = 5 <;> simp [dSign, h]
    rcases hd (σ j) with h1 | h1 <;> rcases hs j with h2 | h2 <;>
      rcases hd j with h3 | h3 <;> simp [s', h1, h2, h3] <;> decide +kernel
  · simp [s', hσ, hs0, dSign]
  · have hs'0 : s' 0 = 1 := by simp [s', hσ, hs0, dSign]
    rw [Fin.prod_univ_succ] at hfull'
    simpa [hs'0] using hfull'
  · show dMat * spMat σ s * dMat = spMat σ s'
    rw [show dMat = spMat (1 : Equiv.Perm (Fin 6)) dSign from rfl,
      spMat_mul, spMat_mul]
    congr 1

theorem exists_LAt_ordAt_of_mem_P
    {x : GL (Fin 6) (ZMod 3)} (hx : x ∈ P) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ i : Fin 81, LAt i = (x : Mat6) ∧ ordAt i = true := by
  have hc : check () = true := check_true
  obtain ⟨i, hi⟩ := exists_LAt_of_mem (P_mat_mem_L hc x hx)
  refine ⟨i, hi, ?_⟩
  rw [check_ordOK hc i]
  constructor
  · rw [hi, ← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  · intro h
    exact hx1 (Units.ext (hi.symm.trans h))

theorem card_fixedB1_matrix_pair (M N : Mat6) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ M *ᵥ v = v ∧ N *ᵥ v = v} =
      (fixedB1 M ∩ fixedB1 N).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext v
  simp [fixedB1, and_assoc, and_left_comm]

theorem card_fixedB1_matrix_triple (M N O : Mat6) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ M *ᵥ v = v ∧ N *ᵥ v = v ∧ O *ᵥ v = v} =
      (fixedB1 M ∩ fixedB1 N ∩ fixedB1 O).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext v
  simp [fixedB1, and_assoc, and_left_comm]

theorem card_fixed_subgroup_le_fixedB1 (B : Subgroup (GL (Fin 6) (ZMod 3)))
    {a : GL (Fin 6) (ZMod 3)} (ha : a ∈ B) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ b ∈ B, (b : Mat6) *ᵥ v = v} ≤
      (fixedB1 (a : Mat6)).card := by
  rw [← card_fixedB1_matrix (a : Mat6)]
  exact Nat.card_mono (Set.toFinite _) fun v hv => ⟨hv.1, hv.2 a ha⟩

theorem card_fixed_subgroup_le_inter (B : Subgroup (GL (Fin 6) (ZMod 3)))
    {a b : GL (Fin 6) (ZMod 3)} (ha : a ∈ B) (hb : b ∈ B) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ c ∈ B, (c : Mat6) *ᵥ v = v} ≤
      (fixedB1 (a : Mat6) ∩ fixedB1 (b : Mat6)).card := by
  rw [← card_fixedB1_matrix_pair (a : Mat6) (b : Mat6)]
  exact Nat.card_mono (Set.toFinite _) fun v hv => ⟨hv.1, hv.2 a ha, hv.2 b hb⟩

theorem card_fixed_subgroup_le_triple (B : Subgroup (GL (Fin 6) (ZMod 3)))
    {a b c : GL (Fin 6) (ZMod 3)} (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ d ∈ B, (d : Mat6) *ᵥ v = v} ≤
      (fixedB1 (a : Mat6) ∩ fixedB1 (b : Mat6) ∩ fixedB1 (c : Mat6)).card := by
  rw [← card_fixedB1_matrix_triple (a : Mat6) (b : Mat6) (c : Mat6)]
  exact Nat.card_mono (Set.toFinite _) fun v hv => ⟨hv.1, hv.2 a ha, hv.2 b hb, hv.2 c hc⟩

@[expose] def twoGenProducts (a b : GL (Fin 6) (ZMod 3)) : Finset (GL (Fin 6) (ZMod 3)) :=
  Finset.univ.image fun pq : Fin 3 × Fin 3 => a ^ pq.1.val * b ^ pq.2.val

theorem exists_second_index
    {B : Subgroup (GL (Fin 6) (ZMod 3))} (hB : B ≤ P) (hel : CFSG.Open.IsElemAbelian 3 B)
    {av : GL (Fin 6) (ZMod 3)} (hav : av ∈ B)
    (hzlt : Nat.card (Subgroup.zpowers av) < Nat.card B)
    {i : Fin 81} (hi : LAt i = (av : Mat6)) :
    ∃ (bv : GL (Fin 6) (ZMod 3)) (_ : bv ∈ B) (j : Fin 81), LAt j = (bv : Mat6) ∧
      ordAt j = true ∧ commAt i j = true ∧ j ≠ i ∧ LAt j ≠ LAt i * LAt i := by
  classical
  have hc : check () = true := check_true
  have hzB : Subgroup.zpowers av ≤ B := Subgroup.zpowers_le.mpr hav
  have hzne : Subgroup.zpowers av ≠ B := by
    intro h
    have := congrArg (fun H : Subgroup (GL (Fin 6) (ZMod 3)) => Nat.card H) h
    omega
  have hzne' : (Subgroup.zpowers av : Set (GL (Fin 6) (ZMod 3))) ≠ (B : Set _) := by
    intro h
    exact hzne (Subgroup.ext (Set.ext_iff.mp h))
  obtain ⟨bv, hbvB, hbvz⟩ :=
    Set.exists_of_ssubset (Set.ssubset_iff_subset_ne.mpr ⟨hzB, hzne'⟩)
  have hbv3 : bv ^ 3 = 1 := hel.2 bv hbvB
  have hbv1 : bv ≠ 1 := by
    intro h
    rw [h] at hbvz
    exact hbvz (Subgroup.one_mem _)
  obtain ⟨j, hj, hjord⟩ := exists_LAt_ordAt_of_mem_P (hB hbvB) hbv3 hbv1
  have hcomm_ab : av * bv = bv * av := by
    have h := hel.1.is_comm.comm (⟨av, hav⟩ : B) ⟨bv, hbvB⟩
    simpa using congrArg (fun z : B => (z : GL (Fin 6) (ZMod 3))) h
  refine ⟨bv, hbvB, j, hj, hjord, ?_, ?_, ?_⟩
  · rw [check_commOK hc i j]
    simpa [hi, hj] using congrArg (fun z : GL (Fin 6) (ZMod 3) => (z : Mat6)) hcomm_ab
  · intro h
    apply hbvz
    have hba : bv = av := by
      apply Units.ext
      rw [← hj, h, hi]
    rw [hba]
    exact Subgroup.mem_zpowers av
  · intro h
    apply hbvz
    have hb_sq : bv = av * av := by
      apply Units.ext
      calc (bv : Mat6) = LAt j := hj.symm
        _ = LAt i * LAt i := h
        _ = ((av * av : GL (Fin 6) (ZMod 3)) : Mat6) := by rw [hi, Units.val_mul]
    rw [hb_sq]
    exact (Subgroup.zpowers av).mul_mem (Subgroup.mem_zpowers av) (Subgroup.mem_zpowers av)

theorem exists_mem_not_products {B : Subgroup (GL (Fin 6) (ZMod 3))}
    (hcard : Nat.card B = 27) {av bv : GL (Fin 6) (ZMod 3)} :
    ∃ cv ∈ B, cv ∉ twoGenProducts av bv := by
  classical
  let T : Finset (GL (Fin 6) (ZMod 3)) := twoGenProducts av bv
  have hTcard : T.card ≤ 9 := by
    calc T.card ≤ (Finset.univ : Finset (Fin 3 × Fin 3)).card := Finset.card_image_le
      _ = 9 := by simp
  have hnot : ¬ (B : Set (GL (Fin 6) (ZMod 3))) ⊆ (T : Set (GL (Fin 6) (ZMod 3))) := by
    intro hsub
    have hle : Nat.card B ≤ T.card := by
      have h := Nat.card_le_card_of_injective
        (fun x : B => (⟨x.1, hsub x.2⟩ : T))
        (by intro x y hxy
            exact Subtype.ext (congrArg (fun z : T => (z : GL (Fin 6) (ZMod 3))) hxy))
      simpa [Nat.card_eq_fintype_card] using h
    rw [hcard] at hle
    omega
  obtain ⟨cv, hcvB, hcvS⟩ := Set.not_subset_iff_exists_mem_notMem.mp hnot
  exact ⟨cv, hcvB, hcvS⟩

theorem exists_third_index
    {B : Subgroup (GL (Fin 6) (ZMod 3))} (hB : B ≤ P) (hel : CFSG.Open.IsElemAbelian 3 B)
    {av bv cv : GL (Fin 6) (ZMod 3)} (hav : av ∈ B) (hbv : bv ∈ B) (hcvB : cv ∈ B)
    (hcvS : cv ∉ twoGenProducts av bv)
    {i j : Fin 81} (hi : LAt i = (av : Mat6)) (hj : LAt j = (bv : Mat6)) :
    ∃ l : Fin 81, LAt l = (cv : Mat6) ∧ ordAt l = true ∧ commAt i l = true ∧
      commAt j l = true ∧ ∀ p q : Fin 3, LAt l ≠ LAt i ^ p.val * LAt j ^ q.val := by
  classical
  have hc : check () = true := check_true
  have hcv3 : cv ^ 3 = 1 := hel.2 cv hcvB
  have hcv1 : cv ≠ 1 := by
    intro h
    apply hcvS
    rw [h]
    exact Finset.mem_image.mpr ⟨(0, 0), Finset.mem_univ _, by simp⟩
  obtain ⟨l, hl, hlord⟩ := exists_LAt_ordAt_of_mem_P (hB hcvB) hcv3 hcv1
  have hcomm_ac : av * cv = cv * av := by
    have h := hel.1.is_comm.comm (⟨av, hav⟩ : B) ⟨cv, hcvB⟩
    simpa using congrArg (fun z : B => (z : GL (Fin 6) (ZMod 3))) h
  have hcomm_bc : bv * cv = cv * bv := by
    have h := hel.1.is_comm.comm (⟨bv, hbv⟩ : B) ⟨cv, hcvB⟩
    simpa using congrArg (fun z : B => (z : GL (Fin 6) (ZMod 3))) h
  refine ⟨l, hl, hlord, ?_, ?_, ?_⟩
  · rw [check_commOK hc i l]
    simpa [hi, hl] using congrArg (fun z : GL (Fin 6) (ZMod 3) => (z : Mat6)) hcomm_ac
  · rw [check_commOK hc j l]
    simpa [hj, hl] using congrArg (fun z : GL (Fin 6) (ZMod 3) => (z : Mat6)) hcomm_bc
  · intro p q h
    apply hcvS
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_univ _, ?_⟩
    apply Units.ext
    calc ((av ^ p.val * bv ^ q.val : GL (Fin 6) (ZMod 3)) : Mat6)
        = LAt i ^ p.val * LAt j ^ q.val := by
            rw [hi, hj, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      _ = LAt l := h.symm
      _ = (cv : Mat6) := hl

theorem card_fixed_mul_card_lt_of_card_eq_three
    {B : Subgroup (GL (Fin 6) (ZMod 3))} (hB : B ≤ P) (hel : CFSG.Open.IsElemAbelian 3 B)
    (hne : B ≠ ⊥) (hcard : Nat.card B = 3) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ B, (a : Mat6) *ᵥ v = v} * Nat.card B < 3 ^ 5 := by
  have hc : check () = true := check_true
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let av : GL (Fin 6) (ZMod 3) := a
  have hav : av ∈ B := a.2
  have hav3 : av ^ 3 = 1 := hel.2 av hav
  have hav1 : av ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨i, hi, hiord⟩ := exists_LAt_ordAt_of_mem_P (hB hav) hav3 hav1
  have hfix := card_fixed_subgroup_le_fixedB1 B hav
  have hcheck := check_single hc hiord
  rw [hi] at hcheck
  calc Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ B, (a : Mat6) *ᵥ v = v} * Nat.card B
      ≤ 27 * 3 := Nat.mul_le_mul (le_trans hfix hcheck) (le_of_eq hcard)
    _ < 3 ^ 5 := by norm_num

theorem card_fixed_mul_card_lt_of_card_eq_nine
    {B : Subgroup (GL (Fin 6) (ZMod 3))} (hB : B ≤ P) (hel : CFSG.Open.IsElemAbelian 3 B)
    (hne : B ≠ ⊥) (hcard : Nat.card B = 9) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ B, (a : Mat6) *ᵥ v = v} * Nat.card B < 3 ^ 5 := by
  classical
  have hc : check () = true := check_true
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let av : GL (Fin 6) (ZMod 3) := a
  have hav : av ∈ B := a.2
  have hav3 : av ^ 3 = 1 := hel.2 av hav
  have hav1 : av ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hav_order : orderOf av = 3 := orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩) hav3 hav1
  have hz_card : Nat.card (Subgroup.zpowers av) = 3 := by
    rw [Nat.card_zpowers, hav_order]
  obtain ⟨i, hi, hiord⟩ := exists_LAt_ordAt_of_mem_P (hB hav) hav3 hav1
  have hzlt : Nat.card (Subgroup.zpowers av) < Nat.card B := by rw [hz_card, hcard]; norm_num
  obtain ⟨bv, hbvB, j, hj, hjord, hcomm, hij, hsq⟩ :=
    exists_second_index hB hel hav hzlt hi
  have hfix := card_fixed_subgroup_le_inter B hav hbvB
  have hcheck := check_pair hc hiord hjord hcomm hij hsq
  rw [hi, hj] at hcheck
  calc Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ B, (a : Mat6) *ᵥ v = v} * Nat.card B
      ≤ 9 * 9 := Nat.mul_le_mul (le_trans hfix hcheck) (le_of_eq hcard)
    _ < 3 ^ 5 := by norm_num

theorem card_fixed_mul_card_lt_of_card_eq_27
    {B : Subgroup (GL (Fin 6) (ZMod 3))} (hB : B ≤ P) (hel : CFSG.Open.IsElemAbelian 3 B)
    (hne : B ≠ ⊥) (hcard : Nat.card B = 27) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ B, (a : Mat6) *ᵥ v = v} * Nat.card B < 3 ^ 5 := by
  classical
  have hc : check () = true := check_true
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let av : GL (Fin 6) (ZMod 3) := a
  have hav : av ∈ B := a.2
  have hav3 : av ^ 3 = 1 := hel.2 av hav
  have hav1 : av ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hav_order : orderOf av = 3 := orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩) hav3 hav1
  have hz_card : Nat.card (Subgroup.zpowers av) = 3 := by
    rw [Nat.card_zpowers, hav_order]
  obtain ⟨i, hi, hiord⟩ := exists_LAt_ordAt_of_mem_P (hB hav) hav3 hav1
  have hzlt : Nat.card (Subgroup.zpowers av) < Nat.card B := by rw [hz_card, hcard]; norm_num
  obtain ⟨bv, hbvB, j, hj, hjord, hcomm, hij, hsq⟩ :=
    exists_second_index hB hel hav hzlt hi
  obtain ⟨cv, hcvB, hcvS⟩ := exists_mem_not_products hcard
  obtain ⟨l, hl, hlord, hik, hjk, hsub⟩ :=
    exists_third_index hB hel hav hbvB hcvB hcvS hi hj
  have hfix := card_fixed_subgroup_le_triple B hav hbvB hcvB
  have hcheck := check_triple hc hiord hjord hcomm hij hsq hlord hik hjk hsub
  rw [hi, hj, hl] at hcheck
  calc Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ B, (a : Mat6) *ᵥ v = v} * Nat.card B
      ≤ 3 * 27 := Nat.mul_le_mul (le_trans hfix hcheck) (le_of_eq hcard)
    _ < 3 ^ 5 := by norm_num

theorem card_fixed_mul_card_lt_of_le_P
    {B : Subgroup (GL (Fin 6) (ZMod 3))} (hB : B ≤ P) (hel : CFSG.Open.IsElemAbelian 3 B)
    (hne : B ≠ ⊥) :
    Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ B, (a : Mat6) *ᵥ v = v} * Nat.card B < 3 ^ 5 := by
  have hc : check () = true := check_true
  have hdvd : Nat.card B ∣ 81 := by
    have h := Subgroup.card_dvd_of_le hB
    rwa [P_card hc] at h
  have hdvd' : Nat.card B ∣ 3 ^ 4 := by simpa using hdvd
  obtain ⟨k, hk4, hcard⟩ := (Nat.dvd_prime_pow (p := 3) (by norm_num) (m := 4)
    (i := Nat.card B)).mp hdvd'
  interval_cases k
  · have hcard1 : Nat.card B = 1 := by simpa using hcard
    exact absurd (Subgroup.eq_bot_of_card_eq B hcard1) hne
  · exact card_fixed_mul_card_lt_of_card_eq_three hB hel hne (by simpa using hcard)
  · exact card_fixed_mul_card_lt_of_card_eq_nine hB hel hne (by simpa using hcard)
  · exact card_fixed_mul_card_lt_of_card_eq_27 hB hel hne (by simpa using hcard)
  · have hcard81 : Nat.card B = 81 := by simpa using hcard
    have hle : Nat.card P ≤ Nat.card B := by rw [P_card hc, hcard81]
    have hBP : B = P := Subgroup.eq_of_le_of_card_ge hB hle
    have hcommP : IsMulCommutative P := by rw [← hBP]; exact hel.1
    obtain ⟨u1, hu1P, hu1⟩ := exists_mem_P_of_LAt hc 1
    have hu1' : u1 = g1u := Units.ext (hu1.trans (LAt_one_eq_g1.trans g1u_val.symm))
    obtain ⟨u2, hu2P, hu2⟩ := exists_mem_P_of_LAt hc 2
    have hu2' : u2 = g2u := Units.ext (hu2.trans (LAt_two_eq_g2.trans g2u_val.symm))
    have hg1P : g1u ∈ P := hu1' ▸ hu1P
    have hg2P : g2u ∈ P := hu2' ▸ hu2P
    have hmul : g1u * g2u = g2u * g1u := by
      have h := hcommP.is_comm.comm (⟨g1u, hg1P⟩ : P) ⟨g2u, hg2P⟩
      simpa using congrArg (fun z : P => (z : GL (Fin 6) (ZMod 3))) h
    exact absurd hmul (P_noncomm hc)

theorem conj_inv_conj (g a : GL (Fin 6) (ZMod 3)) :
    MulAut.conj g⁻¹ (MulAut.conj g a) = a := by
  have h : (MulAut.conj g⁻¹ : MulAut (GL (Fin 6) (ZMod 3))) * MulAut.conj g = 1 := by
    rw [← map_mul (MulAut.conj) g⁻¹ g, inv_mul_cancel, map_one]
  calc MulAut.conj g⁻¹ (MulAut.conj g a)
      = ((MulAut.conj g⁻¹ : MulAut (GL (Fin 6) (ZMod 3))) * MulAut.conj g) a := by
          rw [MulAut.mul_apply]
    _ = (1 : MulAut (GL (Fin 6) (ZMod 3))) a := by rw [h]
    _ = a := rfl

@[expose] def rE6Neg : GL (Fin 6) (ZMod 3) :=
  ⟨rE6 (-1), rE6 (-1), by decide, by decide⟩

@[expose] def rE6One : GL (Fin 6) (ZMod 3) :=
  ⟨rE6 1, rE6 1, by decide, by decide⟩

theorem conj_dGL_rE6 : MulAut.conj wE6SignGL rE6Neg = rE6One := by
  apply Units.ext
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, dGL_inv]
  show dMat * rE6 (-1) * dMat = rE6 1
  decide +kernel

theorem conj_dGL_involutive (A : GL (Fin 6) (ZMod 3)) :
    MulAut.conj wE6SignGL (MulAut.conj wE6SignGL A) = A := by
  rw [← MulAut.mul_apply]
  rw [show MulAut.conj wE6SignGL * MulAut.conj wE6SignGL =
      MulAut.conj (wE6SignGL * wE6SignGL) from (map_mul (MulAut.conj) _ _).symm,
    wE6SignGL_mul_self, map_one]
  rfl

theorem conj_dGL_wE6_neg_one :
    (wE6 (-1)).map (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)) =
      wE6 1 := by
  rw [wE6, wE6, MonoidHom.map_closure]
  congr 1
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    rcases hB with hB | hB
    · left
      exact conj_dGL_mem_evenFix0 hB
    · right
      have hB' : B = rE6Neg := Units.ext hB
      rw [hB']
      simpa [rE6One] using
        congrArg (fun u : GL (Fin 6) (ZMod 3) => (u : Mat6)) conj_dGL_rE6
  · intro h
    rcases h with h | h
    · refine ⟨MulAut.conj wE6SignGL A, Or.inl ?_, ?_⟩
      · exact conj_dGL_mem_evenFix0 h
      · exact conj_dGL_involutive A
    · have hA' : A = rE6One := Units.ext (by simpa [rE6One] using h)
      refine ⟨rE6Neg, Or.inr rfl, ?_⟩
      rw [hA']
      exact conj_dGL_rE6

theorem wE6_one_noOffender
    (hdvd : Nat.card (wE6 1) ∣ 51840)
    {A : Subgroup (GL (Fin 6) (ZMod 3))} (hA : A ≤ wE6 1)
    (hel : CFSG.Open.IsElemAbelian 3 A) (hne : A ≠ ⊥) :
    Nat.card {v : Fin 6 → ZMod 3 // v 0 = 0 ∧
      ∀ a ∈ A, (a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} * Nat.card A < 3 ^ 5 := by
  classical
  have hc : check () = true := check_true
  obtain ⟨u, hu, hAu⟩ := exists_conj_le_P hc hdvd hA hel
  have hB : A.map (MulAut.conj u⁻¹ : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)) ≤ P := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨p, hp, hpaeq⟩ := Subgroup.mem_map.mp (hAu ha)
    rw [← hpaeq]
    change (MulAut.conj u⁻¹) ((MulAut.conj u) p) ∈ P
    rw [conj_inv_conj]
    exact hp
  have hBabel : CFSG.Open.IsElemAbelian 3
      (A.map (MulAut.conj u⁻¹ : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3))) :=
    hel.map (MulAut.conj u⁻¹ : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3))
  have hBne : A.map (MulAut.conj u⁻¹ : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)) ≠ ⊥ := by
    intro hbot
    exact hne ((Subgroup.map_eq_bot_iff_of_injective A
      (f := (MulAut.conj u⁻¹ : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)))
      (MulAut.conj u⁻¹).injective).mp hbot)
  have hAcard : Nat.card (A.map (MulAut.conj u⁻¹ : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3))) =
      Nat.card A :=
    Subgroup.card_map_of_injective
      (f := (MulAut.conj u⁻¹ : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)))
      (MulAut.conj u⁻¹).injective
  have hcard : Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ A, (a : Mat6) *ᵥ v = v} =
      Nat.card {v : Vec6 // v 0 = 0 ∧
        ∀ a ∈ A.map (MulAut.conj u⁻¹ : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)),
          ((a : GL (Fin 6) (ZMod 3)) : Mat6) *ᵥ v = v} :=
    Nat.card_congr (fixedConjEquiv u⁻¹
      (fun v hv => mulVec_zero_of_mem_wE6 ((wE6 1).inv_mem hu) hv)
      (fun v hv => mulVec_zero_of_mem_wE6 hu hv) A)
  rw [hcard, ← hAcard]
  exact card_fixed_mul_card_lt_of_le_P hB hBabel hBne

theorem wE6_noOffender {ε : ZMod 3}
    (hε : ε = 1 ∨ ε = -1) (hdvd : Nat.card (wE6 ε) ∣ 51840)
    {A : Subgroup (GL (Fin 6) (ZMod 3))} (hA : A ≤ wE6 ε)
    (hel : CFSG.Open.IsElemAbelian 3 A) (hne : A ≠ ⊥) :
    Nat.card {v : Fin 6 → ZMod 3 // v 0 = 0 ∧
      ∀ a ∈ A, (a : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = v} * Nat.card A < 3 ^ 5 := by
  classical
  rcases hε with rfl | hε
  · exact wE6_one_noOffender hdvd hA hel hne
  · subst hε
    have hcard_w : Nat.card (wE6 1) = Nat.card (wE6 (-1)) := by
      have h := Subgroup.card_map_of_injective (K := wE6 (-1))
        (f := (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)))
        (MulAut.conj wE6SignGL).injective
      rwa [conj_dGL_wE6_neg_one] at h
    have hdvd1 : Nat.card (wE6 1) ∣ 51840 := by rw [hcard_w]; exact hdvd
    have hB : A.map (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)) ≤
        wE6 1 := by
      have hmap := Subgroup.map_mono
        (f := (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3))) hA
      rwa [conj_dGL_wE6_neg_one] at hmap
    have hBabel : CFSG.Open.IsElemAbelian 3
        (A.map (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3))) :=
      hel.map (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3))
    have hBne : A.map (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)) ≠ ⊥ := by
      intro hbot
      exact hne ((Subgroup.map_eq_bot_iff_of_injective A
        (f := (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)))
        (MulAut.conj wE6SignGL).injective).mp hbot)
    have hAcard :
        Nat.card (A.map (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3))) =
        Nat.card A :=
      Subgroup.card_map_of_injective
        (f := (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)))
        (MulAut.conj wE6SignGL).injective
    have hgi : ∀ v : Vec6, v 0 = 0 → ((wE6SignGL.inv : Mat6) *ᵥ v) 0 = 0 := by
      intro v hv
      show (dMat *ᵥ v) 0 = 0
      exact dGL_mulVec_zero hv
    have hcard : Nat.card {v : Vec6 // v 0 = 0 ∧ ∀ a ∈ A, (a : Mat6) *ᵥ v = v} =
        Nat.card {v : Vec6 // v 0 = 0 ∧
          ∀ a ∈ A.map (MulAut.conj wE6SignGL : GL (Fin 6) (ZMod 3) →* GL (Fin 6) (ZMod 3)),
            ((a : GL (Fin 6) (ZMod 3)) : Mat6) *ᵥ v = v} :=
      Nat.card_congr (fixedConjEquiv wE6SignGL (fun v hv => dGL_mulVec_zero hv) hgi A)
    rw [hcard, ← hAcard]
    exact wE6_one_noOffender hdvd1 hB hBabel hBne

end CFSG.StandardType.FrameRoute.FS81

end
