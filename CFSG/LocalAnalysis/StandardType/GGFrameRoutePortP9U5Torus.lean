module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U7
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType.LineU

variable {F : Type} [Field F] {m : ℕ}

namespace P9U5

private lemma p9u5a_units_card (hF : Nat.card F = 4) : Nat.card Fˣ = 3 := by
  rw [Nat.card_units, hF]

private lemma p9u5a_units_cube (hF : Nat.card F = 4) (x : Fˣ) : x ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := x)
  rwa [p9u5a_units_card hF] at h

private lemma p9u5a_units_cube_val (hF : Nat.card F = 4) (x : Fˣ) : (x : F) ^ 3 = 1 := by
  have h := congrArg (fun y : Fˣ => (y : F)) (p9u5a_units_cube hF x)
  rwa [Units.val_pow_eq_pow_val, Units.val_one] at h

private def p9u5a_tup (n : ℕ) (s : Fin n → Fˣ) : Fin (n + 3) → Fˣ :=
  fun j =>
    if h : j.val < n then s ⟨j.val, h⟩
    else if j.val = n then ∏ i, s i
    else if j.val = n + 1 then ∏ i, s i
    else 1

private lemma p9u5a_tup_mid (n : ℕ) (s : Fin n → Fˣ) (k : Fin n) :
    p9u5a_tup n s ⟨k.val, by omega⟩ = s k := by
  unfold p9u5a_tup
  rw [dif_pos k.2]

private lemma p9u5a_tup_P (n : ℕ) (s : Fin n → Fˣ) :
    p9u5a_tup n s ⟨n, by omega⟩ = ∏ i, s i := by
  unfold p9u5a_tup
  simp only [Fin.val_mk]
  rw [dif_neg (by omega : ¬ (n < n))]
  simp

private lemma p9u5a_tup_P' (n : ℕ) (s : Fin n → Fˣ) :
    p9u5a_tup n s ⟨n + 1, by omega⟩ = ∏ i, s i := by
  unfold p9u5a_tup
  simp only [Fin.val_mk]
  rw [dif_neg (by omega : ¬ (n + 1 < n)), if_neg (by omega : ¬ (n + 1 = n))]
  simp

private lemma p9u5a_tup_last (n : ℕ) (s : Fin n → Fˣ) :
    p9u5a_tup n s ⟨n + 2, by omega⟩ = 1 := by
  unfold p9u5a_tup
  simp only [Fin.val_mk]
  rw [dif_neg (by omega : ¬ (n + 2 < n)), if_neg (by omega : ¬ (n + 2 = n)),
    if_neg (by omega : ¬ (n + 2 = n + 1))]

private lemma p9u5a_tup_prod (hF : Nat.card F = 4) (n : ℕ) (s : Fin n → Fˣ) :
    ∏ j : Fin (n + 3), p9u5a_tup n s j = 1 := by
  rw [Fin.prod_univ_add, Fin.prod_univ_three]
  have hleft : ∏ i : Fin n, p9u5a_tup n s (Fin.castAdd 3 i) = ∏ i : Fin n, s i :=
    Finset.prod_congr rfl (fun i _ => p9u5a_tup_mid n s i)
  have h0 : p9u5a_tup n s (Fin.natAdd n 0) = ∏ i, s i := p9u5a_tup_P n s
  have h1 : p9u5a_tup n s (Fin.natAdd n 1) = ∏ i, s i := p9u5a_tup_P' n s
  have h2 : p9u5a_tup n s (Fin.natAdd n 2) = 1 := p9u5a_tup_last n s
  rw [hleft, h0, h1, h2, mul_one, ← pow_three]
  exact p9u5a_units_cube hF (∏ i : Fin n, s i)

private def p9u5a_tupM (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) : Fin m → Fˣ :=
  fun j => p9u5a_tup (m - 3) s (Fin.cast (by omega : m = (m - 3) + 3) j)

private def p9u5a_i0 (hm : 3 ≤ m) : Fin m := ⟨m - 3, by omega⟩

private def p9u5a_i1 (hm : 3 ≤ m) : Fin m := ⟨m - 3 + 1, by omega⟩

private def p9u5a_ilast (hm : 3 ≤ m) : Fin m := ⟨m - 3 + 2, by omega⟩

private lemma p9u5a_tupM_mid (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) (k : Fin (m - 3)) :
    p9u5a_tupM hm s ⟨k.val, by omega⟩ = s k :=
  p9u5a_tup_mid (m - 3) s k

private lemma p9u5a_tupM_i0 (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    p9u5a_tupM hm s (p9u5a_i0 hm) = ∏ i, s i :=
  p9u5a_tup_P (m - 3) s

private lemma p9u5a_tupM_i1 (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    p9u5a_tupM hm s (p9u5a_i1 hm) = ∏ i, s i :=
  p9u5a_tup_P' (m - 3) s

private lemma p9u5a_tupM_last (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    p9u5a_tupM hm s (p9u5a_ilast hm) = 1 :=
  p9u5a_tup_last (m - 3) s

private lemma p9u5a_tupM_prod (hF : Nat.card F = 4) (hm : 3 ≤ m)
    (s : Fin (m - 3) → Fˣ) : ∏ j : Fin m, p9u5a_tupM hm s j = 1 := by
  have hcast : m = (m - 3) + 3 := by omega
  have hcomp : p9u5a_tupM hm s = fun j => p9u5a_tup (m - 3) s (Fin.cast hcast j) := rfl
  have hcomp2 : (fun j : Fin m => p9u5a_tup (m - 3) s (Fin.cast hcast j)) =
      fun j => p9u5a_tup (m - 3) s ((Fin.castOrderIso hcast).toEquiv j) := rfl
  rw [hcomp, hcomp2,
    Equiv.prod_comp (Fin.castOrderIso hcast).toEquiv (p9u5a_tup (m - 3) s)]
  exact p9u5a_tup_prod hF (m - 3) s

private lemma p9u5a_tupM_cube (hF : Nat.card F = 4) (hm : 3 ≤ m)
    (s : Fin (m - 3) → Fˣ) (j : Fin m) : (p9u5a_tupM hm s j : F) ^ 3 = 1 :=
  p9u5a_units_cube_val hF _

private lemma p9u5a_tupM_prod_val (hF : Nat.card F = 4) (hm : 3 ≤ m)
    (s : Fin (m - 3) → Fˣ) : ∏ j : Fin m, (p9u5a_tupM hm s j : F) = 1 := by
  rw [← Units.coe_prod, p9u5a_tupM_prod hF hm s, Units.val_one]

private lemma p9u5a_diagHom_mem (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    CFSG.SectionRank.OddCover.diagHom m (p9u5a_tupM hm s) ∈ unitarySU 2 1 F m := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [CFSG.SectionRank.OddCover.det_diagHom]
    exact p9u5a_tupM_prod_val hF hm s
  · exact CFSG.RankThree.Classical2.diagHom_unitary h
      (fun i => by simpa using p9u5a_tupM_cube hF hm s i)

private lemma p9u5a_tupM_mul (hm : 3 ≤ m) (s t : Fin (m - 3) → Fˣ) :
    p9u5a_tupM hm s * p9u5a_tupM hm t = p9u5a_tupM hm (s * t) := by
  funext j
  simp only [p9u5a_tupM, p9u5a_tup, Fin.val_cast, Pi.mul_apply, Finset.prod_mul_distrib]
  split_ifs <;> simp

private lemma p9u5a_tupM_one (hm : 3 ≤ m) : p9u5a_tupM (F := F) hm 1 = 1 := by
  funext j
  simp only [p9u5a_tupM, p9u5a_tup, Fin.val_cast, Pi.one_apply]
  split_ifs <;> simp

private def p9u5a_tupHom (hm : 3 ≤ m) : (Fin (m - 3) → Fˣ) →* (Fin m → Fˣ) where
  toFun := p9u5a_tupM hm
  map_one' := p9u5a_tupM_one hm
  map_mul' s t := (p9u5a_tupM_mul hm s t).symm

noncomputable def torus (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4) (hm : 3 ≤ m) :
    (Fin (m - 3) → Fˣ) →* ↥(unitarySU 2 1 F m) :=
  ((CFSG.SectionRank.OddCover.diagHom m).comp (p9u5a_tupHom hm)).codRestrict
    (unitarySU 2 1 F m) (p9u5a_diagHom_mem h hF hm)

private lemma p9u5a_torus_val (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    ((torus h hF hm s : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) =
      CFSG.SectionRank.OddCover.diagHom m (p9u5a_tupM hm s) := rfl

private lemma p9u5a_torus_matrix (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    (((torus h hF hm s : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = diagonal (fun i => (p9u5a_tupM hm s i : F)) := by
  rw [p9u5a_torus_val]
  exact CFSG.SectionRank.OddCover.coe_diagHom (p9u5a_tupM hm s)

theorem torus_pow_three (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4) (hm : 3 ≤ m)
    (s : Fin (m - 3) → Fˣ) : torus h hF hm s ^ 3 = 1 := by
  refine pow_eq_one_of_diagSU (n := 1) (p := 3) (p9u5a_torus_matrix h hF hm s) (fun i => ?_)
  exact p9u5a_tupM_cube hF hm s i

theorem torus_eq_one_of_scalar (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) {c : F}
    (hc : (((torus h hF hm s : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)) : s = 1 := by
  rw [p9u5a_torus_matrix] at hc
  have hlast := congrFun (congrFun hc (p9u5a_ilast hm)) (p9u5a_ilast hm)
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, p9u5a_tupM_last hm] at hlast
  have hc1 : c = 1 := by simpa using hlast.symm
  funext k
  have hk := congrFun (congrFun hc ⟨k.val, by omega⟩) ⟨k.val, by omega⟩
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, p9u5a_tupM_mid, hc1] at hk
  exact Units.ext hk

private lemma p9u5a_tupM_swap (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    (fun j => p9u5a_tupM hm s (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm) j)) =
      p9u5a_tupM hm s := by
  classical
  funext j
  by_cases hj0 : j = p9u5a_i0 hm
  · subst hj0
    rw [Equiv.swap_apply_left, p9u5a_tupM_i0, p9u5a_tupM_i1]
  · by_cases hj1 : j = p9u5a_i1 hm
    · subst hj1
      rw [Equiv.swap_apply_right, p9u5a_tupM_i1, p9u5a_tupM_i0]
    · rw [Equiv.swap_apply_of_ne_of_ne hj0 hj1]

private lemma p9u5a_permMatrix_conj (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm)).permMatrix F *
        diagonal (fun i => (p9u5a_tupM hm s i : F)) *
        (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm)).permMatrix F =
      diagonal (fun i => (p9u5a_tupM hm s i : F)) := by
  classical
  have h := CFSG.StandardType.TypeANbrDvd.permMatrix_mul_diagonal_mul_inv
    (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm)) (fun i => (p9u5a_tupM hm s i : F))
  rw [Equiv.swap_inv] at h
  rw [h]
  congr 1
  funext i
  exact congrArg (fun y : Fˣ => (y : F)) (congrFun (p9u5a_tupM_swap hm s) i)

private noncomputable def p9u5a_swapGL (hm : 3 ≤ m) : GL (Fin m) F :=
  CFSG.RankThree.Classical.permGL (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm))

private lemma p9u5a_swapGL_matrix (hm : 3 ≤ m) :
    ((p9u5a_swapGL (F := F) hm : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm)).permMatrix F := by
  rw [p9u5a_swapGL, coe_permGL_matrix, Equiv.swap_inv]

private lemma p9u5a_swapGL_mul_self (hm : 3 ≤ m) :
    p9u5a_swapGL (F := F) hm * p9u5a_swapGL (F := F) hm = 1 := by
  have h := (CFSG.RankThree.Classical.permGL (ι := Fin m) (K := F)).map_mul
    (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm)) (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm))
  rw [Equiv.swap_mul_self] at h
  rw [p9u5a_swapGL, ← h, (CFSG.RankThree.Classical.permGL (ι := Fin m) (K := F)).map_one]

noncomputable def swap (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m) :
    ↥(unitarySU 2 1 F m) :=
  permSU h (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm))

private lemma p9u5a_swap_val (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m) :
    ((swap h hm : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) =
      p9u5a_swapGL (F := F) hm := rfl

theorem swap_mul_self (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m) :
    swap h hm * swap h hm = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, p9u5a_swap_val, p9u5a_swapGL_mul_self]

private lemma p9u5a_permMatrix_apply (π : Equiv.Perm (Fin m)) (a b : Fin m) :
    π.permMatrix F a b = if π a = b then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem swap_not_scalar (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m) :
    ¬ ∃ c : F, (((swap h hm : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c) := by
  rintro ⟨c, hc⟩
  have hmat : ((swap h hm : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm)).permMatrix F := by
    rw [p9u5a_swap_val, p9u5a_swapGL_matrix]
  have h2 : (Equiv.swap (p9u5a_i0 hm) (p9u5a_i1 hm)).permMatrix F =
      diagonal (fun _ => c) := by
    rw [← hmat]
    exact hc
  have hij : p9u5a_i0 hm ≠ p9u5a_i1 hm := by
    intro h'
    have h'' : m - 3 = m - 3 + 1 := congrArg Fin.val h'
    omega
  have hentry := congrFun (congrFun h2 (p9u5a_i0 hm)) (p9u5a_i1 hm)
  rw [p9u5a_permMatrix_apply, if_pos (Equiv.swap_apply_left _ _),
    Matrix.diagonal_apply_ne _ hij] at hentry
  exact one_ne_zero hentry

private lemma p9u5a_torus_comm_swapGL (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) (s : Fin (m - 3) → Fˣ) :
    (torus h hF hm s : GL (Fin m) F) * p9u5a_swapGL hm =
      p9u5a_swapGL hm * (torus h hF hm s : GL (Fin m) F) := by
  have hσ2 := p9u5a_swapGL_mul_self (F := F) hm
  have hconj : p9u5a_swapGL hm * (torus h hF hm s : GL (Fin m) F) * p9u5a_swapGL hm =
      (torus h hF hm s : GL (Fin m) F) := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [p9u5a_torus_matrix, p9u5a_swapGL_matrix]
    exact p9u5a_permMatrix_conj hm s
  calc (torus h hF hm s : GL (Fin m) F) * p9u5a_swapGL hm
      = (p9u5a_swapGL hm * p9u5a_swapGL hm) * (torus h hF hm s : GL _ F) *
          p9u5a_swapGL hm := by rw [hσ2, one_mul]
    _ = p9u5a_swapGL hm * (p9u5a_swapGL hm * (torus h hF hm s : GL _ F) *
          p9u5a_swapGL hm) := by group
    _ = p9u5a_swapGL hm * (torus h hF hm s : GL _ F) := by rw [hconj]

theorem torus_comm_swap (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4) (hm : 3 ≤ m)
    (s : Fin (m - 3) → Fˣ) :
    torus h hF hm s * swap h hm = swap h hm * torus h hF hm s := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact p9u5a_torus_comm_swapGL h hF hm s

end P9U5

end CFSG.StandardType.FrameRoute

end
