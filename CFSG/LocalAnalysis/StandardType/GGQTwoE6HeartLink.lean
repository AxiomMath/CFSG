module

public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartDefs

public section

namespace CFSG.StandardType.E6Heart

@[expose] def ofList (y : List ℕ) : Fin 6 → ZMod 3 := fun i => ((y.getD i 0 : ℕ) : ZMod 3)

@[expose] def yOf (t : ℕ) : H :=
  Submodule.Quotient.mk (ofList (Certificates.E6Heart.repL t))

private theorem ggE6d_C_symm (i j : Fin 6) : C i j = C j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem ggE6d_cEntry_eq (i j : Fin 6) :
    Certificates.E6Heart.cEntry i j = C i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem ggE6d_foldl_idx6 (g : Nat → ℤ) :
    List.foldl (fun s i => s + g i) 0 Certificates.E6Heart.idx6 = ∑ i : Fin 6, g i := by
  simp [Certificates.E6Heart.idx6, List.foldl, Fin.sum_univ_six]

private theorem ggE6d_pairZ_sum (a b : List ℤ) :
    Certificates.E6Heart.pairZ a b =
      ∑ i : Fin 6, ∑ j : Fin 6,
        a.getD i 0 * Certificates.E6Heart.cEntry i j * b.getD j 0 := by
  unfold Certificates.E6Heart.pairZ
  rw [ggE6d_foldl_idx6 (fun i => List.foldl (fun t j =>
        t + a.getD i 0 * Certificates.E6Heart.cEntry i j * b.getD j 0) 0
          Certificates.E6Heart.idx6)]
  apply Finset.sum_congr rfl; intro i _
  rw [ggE6d_foldl_idx6 (fun j => a.getD i 0 * Certificates.E6Heart.cEntry i j * b.getD j 0)]

private theorem ggE6d_m3_cast (z : ℤ) :
    ((Certificates.E6Heart.m3 z : ℕ) : ZMod 3) = (z : ZMod 3) := by
  unfold Certificates.E6Heart.m3
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg z (by norm_num : (3:ℤ) ≠ 0))]
  exact ZMod.intCast_mod z 3

private theorem ggE6d_toVec_map (y : List ℕ) (n : ℕ) :
    (y.map (fun u : ℕ => (u : ℤ))).getD n 0 = ((y.getD n 0 : ℕ) : ℤ) := by
  induction y generalizing n with
  | nil => simp [List.getD]
  | cons a as ih =>
    cases n with
    | zero => simp [List.getD]
    | succ n =>
      rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_map]
      exact Option.getD_map (α := ℕ) (β := ℤ) (fun u : ℕ => (u : ℤ)) 0 (as[n]?)

private theorem ggE6d_toVec_map_cast (y : List ℕ) (i : Fin 6) :
    ((toVec (y.map (fun u : ℕ => (u : ℤ))) i : ℤ) : ZMod 3) = ofList y i := by
  simp only [toVec, ofList]
  rw [ggE6d_toVec_map, Int.cast_natCast]

private theorem ggE6d_ipair_cast (u v : Fin 6 → ℤ) :
    ((ipair u v : ℤ) : ZMod 3) =
      ∑ i, ∑ j, (u i : ZMod 3) * (C i j : ZMod 3) * (v j : ZMod 3) := by
  unfold ipair
  push_cast
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem C_symm (i j : Fin 6) : C i j = C j i :=
  ggE6d_C_symm i j

theorem ipair_comm (a b : Fin 6 → ℤ) : ipair a b = ipair b a := by
  unfold ipair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [ggE6d_C_symm j i]
  ring

theorem pairZ_eq (a b : List ℤ) (ha : a.length = 6) (hb : b.length = 6) :
    Certificates.E6Heart.pairZ a b = ipair (toVec a) (toVec b) := by
  rw [ggE6d_pairZ_sum]
  unfold ipair toVec
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [ggE6d_cEntry_eq i j]

theorem pair3_eq (a : List ℤ) (y : List ℕ) (ha : a.length = 6) (hy : y.length = 6) :
    ((Certificates.E6Heart.pair3 a y : ℕ) : ZMod 3) = pair (toVec a) (ofList y) := by
  have hb : (y.map (fun u : ℕ => (u : ℤ))).length = 6 := by
    rw [List.length_map]; exact hy
  rw [Certificates.E6Heart.pair3, ggE6d_m3_cast]
  rw [show Certificates.E6Heart.pairZ a (y.map (fun u : ℕ => (u : ℤ))) =
      ipair (toVec a) (toVec (y.map (fun u : ℕ => (u : ℤ)))) from
    pairZ_eq a (y.map (fun u : ℕ => (u : ℤ))) ha hb]
  rw [ggE6d_ipair_cast]
  unfold pair
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [show (toVec (y.map (fun u : ℕ => (u : ℤ))) j : ZMod 3) = ofList y j from
    ggE6d_toVec_map_cast y j]

theorem qOf_eq (y : List ℕ) (hy : y.length = 6) :
    ((Certificates.E6Heart.qOf y : ℕ) : ZMod 3) = Q (ofList y) := by
  have hy' : (y.map (fun u : ℕ => (u : ℤ))).length = 6 := by
    rw [List.length_map]; exact hy
  rw [Certificates.E6Heart.qOf, ggE6d_m3_cast]
  rw [show Certificates.E6Heart.pairZ (y.map (fun u : ℕ => (u : ℤ)))
        (y.map (fun u : ℕ => (u : ℤ))) =
      ipair (toVec (y.map (fun u : ℕ => (u : ℤ))))
        (toVec (y.map (fun u : ℕ => (u : ℤ)))) from
    pairZ_eq _ _ hy' hy']
  rw [ggE6d_ipair_cast]
  unfold Q
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [ggE6d_toVec_map_cast y i, ggE6d_toVec_map_cast y j]

theorem alpha_mk (a : Fin 6 → ℤ) (v : Fin 6 → ZMod 3) :
    alpha a (Submodule.Quotient.mk v) = pair a v := by
  rw [alpha, Submodule.liftQ_apply]
  rfl

theorem Qh_mk (v : Fin 6 → ZMod 3) : Qh (Submodule.Quotient.mk v) = Q v := by
  rw [Qh]
  rfl

end CFSG.StandardType.E6Heart

end
