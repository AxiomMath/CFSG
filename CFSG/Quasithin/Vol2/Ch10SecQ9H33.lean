module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H32
public import CFSG.Quasithin.Vol2.Ch10SecQ9H29
public import CFSG.Quasithin.Vol2.Ch10SecQ9H31

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n m k : ℕ}

theorem fixN_eq_stdE {X : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))}
    (hU : uniSL n ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))) :
    ∃ c ≤ n, fixN X = stdE n c :=
  eq_stdE_of_invariant fun i j h w hw =>
    smul_mem_fixN (hU (trvE_mem_uniSL i j (by rw [Fin.lt_def]; omega))) hw

theorem topB_eq_one_of_fix {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hg : ∀ j : Fin m, g • Pi.single (Fin.castAdd k j) (1 : ZMod 2) =
      (Pi.single (Fin.castAdd k j) 1 : Fin (m + k) → ZMod 2)) :
    topB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := by
  ext a c
  have h := congrFun (hg c) (Fin.castAdd k a)
  rw [smul_eq_mulVec', mulVec_single_one] at h
  have h' : (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) (Fin.castAdd k a) (Fin.castAdd k c) =
      (Pi.single (Fin.castAdd k c) (1 : ZMod 2) : Fin (m + k) → ZMod 2) (Fin.castAdd k a) := h
  rw [topB, submatrix_apply, Matrix.one_apply, h']
  simp [Pi.single_apply, Fin.castAdd_inj]

theorem concl_of_flag14 {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h1 : InvStd X 1) (h4 : InvStd X 4)
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hperf : ⁅X, X⁆ = X) (hcard : Nat.card X = Nat.card (o2G X) * 168)
    {y : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)}
    (hyN : y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hy3 : orderOf y = 3) (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ o2G X) :
    ∃ r ∈ uniSL 5, ∃ k : ℕ, (r * y * r⁻¹ * y) ^ 2 ^ k = 1 := by
  obtain ⟨c, -, hcE⟩ := fixN_eq_stdE hU
  have hX1 : X ≤ stabStd 1 4 := le_stabStd_of_invStd (m := 1) (k := 4) h1
  have hfixE : ∀ M, M = c → InvStd X M := fun M hM x hx v hv => by
    rw [hM, ← hcE] at hv ⊢
    rw [hv x hx]
    exact hv
  have he0 : Pi.single (Fin.castAdd 4 (0 : Fin 1)) (1 : ZMod 2) ∈ fixN X := fun x hx =>
    smul_eq_of_topB_one (hX1 hx) (topB_eq_one_of_one ⟨x, hX1 hx⟩) (castAdd_mem_stdE 0)
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ 4 ≤ c) with h | h | h | h | h
  · rw [hcE, h] at he0
    have := he0 (Fin.castAdd 4 0) (Nat.zero_le _)
    simp at this
  · exact (false_of_flag14 h1 h4 (fun v hv => by rw [hcE, h] at hv; exact hv) hcard hyN hy3
      hyc).elim
  · exact concl_of_inv23 (Or.inl (hfixE 2 h.symm)) hperf hcard hyN hy3 hyc
  · exact concl_of_inv23 (Or.inr (hfixE 3 h.symm)) hperf hcard hyN hy3 hyc
  ·
    exfalso
    have hX4 : X ≤ stabStd 4 1 := le_stabStd_of_invStd (m := 4) (k := 1) h4
    have hsq : ∀ x ∈ X, x * x = 1 := fun x hx =>
      sq_eq_one_of_blocks (hX4 hx) (topB_eq_one_of_fix fun j => by
        have hj : Pi.single (Fin.castAdd 1 j) (1 : ZMod 2) ∈ fixN X := by
          rw [hcE]
          exact stdE_mono h (castAdd_mem_stdE (k := 1) j)
        exact hj x hx) (botB_eq_one_of_one ⟨x, hX4 hx⟩)
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3
      (by rw [hcard]; exact Dvd.dvd.mul_left (by norm_num) _)
    have h2 : orderOf (x : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq x.1 x.2)
    rw [Subgroup.orderOf_coe, hx] at h2
    omega

theorem concl_of_uniSL {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hperf : ⁅X, X⁆ = X) (e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {y : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)}
    (hyN : y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hy3 : orderOf y = 3) (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ o2G X) :
    ∃ r ∈ uniSL 5, ∃ k : ℕ, (r * y * r⁻¹ * y) ^ 2 ^ k = 1 := by
  have hcard := card_eq_o2G_mul X e
  have hφ : ∀ x : ↥X, X.subtype x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx =>
    ⟨0, by rw [pow_zero, pow_one]; exact Subtype.ext hx⟩
  have hrange : X.subtype.range = X := Subgroup.range_subtype X
  obtain ⟨A, hAp, hA1, hXA, hUA⟩ := exists_twoSubgroup e X.subtype hφ isPGroup_uniSL_five
    (by rw [card_uniSL_five]; norm_num) (by rw [hrange]; exact hU) (le_normalizer_o2G_of hU)
  rw [hrange] at hXA
  obtain ⟨M, hM1, hM5, hM⟩ := exists_invStd (by norm_num) hAp hA1 hXA fun i j h =>
    hUA (trvE_mem_uniSL i j (by rw [Fin.lt_def]; omega))
  interval_cases M
  · obtain ⟨m', hm1, hm4, hinv⟩ := invStd_of_invStd_one hM hU e
    interval_cases m'
    · exact concl_of_inv23 (Or.inl hinv) hperf hcard hyN hy3 hyc
    · exact concl_of_inv23 (Or.inr hinv) hperf hcard hyN hy3 hyc
    · exact concl_of_flag14 hM hinv hU hperf hcard hyN hy3 hyc
  · exact concl_of_inv23 (Or.inl hM) hperf hcard hyN hy3 hyc
  · exact concl_of_inv23 (Or.inr hM) hperf hcard hyN hy3 hyc
  · obtain ⟨m', hm1, hm4, hinv⟩ := invStd_of_invStd_four hM hU e
    interval_cases m'
    · exact concl_of_flag14 hinv hM hU hperf hcard hyN hy3 hyc
    · exact concl_of_inv23 (Or.inl hinv) hperf hcard hyN hy3 hyc
    · exact concl_of_inv23 (Or.inr hinv) hperf hcard hyN hy3 hyc

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
