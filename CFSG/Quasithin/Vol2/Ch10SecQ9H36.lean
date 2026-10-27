module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H33

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

theorem case3_of_invStd {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h3 : InvStd X 3) (hperf : ⁅X, X⁆ = X) :
    InvStd X 3 ∧ ∀ x ∈ X, ∀ v, x • v + v ∈ stdE 5 3 := by
  have hX : X ≤ stabStd 3 2 := le_stabStd_of_invStd (m := 3) (k := 2) h3
  have hbot := botH_eq_one_of_perfect (m := 3) hX hperf
  exact ⟨h3, fun x hx v =>
    smul_add_mem_of_botB_one (hX hx) (congrArg Subtype.val (hbot ⟨x, hX hx⟩ hx)) v⟩

theorem case2_of_invStd {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h2 : InvStd X 2) (hperf : ⁅X, X⁆ = X) :
    InvStd X 2 ∧ ∀ x ∈ X, ∀ v ∈ stdE 5 2, x • v = v := by
  have hX : X ≤ stabStd 2 3 := le_stabStd_of_invStd (m := 2) (k := 3) h2
  have htop := topH_eq_one_of_perfect (k := 3) hX hperf
  exact ⟨h2, fun x hx v hv =>
    smul_eq_of_topB_one (hX hx) (congrArg Subtype.val (htop ⟨x, hX hx⟩ hx)) hv⟩

theorem cases_of_flag {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h1 : InvStd X 1) (h4 : InvStd X 4)
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hperf : ⁅X, X⁆ = X) (hcard : Nat.card X = Nat.card (o2G X) * 168) :
    (InvStd X 3 ∧ ∀ x ∈ X, ∀ v, x • v + v ∈ stdE 5 3) ∨
      (InvStd X 2 ∧ ∀ x ∈ X, ∀ v ∈ stdE 5 2, x • v = v) ∨
      (InvStd X 1 ∧ InvStd X 4 ∧ fixN X = stdE 5 1) := by
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
  · exact Or.inr (Or.inr ⟨h1, h4, by rw [hcE, h]⟩)
  · exact Or.inr (Or.inl (case2_of_invStd (hfixE 2 h.symm) hperf))
  · exact Or.inl (case3_of_invStd (hfixE 3 h.symm) hperf)
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

theorem invStd_cases {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hperf : ⁅X, X⁆ = X)
    (hq : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    (InvStd X 3 ∧ ∀ x ∈ X, ∀ v, x • v + v ∈ stdE 5 3) ∨
      (InvStd X 2 ∧ ∀ x ∈ X, ∀ v ∈ stdE 5 2, x • v = v) ∨
      (InvStd X 1 ∧ InvStd X 4 ∧ fixN X = stdE 5 1) := by
  obtain ⟨e⟩ := hq
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
    · exact Or.inr (Or.inl (case2_of_invStd hinv hperf))
    · exact Or.inl (case3_of_invStd hinv hperf)
    · exact cases_of_flag hM hinv hU hperf hcard
  · exact Or.inr (Or.inl (case2_of_invStd hM hperf))
  · exact Or.inl (case3_of_invStd hM hperf)
  · obtain ⟨m', hm1, hm4, hinv⟩ := invStd_of_invStd_four hM hU e
    interval_cases m'
    · exact cases_of_flag hinv hM hU hperf hcard
    · exact Or.inr (Or.inl (case2_of_invStd hinv hperf))
    · exact Or.inl (case3_of_invStd hinv hperf)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
