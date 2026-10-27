module

public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] def Adm1111 (p L H : Submodule K (Fin 4 → K)) : Prop :=
  p ⊓ Vsub 4 3 = ⊥ ∧ L ⊓ Vsub 4 2 = ⊥ ∧ H ⊓ Vsub 4 1 = ⊥

private theorem plh_mem_farSet_a3_1111_iff (x : FlagK K 4) :
    x ∈ farSet 4 [0, 1, 2, 3, 4] ↔
      x.E 1 ⊓ Vsub 4 3 = ⊥ ∧ x.E 2 ⊓ Vsub 4 2 = ⊥ ∧ x.E 3 ⊓ Vsub 4 1 = ⊥ := by
  have hd : ∀ i, i < ([0, 1, 2, 3, 4] : List ℕ).length →
      ([0, 1, 2, 3, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi5 : i < 5 := by simpa using hi
    interval_cases i <;> decide
  rw [mem_farSet_iff (K := K) (n := 4) (d := [0, 1, 2, 3, 4]) hd]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have h' := (h 3 (by decide) 1 (by decide)).1 (by decide)
      simpa using h'
    · have h' := (h 2 (by decide) 2 (by decide)).1 (by decide)
      simpa using h'
    · have h' := (h 1 (by decide) 3 (by decide)).1 (by decide)
      simpa using h'
  · rintro ⟨h1, h2, h3⟩
    intro i hi j hj
    have hi5 : i < 5 := by simpa using hi
    interval_cases i
    · constructor
      · intro _
        rw [show ([0, 1, 2, 3, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, inf_bot_eq]
      · intro hge
        have hj4 : j = 4 := by
          have : 4 ≤ j := by simpa using hge
          omega
        subst hj4
        rw [show ([0, 1, 2, 3, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, sup_bot_eq]
        exact x.top 4 le_rfl
    · constructor
      · intro hjc
        have hj3 : j ≤ 3 := by
          have : j + 1 ≤ 4 := by simpa using hjc
          omega
        exact le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 1) (x.mono hj3)).trans
          (le_of_eq h3))
      · intro hge
        have hj3 : 3 ≤ j := by
          have : 4 ≤ j + 1 := by simpa using hge
          omega
        have hsup : x.E 3 ⊔ Vsub (K := K) 4 1 = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [Module.finrank_fin_fun]
          have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 3)
            (Vsub (K := K) 4 1)
          rw [h3, finrank_bot, add_zero, FlagK.finrank_E_three,
            finrank_Vsub (K := K) (n := 4) (c := 1) (by norm_num)] at hsum
          omega
        exact top_le_iff.mp (hsup ▸ sup_le_sup (x.mono hj3) le_rfl)
    · constructor
      · intro hjc
        have hj2 : j ≤ 2 := by
          have : j + 2 ≤ 4 := by simpa using hjc
          omega
        exact le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 2) (x.mono hj2)).trans
          (le_of_eq h2))
      · intro hge
        have hj2 : 2 ≤ j := by
          have : 4 ≤ j + 2 := by simpa using hge
          omega
        have hsup : x.E 2 ⊔ Vsub (K := K) 4 2 = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [Module.finrank_fin_fun]
          have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 2)
            (Vsub (K := K) 4 2)
          rw [h2, finrank_bot, add_zero, FlagK.finrank_E_two,
            finrank_Vsub (K := K) (n := 4) (c := 2) (by norm_num)] at hsum
          omega
        exact top_le_iff.mp (hsup ▸ sup_le_sup (x.mono hj2) le_rfl)
    · constructor
      · intro hjc
        have hj1 : j ≤ 1 := by
          have : j + 3 ≤ 4 := by simpa using hjc
          omega
        exact le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 3) (x.mono hj1)).trans
          (le_of_eq h1))
      · intro hge
        have hj1 : 1 ≤ j := by
          have : 4 ≤ j + 3 := by simpa using hge
          omega
        have hsup : x.E 1 ⊔ Vsub (K := K) 4 3 = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [Module.finrank_fin_fun]
          have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 1)
            (Vsub (K := K) 4 3)
          rw [h1, finrank_bot, add_zero, FlagK.finrank_E_one,
            finrank_Vsub (K := K) (n := 4) (c := 3) (by norm_num)] at hsum
          omega
        exact top_le_iff.mp (hsup ▸ sup_le_sup (x.mono hj1) le_rfl)
    · constructor
      · intro hjc
        have hj0 : j = 0 := by
          have : j + 4 ≤ 4 := by simpa using hjc
          omega
        subst hj0
        rw [show ([0, 1, 2, 3, 4] : List ℕ).getD 4 0 = 4 from rfl, Vsub_self, inf_top_eq]
        exact FlagK.E_zero x
      · intro _
        rw [show ([0, 1, 2, 3, 4] : List ℕ).getD 4 0 = 4 from rfl, Vsub_self, sup_top_eq]

private theorem plh_Vsub_le_sgS_Vsub {c c' : ℕ} (h : c ≤ c') :
    Vsub (K := K) 4 c ≤ sgS K f 4 (Vsub (K := K) 4 c') := by
  intro v hv
  rw [sgS, Submodule.mem_comap]
  intro j hj
  have hvj : v j = 0 := hv j (by omega)
  simp [sgv, hvj]

private theorem plh_inf_Vsub_sgS_Vsub (c : ℕ) :
    Vsub (K := K) 4 (c + 1) ⊓ sgS K f 4 (Vsub (K := K) 4 c) = Vsub (K := K) 4 c := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [sgS, Submodule.mem_comap] at hv2
    intro j hj
    by_cases hjc : j.val = c
    · have h0 : sg K f (v j) = 0 := hv2 j (le_of_eq hjc.symm)
      exact (sg K f).injective (by rw [h0, map_zero])
    · have hjc' : c + 1 ≤ j.val := by omega
      exact hv1 j hjc'
  · intro v hv
    rw [Submodule.mem_inf]
    exact ⟨Vsub_mono (K := K) (by omega) hv, plh_Vsub_le_sgS_Vsub (K := K) (f := f) le_rfl hv⟩

theorem genSet_a3_1111_eq :
    genSet K f 4 [0, 1, 2, 3, 4] [] = admSet (Adm1111 (K := K)) := by
  ext x
  simp only [genSet, Set.mem_setOf_eq, admSet, Adm1111]
  have hfar_iff := plh_mem_farSet_a3_1111_iff (K := K) x
  constructor
  · rintro ⟨hfar, _⟩
    exact hfar_iff.mp hfar
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hfar_iff.mpr ⟨h1, h2, h3⟩, ?_⟩
    intro i hi
    have hd : ∀ i, i < ([0, 1, 2, 3, 4] : List ℕ).length →
        ([0, 1, 2, 3, 4] : List ℕ).getD i 0 ≤ 4 := by
      intro k hk
      have hk5 : k < 5 := by simpa using hk
      interval_cases k <;> decide
    have hmono : ∀ i, i + 1 < ([0, 1, 2, 3, 4] : List ℕ).length →
        ([0, 1, 2, 3, 4] : List ℕ).getD i 0 ≤
          ([0, 1, 2, 3, 4] : List ℕ).getD (i + 1) 0 := by
      intro k hk
      have hk4 : k < 4 := by
        have : k + 1 < 5 := by simpa using hk
        omega
      interval_cases k <;> decide
    have hfar := hfar_iff.mpr ⟨h1, h2, h3⟩
    have h1i : ([0, 1, 2, 3, 4] : List ℕ).getD (i + 1) 0 =
        ([0, 1, 2, 3, 4] : List ℕ).getD i 0 + 1 := by
      have hi4 : i < 4 := by
        have : i + 1 < 5 := by simpa using hi
        omega
      interval_cases i <;> decide
    rw [blockOK]
    intro r hr
    simp only [List.getD_nil, Bool.false_eq_true, ↓reduceIte]
    have hr1 : r ≤ 1 := by
      have hsub : ([0, 1, 2, 3, 4] : List ℕ).getD (i + 1) 0 -
          ([0, 1, 2, 3, 4] : List ℕ).getD i 0 = 1 := by omega
      omega
    have hr01 : r = 0 ∨ r = 1 := by omega
    rcases hr01 with rfl | rfl
    · rw [Nat.sub_zero]
      rw [blockU_zero (K := K) hd hmono hfar hi]
      rw [blockU_last (K := K) hd hmono hfar hi, h1i]
      exact inf_eq_left.mpr (plh_Vsub_le_sgS_Vsub (K := K) (f := f)
        (c := ([0, 1, 2, 3, 4] : List ℕ).getD i 0)
        (c' := ([0, 1, 2, 3, 4] : List ℕ).getD i 0 + 1) (by omega))
    · have hm1 : ([0, 1, 2, 3, 4] : List ℕ).getD (i + 1) 0 -
          ([0, 1, 2, 3, 4] : List ℕ).getD i 0 = 1 := by omega
      have hzero : ([0, 1, 2, 3, 4] : List ℕ).getD (i + 1) 0 -
          ([0, 1, 2, 3, 4] : List ℕ).getD i 0 - 1 = 0 := by omega
      rw [hzero]
      rw [blockU_zero (K := K) hd hmono hfar hi]
      have hlast := blockU_last (K := K) hd hmono hfar hi
      rw [hm1] at hlast
      rw [hlast, h1i]
      exact plh_inf_Vsub_sgS_Vsub (K := K) (f := f) _

end CFSG.ClassicalInvolution.Phan.PhanE

end
