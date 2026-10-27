module

public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private theorem plh_mem_farSet_a3_121_iff (x : FlagK K 4) :
    x ∈ farSet 4 [0, 1, 3, 4] ↔
      x.E 1 ⊓ Vsub 4 3 = ⊥ ∧ x.E 3 ⊓ Vsub 4 1 = ⊥ := by
  have hd : ∀ i, i < ([0, 1, 3, 4] : List ℕ).length →
      ([0, 1, 3, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi4 : i < 4 := by simpa using hi
    interval_cases i <;> decide
  rw [mem_farSet_iff (K := K) (n := 4) (d := [0, 1, 3, 4]) hd]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h' := (h 2 (by decide) 1 (by decide)).1 (by decide)
      simpa using h'
    · have h' := (h 1 (by decide) 3 (by decide)).1 (by decide)
      simpa using h'
  · rintro ⟨h1, h3⟩
    intro i hi j hj
    have hi4 : i < 4 := by simpa using hi
    interval_cases i
    · constructor
      · intro _
        rw [show ([0, 1, 3, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, inf_bot_eq]
      · intro hge
        have hj4 : j = 4 := by
          have : 4 ≤ j := by simpa using hge
          omega
        subst hj4
        rw [show ([0, 1, 3, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, sup_bot_eq]
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
        have hj1 : j ≤ 1 := by
          have : j + 3 ≤ 4 := by simpa using hjc
          omega
        interval_cases j
        · rw [FlagK.E_zero, bot_inf_eq]
        · simpa using h1
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
        rw [show ([0, 1, 3, 4] : List ℕ).getD 3 0 = 4 from rfl, Vsub_self, inf_top_eq]
        exact FlagK.E_zero x
      · intro _
        rw [show ([0, 1, 3, 4] : List ℕ).getD 3 0 = 4 from rfl, Vsub_self, sup_top_eq]

@[expose] noncomputable def Adm121 (p L H : Submodule K (Fin 4 → K)) : Prop :=
  p ⊓ Vsub 4 3 = ⊥ ∧ H ⊓ Vsub 4 1 = ⊥ ∧
    ((L ⊓ Vsub 4 3) ⊔ Vsub 4 1) ⊓ sgS K f 4 ((L ⊓ Vsub 4 3) ⊔ Vsub 4 1) = Vsub 4 1

theorem genSet_a3_121_eq :
    genSet K f 4 [0, 1, 3, 4] [] = admSet (Adm121 (K := K) f) := by
  ext x
  simp only [genSet, Set.mem_setOf_eq, admSet, Adm121]
  have hfar_iff := plh_mem_farSet_a3_121_iff (K := K) x
  refine ⟨?_, ?_⟩
  · rintro ⟨hfar, hblock⟩
    have hfar' := hfar_iff.mp hfar
    refine ⟨hfar'.1, hfar'.2, ?_⟩
    have hb := hblock 1 (by decide)
    rw [blockOK] at hb
    have hb1 := hb 1 (by decide)
    simp only [List.getD_nil, Bool.false_eq_true, ↓reduceIte] at hb1
    simpa [blockU] using hb1
  · rintro ⟨h1, h3, hU⟩
    have hfar' : x ∈ farSet 4 [0, 1, 3, 4] := hfar_iff.mpr ⟨h1, h3⟩
    refine ⟨hfar', ?_⟩
    have hle : ∀ i, i < ([0, 1, 3, 4] : List ℕ).length →
        ([0, 1, 3, 4] : List ℕ).getD i 0 ≤ 4 := by
      intro i hi
      have hi4 : i < 4 := by simpa using hi
      interval_cases i <;> decide
    have hmono : ∀ i, i + 1 < ([0, 1, 3, 4] : List ℕ).length →
        ([0, 1, 3, 4] : List ℕ).getD i 0 ≤
          ([0, 1, 3, 4] : List ℕ).getD (i + 1) 0 := by
      intro i hi
      have hi3 : i < 3 := by
        have : i + 1 < 4 := by simpa using hi
        omega
      interval_cases i <;> decide
    intro i hi
    have hi3 : i < 3 := by
      have : i + 1 < 4 := by simpa using hi
      omega
    interval_cases i
    · exact blockOK_of_size_one f hle hmono hfar' (by decide) (by decide)
    · rw [blockOK_iff_of_far f hle hmono hfar' (by decide)]
      intro r hr0 hrm
      have hr1 : r = 1 := by
        have : r < 2 := by simpa using hrm
        omega
      subst hr1
      simp only [List.getD_nil, Bool.false_eq_true, ↓reduceIte]
      simpa [blockU] using hU
    · exact blockOK_of_size_one f hle hmono hfar' (by decide) (by decide)

end CFSG.ClassicalInvolution.Phan.PhanE

end
