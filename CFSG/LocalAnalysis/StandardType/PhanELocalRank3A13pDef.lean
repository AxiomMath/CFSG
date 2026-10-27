module

public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def Adm13p (p L H : Submodule K (Fin 4 → K)) : Prop :=
  H ⊓ Vsub 4 1 = ⊥ ∧ (p ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (p ⊔ Vsub 4 1) = Vsub 4 1 ∧
    (L ⊔ Vsub 4 1) ⊓ perpB K f 4 1 4 (L ⊔ Vsub 4 1) = Vsub 4 1

private theorem plh_blockU_a3_13p (x : FlagK K 4) (r : ℕ) :
    blockU K 4 [0, 1, 4] x.E 1 r = x.E r ⊔ Vsub (K := K) 4 1 := by
  have hget : ([0, 1, 4] : List ℕ).getD (1 + 1) 0 = 4 := rfl
  have hget1 : ([0, 1, 4] : List ℕ).getD 1 0 = 1 := rfl
  have harg : (4 : ℕ) - ([0, 1, 4] : List ℕ).getD (1 + 1) 0 + r = r := by
    rw [hget]
    omega
  simp only [blockU]
  rw [harg, hget, hget1, Vsub_self, inf_top_eq]

private theorem plh_mem_farSet_a3_13p_iff (x : FlagK K 4) :
    x ∈ farSet 4 [0, 1, 4] ↔ x.E 3 ⊓ Vsub 4 1 = ⊥ := by
  have hd : ∀ i, i < ([0, 1, 4] : List ℕ).length →
      ([0, 1, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i <;> decide
  rw [mem_farSet_iff (K := K) (n := 4) (d := [0, 1, 4]) hd]
  constructor
  · intro h
    have h' := (h 1 (by decide) 3 (by decide)).1 (by decide)
    simpa using h'
  · intro h
    intro i hi j hj
    have hi3 : i < 3 := by simpa using hi
    interval_cases i
    · constructor
      · intro _
        rw [show ([0, 1, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, inf_bot_eq]
      · intro hge
        have hj4 : j = 4 := by
          have : 4 ≤ j := by simpa using hge
          omega
        subst hj4
        rw [show ([0, 1, 4] : List ℕ).getD 0 0 = 0 from rfl, Vsub_zero, sup_bot_eq]
        exact x.top 4 le_rfl
    · constructor
      · intro hjc
        have hj3 : j ≤ 3 := by
          have : j + 1 ≤ 4 := by simpa using hjc
          omega
        exact le_bot_iff.mp ((inf_le_inf_right (Vsub (K := K) 4 1) (x.mono hj3)).trans
          (le_of_eq h))
      · intro hge
        have hj3 : 3 ≤ j := by
          have : 4 ≤ j + 1 := by simpa using hge
          omega
        have hsup : x.E 3 ⊔ Vsub (K := K) 4 1 = ⊤ := by
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [Module.finrank_fin_fun]
          have hsum := Submodule.finrank_sup_add_finrank_inf_eq (x.E 3)
            (Vsub (K := K) 4 1)
          rw [h, finrank_bot, add_zero, FlagK.finrank_E_three,
            finrank_Vsub (K := K) (n := 4) (c := 1) (by norm_num)] at hsum
          omega
        exact top_le_iff.mp (hsup ▸ sup_le_sup (x.mono hj3) le_rfl)
    · constructor
      · intro hjc
        have hj0 : j = 0 := by
          have : j + 4 ≤ 4 := by simpa using hjc
          omega
        subst hj0
        rw [show ([0, 1, 4] : List ℕ).getD 2 0 = 4 from rfl, Vsub_self, inf_top_eq]
        exact FlagK.E_zero x
      · intro _
        rw [show ([0, 1, 4] : List ℕ).getD 2 0 = 4 from rfl, Vsub_self, sup_top_eq]

private theorem plh_blockOK_a3_13p_iff (x : FlagK K 4) (hfar : x ∈ farSet 4 [0, 1, 4]) :
    blockOK K f 4 [0, 1, 4] [false, true] x.E 1 ↔
      (x.E 1 ⊔ Vsub (K := K) 4 1) ⊓ perpB K f 4 1 4 (x.E 1 ⊔ Vsub (K := K) 4 1) =
          Vsub (K := K) 4 1 ∧
      (x.E 2 ⊔ Vsub (K := K) 4 1) ⊓ perpB K f 4 1 4 (x.E 2 ⊔ Vsub (K := K) 4 1) =
          Vsub (K := K) 4 1 := by
  have hd : ∀ i, i < ([0, 1, 4] : List ℕ).length →
      ([0, 1, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i <;> decide
  have hmono : ∀ i, i + 1 < ([0, 1, 4] : List ℕ).length →
      ([0, 1, 4] : List ℕ).getD i 0 ≤ ([0, 1, 4] : List ℕ).getD (i + 1) 0 := by
    intro i hi
    have hi2 : i < 2 := by
      have : i + 1 < 3 := by simpa using hi
      omega
    interval_cases i <;> decide
  have hget : ([0, 1, 4] : List ℕ).getD (1 + 1) 0 = 4 := rfl
  have hget1 : ([0, 1, 4] : List ℕ).getD 1 0 = 1 := rfl
  rw [blockOK_iff_of_far (K := K) (f := f) hd hmono hfar (i := 1) (by decide)]
  simp only [plh_blockU_a3_13p, hget, hget1, List.getD_nil,
    show ([false, true] : List Bool).getD 1 false = true from rfl, ↓reduceIte]
  constructor
  · intro h
    have h1 := h 1 (by norm_num) (by norm_num)
    have h2 := h 2 (by norm_num) (by norm_num)
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ r hr0 hr3
    have hr : r = 1 ∨ r = 2 := by omega
    rcases hr with rfl | rfl
    · exact h1
    · exact h2

theorem genSet_a3_13p_eq :
    genSet K f 4 [0, 1, 4] [false, true] = admSet (Adm13p (K := K) f) := by
  ext x
  simp only [genSet, Set.mem_setOf_eq, admSet, Adm13p]
  have hfar_iff := plh_mem_farSet_a3_13p_iff (K := K) x
  have hd : ∀ i, i < ([0, 1, 4] : List ℕ).length →
      ([0, 1, 4] : List ℕ).getD i 0 ≤ 4 := by
    intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i <;> decide
  have hmono : ∀ i, i + 1 < ([0, 1, 4] : List ℕ).length →
      ([0, 1, 4] : List ℕ).getD i 0 ≤ ([0, 1, 4] : List ℕ).getD (i + 1) 0 := by
    intro i hi
    have hi2 : i < 2 := by
      have : i + 1 < 3 := by simpa using hi
      omega
    interval_cases i <;> decide
  constructor
  · rintro ⟨hfar, hblock⟩
    have hb := (plh_blockOK_a3_13p_iff (K := K) (f := f) x hfar).mp (hblock 1 (by decide))
    exact ⟨hfar_iff.mp hfar, hb.1, hb.2⟩
  · rintro ⟨hH, h2, h3⟩
    refine ⟨hfar_iff.mpr hH, ?_⟩
    intro i hi
    have hi2 : i < 2 := by
      have : i + 1 < 3 := by simpa using hi
      omega
    interval_cases i
    · exact blockOK_of_size_one (K := K) (f := f) hd hmono (hfar_iff.mpr hH)
        (i := 0) (by decide) (by decide)
    · exact (plh_blockOK_a3_13p_iff (K := K) (f := f) x (hfar_iff.mpr hH)).mpr ⟨h2, h3⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
