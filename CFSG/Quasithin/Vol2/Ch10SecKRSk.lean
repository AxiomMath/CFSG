module

public import CFSG.Quasithin.Vol2.Ch10SecKRSc
public import CFSG.Quasithin.Vol2.Ch10SecQ9H40

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open Matrix C10P4F

theorem presStd32_apply {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : PresStd (m := 3) (k := 2) M)
    {a b : Fin 5} (hb : (b : ℕ) < 3) (ha : 3 ≤ (a : ℕ)) : M a b = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 2, a = Fin.natAdd 3 i :=
    ⟨⟨(a : ℕ) - 3, by omega⟩, Fin.ext (by simp; omega)⟩
  obtain ⟨j, rfl⟩ : ∃ j : Fin 3, b = Fin.castAdd 2 j := ⟨⟨b, hb⟩, rfl⟩
  exact h i j

theorem mem_M2_of_X3 {g : SL5} (hg : g ∈ X3) (hQ : g ∈ Q1) : g ∈ M 2 := by
  rw [mem_M_iff]
  intro a b hab hn
  have hab' : (b : ℕ) < a := hab
  have h43 : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 3 = 0 := by
    have := congrFun (congrFun hg.2 1) 0
    simpa [botB] using this
  rcases Nat.lt_or_ge (b : ℕ) 3 with hb | hb
  · rcases Nat.lt_or_ge (a : ℕ) 3 with ha | ha
    ·
      have hb0 : (b : ℕ) = 0 := by
        by_contra h
        exact hn ⟨by omega, by omega⟩
      have : b = 0 := Fin.ext hb0
      rw [this]
      exact mem_Q1_iff.mp hQ a (by omega)
    · exact presStd32_apply hg.1 hb ha
  · have ha4 : a = 4 := Fin.ext (by omega)
    have hb3 : b = 3 := Fin.ext (by omega)
    rw [ha4, hb3]
    exact h43

theorem col_of_fix {g : SL5} (hfix : ∀ v ∈ stdE 5 3, g • v = v) {a b : Fin 5}
    (hb : (b : ℕ) < 3) : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b = if a = b then 1 else 0 := by
  have hv : (Pi.single b (1 : ZMod 2) : Fin 5 → ZMod 2) ∈ stdE 5 3 := fun i hi => by
    have : i ≠ b := fun h => by rw [h] at hi; omega
    simp [this]
  have h1 := congrFun (hfix _ hv) a
  rw [smul_eq_mulVec'] at h1
  by_cases hab : a = b
  · subst hab
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
  · simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hab] using h1

theorem mem_M4_of_fix {g : SL5} (hfix : ∀ v ∈ stdE 5 3, g • v = v) : g ∈ M 4 := by
  have hcol : ∀ a b : Fin 5, (b : ℕ) < 3 → a ≠ b →
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b = 0 := fun a b hb hab => by
    rw [col_of_fix hfix hb]; simp [hab]
  rw [mem_M_iff]
  intro a b hab hn
  have hab' : (b : ℕ) < a := hab
  rcases Nat.lt_or_ge (b : ℕ) 3 with hb | hb
  · exact hcol a b hb (ne_of_gt hab)
  · exact absurd ⟨by omega, by omega⟩ hn

@[expose] def cS : SL5 := trvE 1 2 (by decide) * trvE 2 1 (by decide)

@[expose] def dS : SL5 := trvE 0 1 (by decide) * trvE 1 0 (by decide)

theorem cS_pow : cS ^ 3 = 1 := by decide

theorem dS_pow : dS ^ 3 = 1 := by decide

theorem dS_ne : dS ≠ 1 := by decide

theorem cS_mem_X3 : cS ∈ X3 := by
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> rfl
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem dS_mem_X3 : dS ∈ X3 := by
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> rfl
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl

theorem cS_mem_Q1 : cS ∈ Q1 :=
  mem_Q1_iff.mpr fun a ha => by fin_cases a <;> simp at ha <;> rfl

theorem dS_mem_M1 : dS ∈ M 1 := by
  rw [mem_M_iff]
  intro a b hab hn
  fin_cases a <;> fin_cases b <;> simp_all <;> rfl

theorem dS_mulVec_ne : (dS : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single 0 1 ≠ Pi.single 0 1 := by
  decide

theorem dS_conj_B0 : (dS : Matrix (Fin 5) (Fin 5) (ZMod 2)) * B0 *
    (dS : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = B0 := by decide

theorem dS_mem_Q2 : dS ∈ Q2 := fun i j => by fin_cases i <;> fin_cases j <;> rfl

theorem botB_dS : botB (m := 2) (k := 3) (dS : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
