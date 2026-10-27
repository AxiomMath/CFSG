module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin6
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Gen

public section

namespace CFSG.Quasithin

open Equiv CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

namespace S35.B5

open S35.Fin

@[expose] def rot5 : Perm (Fin 5) := finRotate 5

theorem cj_zpowers_rot5 :
    cj rot5 (Subgroup.zpowers S5g) = Subgroup.zpowers (rot5 * S5g * rot5⁻¹) :=
  cj_zpowers rot5 S5g

theorem gen_cyclic :
    Subgroup.zpowers S5g ⊔ cj rot5 (Subgroup.zpowers S5g) = ⊤ := by
  rw [cj_zpowers_rot5]
  set a : Perm (Fin 5) := S5g with ha
  set b : Perm (Fin 5) := rot5 * S5g * rot5⁻¹ with hb
  have hA : a ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hB : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have e01 : swap (0 : Fin 5) 1 = b * b * a * b * a := by
    rw [ha, hb]; unfold rot5 S5g; decide +kernel
  have e12 : swap (1 : Fin 5) 2 = a * b * b * a * b := by
    rw [ha, hb]; unfold rot5 S5g; decide +kernel
  have e23 : swap (2 : Fin 5) 3 = a * b * a * a * b := by
    rw [ha, hb]; unfold rot5 S5g; decide +kernel
  have e34 : swap (3 : Fin 5) 4 = a * a * b⁻¹ * a⁻¹ * b⁻¹ := by
    rw [ha, hb]; unfold rot5 S5g; decide +kernel
  have hA' := inv_mem hA
  have hB' := inv_mem hB
  refine eq_top_of_path_swaps ?_ ?_ ?_ ?_
  · rw [e01]; exact mul_mem (mul_mem (mul_mem (mul_mem hB hB) hA) hB) hA
  · rw [e12]; exact mul_mem (mul_mem (mul_mem (mul_mem hA hB) hB) hA) hB
  · rw [e23]; exact mul_mem (mul_mem (mul_mem (mul_mem hA hB) hA) hA) hB
  · rw [e34]; exact mul_mem (mul_mem (mul_mem (mul_mem hA hA) hB') hA') hB'

theorem gen_syl :
    S5Syl ⊔ cj conjThat234 S5Syl = ⊤ := by
  rw [eq_top_iff]
  refine top_le_that_sup.trans (sup_le_sup ?_ ?_)
  · rw [← That_std]
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  · exact Subgroup.map_mono (by
      rw [← That_std]
      exact (Subgroup.closure_le _).mpr fun x hx => hx.1)

theorem gen_that :
    S5That ⊔ cj conjThat234 S5That = ⊤ := top_le_iff.mp top_le_that_sup

theorem exists_gen_perm_std {X : Subgroup (Perm (Fin 5))} (hle : X ≤ S5Syl)
    (hn : ∀ d ∈ S5Syl, ∀ x ∈ X, d * x * d⁻¹ ∈ X) (hA : ¬ X ≤ alternatingGroup (Fin 5)) :
    ∃ g : Perm (Fin 5), X ⊔ cj g X = ⊤ := by
  rcases normal_cases_std hle hn with h | h | h | h | h | h
  · exact absurd (h ▸ bot_le) hA
  · refine absurd ?_ hA
    rw [h, Subgroup.zpowers_le]
    exact Perm.mem_alternatingGroup.mpr (by unfold zStd; decide +kernel)
  · exact absurd (h ▸ inf_le_right) hA
  · exact ⟨_, h ▸ gen_that⟩
  · exact ⟨_, h ▸ gen_cyclic⟩
  · exact ⟨_, h ▸ gen_syl⟩

theorem cj_mul (g h : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) :
    cj (g * h) B = cj g (cj h B) := by
  ext x
  rw [mem_cj, mem_cj, mem_cj]
  simp [mul_assoc]

theorem cj_top (g : Perm (Fin 5)) : cj g (⊤ : Subgroup (Perm (Fin 5))) = ⊤ := by
  ext x
  rw [mem_cj]
  simp

theorem cj_sup (g : Perm (Fin 5)) (B C : Subgroup (Perm (Fin 5))) :
    cj g (B ⊔ C) = cj g B ⊔ cj g C := Subgroup.map_sup _ _ _

theorem cj_alt (g : Perm (Fin 5)) : cj g (alternatingGroup (Fin 5)) = alternatingGroup (Fin 5) := by
  ext x
  rw [mem_cj]
  simp only [Perm.mem_alternatingGroup, Perm.sign_mul]
  rcases Int.units_eq_one_or (Perm.sign g) with h | h <;> simp [h]

theorem exists_gen_perm {D X : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (hXD : X ≤ D)
    (hn : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ ∈ X) (hA : ¬ X ≤ alternatingGroup (Fin 5)) :
    ∃ g : Perm (Fin 5), X ⊔ cj g X = ⊤ := by
  obtain ⟨g0, rfl⟩ := exists_cj hD
  have hle : cj g0⁻¹ X ≤ S5Syl := le_cj_iff.mp hXD
  have hn' : ∀ d ∈ S5Syl, ∀ x ∈ cj g0⁻¹ X, d * x * d⁻¹ ∈ cj g0⁻¹ X := by
    intro d hd x hx
    rw [mem_cj] at hx ⊢
    have h1 := hn (g0 * d * g0⁻¹) (mem_cj_conj.mpr hd) _ hx
    simpa [mul_assoc] using h1
  have hA' : ¬ cj g0⁻¹ X ≤ alternatingGroup (Fin 5) := by
    intro h
    apply hA
    have := Subgroup.map_mono (f := (MulAut.conj g0).toMonoidHom) h
    rw [← cj_cj_inv g0 X]
    exact (cj_alt g0 ▸ this)
  obtain ⟨g1, hg1⟩ := exists_gen_perm_std hle hn' hA'
  refine ⟨g0 * g1 * g0⁻¹, ?_⟩
  have h2 : cj (g0 * g1 * g0⁻¹) X = cj g0 (cj g1 (cj g0⁻¹ X)) := by
    rw [cj_mul, cj_mul]
  have h3 : X ⊔ cj g0 (cj g1 (cj g0⁻¹ X)) = cj g0 (cj g0⁻¹ X ⊔ cj g1 (cj g0⁻¹ X)) := by
    rw [cj_sup, cj_cj_inv]
  rw [h2, h3, hg1, cj_top]

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
