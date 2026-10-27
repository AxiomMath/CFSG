module

public import CFSG.LocalAnalysis.StandardType.GGK2E6B5RawBasis
public import CFSG.LocalAnalysis.StandardType.GGK2E6C2SPFromMonomial

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.HdRo7C

noncomputable def b5CDiag (i : Fin 5) : ZMod 3 := if i = 4 then 2 else 1

lemma b5CDiag_ne_zero (i : Fin 5) : b5CDiag i ≠ 0 := by
  unfold b5CDiag
  split_ifs
  · exact (by decide : (2 : ZMod 3) ≠ 0)
  · exact one_ne_zero

lemma b5CDiag_cartan (i j : Fin 5) :
    (b5CDiag i)⁻¹ * b5CDiag j * (CartanMatrix.C 5 i j : ZMod 3) =
      (CartanMatrix.B 5 i j : ZMod 3) := by
  fin_cases i <;> fin_cases j <;>
    simp [b5CDiag, CartanMatrix.B, CartanMatrix.C] <;>
    first | exact inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) | norm_num

theorem exists_b5_c2sp_model_of_cartan
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {u : Fin 5 → V} {α : Fin 5 → Module.Dual (ZMod 3) V} {x : V}
    (hφ : ∀ i, α i (u i) = 2)
    (hCartan : (∀ i j, α i (u j) = (CartanMatrix.B 5 i j : ZMod 3)) ∨
      (∀ i j, α i (u j) = (CartanMatrix.C 5 i j : ZMod 3)))
    (hx0 : x ≠ 0) (hαx : ∀ i, α i x = 0)
    (hfin : Module.finrank (ZMod 3) V = 6) :
    ∃ b : Module.Basis (Fin 6) (ZMod 3) V,
      b 0 = x ∧ ∀ i : Fin 5, C2SP 3 b (Module.reflection (hφ i)) := by
  classical
  rcases hCartan with hB | hC
  · obtain ⟨b, hb0, hmono⟩ := exists_b5_six_basis_of_coroots
      (p := 3) (by norm_num) (u := u) (α := α) (x := x) hφ hB hx0 hαx hfin
    refine ⟨b, hb0, fun i => ?_⟩
    apply c2sp_of_monomial_three b (Module.reflection (hφ i))
    · rw [hb0, Module.reflection_apply, hαx i, zero_smul, sub_zero]
    · intro k
      obtain ⟨j, c, hc⟩ := hmono i k
      refine ⟨j, c, ?_, hc⟩
      intro hc0
      have hr0 : Module.reflection (hφ i) (b k) = 0 := by
        rw [hc, hc0, zero_smul]
      have hbk : b k = 0 := (Module.reflection (hφ i)).injective (by simpa using hr0)
      exact b.ne_zero k hbk
  ·
    let u' : Fin 5 → V := fun i => b5CDiag i • u i
    let α' : Fin 5 → Module.Dual (ZMod 3) V := fun i => (b5CDiag i)⁻¹ • α i
    have hφ' : ∀ i, α' i (u' i) = 2 := by
      intro i
      dsimp only [α', u']
      rw [LinearMap.smul_apply, smul_eq_mul, LinearMap.map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
      rw [hφ i]
      field_simp [b5CDiag_ne_zero i]
    have hB' : ∀ i j, α' i (u' j) = (CartanMatrix.B 5 i j : ZMod 3) := by
      intro i j
      dsimp only [α', u']
      rw [LinearMap.smul_apply, smul_eq_mul, LinearMap.map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
      rw [hC i j]
      simpa [mul_assoc] using b5CDiag_cartan i j
    obtain ⟨b, hb0, hmono⟩ := exists_b5_six_basis_of_coroots
      (p := 3) (by norm_num) (u := u') (α := α') (x := x) hφ' hB' hx0
      (by intro i; simp [α', hαx i]) hfin
    refine ⟨b, hb0, fun i => ?_⟩
    have hrefl : (Module.reflection (hφ' i) : V ≃ₗ[ZMod 3] V) =
        Module.reflection (hφ i) := by
      ext v
      simp only [Module.reflection_apply]
      congr 1
      dsimp only [α', u']
      rw [LinearMap.smul_apply, smul_eq_mul, smul_smul]
      field_simp [b5CDiag_ne_zero i]
    rw [← hrefl]
    apply c2sp_of_monomial_three b (Module.reflection (hφ' i))
    · rw [Module.reflection_apply]
      rw [hb0]
      have hα'x : α' i x = 0 := by simp [α', hαx i]
      rw [hα'x, zero_smul, sub_zero]
    · intro k
      obtain ⟨j, c, hc⟩ := hmono i k
      refine ⟨j, c, ?_, hc⟩
      intro hc0
      have hr0 : Module.reflection (hφ' i) (b k) = 0 := by
        rw [hc, hc0, zero_smul]
      have hbk : b k = 0 := (Module.reflection (hφ' i)).injective (by simpa using hr0)
      exact b.ne_zero k hbk

end CFSG.StandardType

end
