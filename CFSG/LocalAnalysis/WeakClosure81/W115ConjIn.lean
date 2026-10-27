module

public import CFSG.Sporadic.Mathieu.Asc1113M22Data
public import CFSG.Quasithin.Background.F7TwoInvSporM22

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Blueprint
open CFSG.Mathieu.Asc1113M22
open CFSG.Sporadic.Mathieu.Asc1113M22
open CFSG.Quasithin.F7Two

theorem w115_fourConj_inner
    {j : ↥NativeSporadic.M22} (hj2 : j * j = 1) (hj1 : j ≠ 1) :
    ∃ h : Fin 4 → ↥NativeSporadic.M22,
      Subgroup.closure (Set.range fun i => h i * j * (h i)⁻¹) = ⊤ := by
  have hj2' : (j : Equiv.Perm (Fin 22)) * (j : Equiv.Perm (Fin 22)) = 1 := by
    have h := congrArg (Subtype.val) hj2
    simpa using h
  have hj1' : (j : Equiv.Perm (Fin 22)) ≠ 1 := by
    intro h
    exact hj1 (Subtype.ext (by simpa using h))
  have hjord : orderOf (j : Equiv.Perm (Fin 22)) = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hj2') hj1'
  have hzord : orderOf z = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact z_sq) z_ne_one
  obtain ⟨c, hc, hjc⟩ := m22_inner_cover (u := (j : Equiv.Perm (Fin 22))) j.2 hjord
  obtain ⟨c', hc', hzc⟩ := m22_inner_cover (u := z) z_mem_H0 hzord
  let k : ↥NativeSporadic.M22 :=
    ⟨c * c'⁻¹, Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hc')⟩
  have hkval : (k : Equiv.Perm (Fin 22)) = c * c'⁻¹ := rfl
  have hj_eq : (j : Equiv.Perm (Fin 22)) = (k : Equiv.Perm (Fin 22)) * z
      * (k : Equiv.Perm (Fin 22))⁻¹ := by
    rw [hjc, hzc, hkval]
    group
  let h : Fin 4 → ↥NativeSporadic.M22 := fun i =>
    ⟨![g1, g2, g3, g4] i, by
      fin_cases i <;> simp [g1_mem_H0, g2_mem_H0, g3_mem_H0, g4_mem_H0]⟩ * k⁻¹
  refine ⟨h, ?_⟩
  have hcoe : ∀ i,
      ((h i * j * (h i)⁻¹ : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22)) = C4 i := by
    intro i
    fin_cases i
    · have h0 : (h 0 : Equiv.Perm (Fin 22)) = g1 * (k : Equiv.Perm (Fin 22))⁻¹ := rfl
      calc ((h 0 * j * (h 0)⁻¹ : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22))
          = (h 0 : Equiv.Perm (Fin 22)) * (j : Equiv.Perm (Fin 22))
              * (h 0 : Equiv.Perm (Fin 22))⁻¹ := rfl
        _ = g1 * z * g1⁻¹ := by rw [h0, hj_eq]; group
        _ = c1 := c1_eq_conj.symm
        _ = C4 0 := rfl
    · have h1 : (h 1 : Equiv.Perm (Fin 22)) = g2 * (k : Equiv.Perm (Fin 22))⁻¹ := rfl
      calc ((h 1 * j * (h 1)⁻¹ : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22))
          = (h 1 : Equiv.Perm (Fin 22)) * (j : Equiv.Perm (Fin 22))
              * (h 1 : Equiv.Perm (Fin 22))⁻¹ := rfl
        _ = g2 * z * g2⁻¹ := by rw [h1, hj_eq]; group
        _ = c2 := c2_eq_conj.symm
        _ = C4 1 := rfl
    · have h2 : (h 2 : Equiv.Perm (Fin 22)) = g3 * (k : Equiv.Perm (Fin 22))⁻¹ := rfl
      calc ((h 2 * j * (h 2)⁻¹ : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22))
          = (h 2 : Equiv.Perm (Fin 22)) * (j : Equiv.Perm (Fin 22))
              * (h 2 : Equiv.Perm (Fin 22))⁻¹ := rfl
        _ = g3 * z * g3⁻¹ := by rw [h2, hj_eq]; group
        _ = c3 := c3_eq_conj.symm
        _ = C4 2 := rfl
    · have h3 : (h 3 : Equiv.Perm (Fin 22)) = g4 * (k : Equiv.Perm (Fin 22))⁻¹ := rfl
      calc ((h 3 * j * (h 3)⁻¹ : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22))
          = (h 3 : Equiv.Perm (Fin 22)) * (j : Equiv.Perm (Fin 22))
              * (h 3 : Equiv.Perm (Fin 22))⁻¹ := rfl
        _ = g4 * z * g4⁻¹ := by rw [h3, hj_eq]; group
        _ = c4 := c4_eq_conj.symm
        _ = C4 3 := rfl
  have hfun : ((NativeSporadic.M22).subtype ∘ fun i => h i * j * (h i)⁻¹) = C4 := by
    funext i
    exact hcoe i
  have himg : (NativeSporadic.M22).subtype ''
        (Set.range fun i => h i * j * (h i)⁻¹) = Set.range C4 := by
    rw [← Set.range_comp]
    exact congrArg Set.range hfun
  have hmap : (Subgroup.closure (Set.range fun i => h i * j * (h i)⁻¹)).map
        (NativeSporadic.M22).subtype
      = (⊤ : Subgroup ↥NativeSporadic.M22).map (NativeSporadic.M22).subtype := by
    rw [MonoidHom.map_closure, himg, Subgroup.map_top, Subgroup.range_subtype]
    exact Kz_eq_H0
  exact Subgroup.map_subtype_inj.mp hmap

end CFSG.LocalAnalysis.WeakClosure81.W115
