module

public import CFSG.LieType.Chevalley.F4FieldTwoEuclid
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem ggTBJ_f4_corootPair_le_fin (k l : Fin 48) :
    |corootPair (τ := Tag.F4) (Tag.F4.rootCertificate.root l)
      (Tag.F4.rootCertificate.root k)| ≤ 2 := by
  revert k l
  decide +kernel

theorem ggTBJ_zmod_intCast_ne_zero_of_abs_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {c : ℤ} (hle : |c| ≤ 2) (hne : c ≠ 0) : (c : ZMod p) ≠ 0 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hnd : ∀ d : ℤ, (d = 1 ∨ d = 2) → ¬ (p : ℤ) ∣ d := by
    intro d hd hdiv
    have hpos : (0 : ℤ) < d := by rcases hd with rfl | rfl <;> norm_num
    have hle' := Int.le_of_dvd hpos hdiv
    have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    rcases hd with rfl | rfl <;> omega
  have hc : c = -2 ∨ c = -1 ∨ c = 1 ∨ c = 2 := by
    have h := abs_le.1 hle
    omega
  rcases hc with rfl | rfl | rfl | rfl
  · intro hh
    exact hnd 2 (Or.inr rfl)
      (dvd_neg.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (-2) p).1 hh))
  · intro hh
    exact hnd 1 (Or.inl rfl)
      (dvd_neg.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd (-1) p).1 hh))
  · intro hh
    exact hnd 1 (Or.inl rfl) ((ZMod.intCast_zmod_eq_zero_iff_dvd 1 p).1 hh)
  · intro hh
    exact hnd 2 (Or.inr rfl) ((ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).1 hh)

theorem ggTBJ_corootPair_self
    (τ : Tag) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : corootPair β β = 2 := by
  have h := corootPair_mul (τ := τ) hβ β
  have hp := iform_self_pos_of_isRoot (τ := τ) hβ
  exact mul_right_cancel₀ hp.ne' (by rw [h])

end CFSG.StandardType

end
