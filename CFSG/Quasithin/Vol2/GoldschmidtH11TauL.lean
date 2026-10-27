module

public import CFSG.Quasithin.Vol2.GoldschmidtH11AutSL
public import CFSG.Quasithin.Vol2.GoldschmidtH11Tau

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

@[expose] def Lh (a : ℕ) (h : Nat.card F = 2 ^ (2 * a)) : Subgroup (MulAut (HV F a)) :=
  (actHom a h).range

theorem mem_Lh {x : MulAut (HV F a)} : x ∈ Lh a h ↔ ∃ γ : SL(2, F), actHom a h γ = x := Iff.rfl

theorem actHom_mem_Lh (γ : SL(2, F)) : actHom a h γ ∈ Lh a h := ⟨γ, rfl⟩

theorem tauAut_inv (h : Nat.card F = 2 ^ (2 * a)) : (tauAut a h)⁻¹ = tauAut a h :=
  inv_eq_of_mul_eq_one_right (tauAut_mul_self a h)

theorem tau_conj_mem_Lh {x : MulAut (HV F a)} (hx : x ∈ Lh a h) :
    tauAut a h * x * (tauAut a h)⁻¹ ∈ Lh a h := by
  obtain ⟨γ, rfl⟩ := hx
  rw [tau_conj_actHom]
  exact actHom_mem_Lh _

theorem tauAut_not_mem_Lh (ha : 0 < a) : tauAut a h ∉ Lh a h := by
  rintro ⟨γ₀, hγ₀⟩
  have key : ∀ δ : SL(2, F),
      γ₀⁻¹ * Matrix.SpecialLinearGroup.map (sgEquiv a h).toRingHom δ * (γ₀⁻¹)⁻¹ = δ := by
    intro δ
    apply actHom_injective a h
    have e1 := tau_conj_actHom h δ
    rw [← hγ₀] at e1
    simp only [map_mul, map_inv, inv_inv]
    change (actHom a h γ₀)⁻¹ * actHom a h (sgMap h δ) * actHom a h γ₀ = actHom a h δ
    rw [← e1]
    group
  have := (eq_one_of_aut_formula (sgEquiv a h) γ₀⁻¹ key).1
  obtain ⟨x, hx⟩ := exists_sg_ne a ha h
  exact hx (by simpa [sgEquiv_apply] using congrArg (fun e : F ≃+* F => e x) this)

theorem tau_mul_mem_Lh {x ℓ : MulAut (HV F a)} (hℓ : ℓ ∈ Lh a h) (hx : x = ℓ * tauAut a h * ℓ⁻¹) :
    tauAut a h * x ∈ Lh a h := by
  have h1 := tau_conj_mem_Lh hℓ
  have e : tauAut a h * x = (tauAut a h * ℓ * (tauAut a h)⁻¹) * ℓ⁻¹ := by
    rw [hx, tauAut_inv]
    simp only [mul_assoc]
  rw [e]
  exact (Lh a h).mul_mem h1 ((Lh a h).inv_mem hℓ)

end CFSG.Quasithin.H11
