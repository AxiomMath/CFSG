module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTInnerGrp

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.GroupTheory.NormalOddInversion

public section

namespace CFSG.StandardType
open Subgroup

theorem GGIsReflection.ne_one {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} [Finite Bs] {t : MulAut Bs} (hr : GGIsReflection p t) : t ≠ 1 := by
  rintro rfl
  have h := hr.2
  have hfix : Nat.card {b : Bs // (1 : MulAut Bs) b = b} = Nat.card Bs :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
  rw [hfix] at h
  have hpos : 0 < Nat.card Bs := Nat.card_pos
  have : Nat.card Bs * p = Nat.card Bs * 1 := by rw [mul_one]; exact h
  exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hpos this)

theorem GGIsReflection.exists_inverted_ne_one {G : Type} [Group G] {p : ℕ}
    (hp : p.Prime) {Bs : Subgroup G} [Finite Bs] {φ : MulAut Bs} (hφ : GGIsReflection p φ) :
    ∃ e : Bs, e ≠ 1 ∧ φ e = e⁻¹ :=
  CFSG.GroupTheory.exists_ne_one_apply_eq_inv_of_mul_self_eq_one
    (by simpa [pow_two] using hφ.1) (hφ.ne_one hp)

theorem GGIsReflection.eqLocus_sup_zpowers_of_inverted_three
    {G : Type} [Group G] {E : Subgroup G} [Finite E]
    (hE : CFSG.Open.IsElemAbelian 3 E) {φ : MulAut E} (hφ : GGIsReflection 3 φ)
    {e : E} (he : e ≠ 1) (hφe : φ e = e⁻¹) :
    φ.toMonoidHom.eqLocus (MonoidHom.id E) ⊔ zpowers e = ⊤ := by
  have : IsMulCommutative E := hE.1
  have h3 : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (hE.2 x x.2)
  have hδe : φ e * e⁻¹ = e := by
    rw [hφe, ← mul_inv_rev]
    have hx3 := h3 e
    have hx : e * e = e⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      simpa only [pow_succ, pow_two, pow_zero, one_mul, mul_assoc] using hx3
    rw [hx, inv_inv]
  have hd1 : φ e * e⁻¹ ≠ 1 := by rwa [hδe]
  apply top_unique
  intro x hx
  have hδ : φ x * x⁻¹ ∈ zpowers e := by
    have h := CFSG.GGQ2Prime.rhoTInner_mem_zpowers_of_reflection h3 hφ.2 e x hd1
    rwa [hδe] at h
  let d := φ x * x⁻¹
  let f := x * d⁻¹
  have hfix : φ f = f := by
    have hφφ : φ (φ x) = x := by
      have h := congrArg (fun a : MulAut E => a x) hφ.1
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
    have hd : φ d = d⁻¹ := by
      dsimp [d]
      rw [map_mul, map_inv, hφφ]
      group
    have hd3 := h3 d
    have hinv : d⁻¹ = d * d := inv_eq_of_mul_eq_one_right (by
      change d * (d * d) = 1
      simpa only [pow_succ, pow_two, pow_zero, one_mul, mul_assoc] using hd3)
    dsimp [f]
    rw [map_mul, map_inv, hd, inv_inv, show φ x = d * x from by dsimp [d]; group]
    calc (d * x) * d = x * (d * d) := by
          rw [mul_comm' d x]
          group
      _ = x * d⁻¹ := by rw [hinv]
  have hf : f ∈ φ.toMonoidHom.eqLocus (MonoidHom.id E) := hfix
  have hx : f * d = x := by dsimp [f]; group
  rw [← hx]
  exact (φ.toMonoidHom.eqLocus (MonoidHom.id E) ⊔ zpowers e).mul_mem
    (mem_sup_left hf) (mem_sup_right hδ)


end CFSG.StandardType
