module

public import CFSG.Quasithin.Vol2.Ch10SecAT1Torus
public import CFSG.Quasithin.Vol2.Ch10SecQ3CO

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem conj_dU_mem_normalizer {F : Type} [Field F]
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hP : ∀ p, p ∈ P ↔ ∃ b : F, g * p * g⁻¹ = SecA.unipSL b) (μ : Fˣ) :
    g⁻¹ * dU μ * g ∈ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have hd : dU μ = SecA.diagSL μ.ne_zero := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_dU, SecA.coe_diagSL]
  rw [Subgroup.mem_normalizer_iff]
  intro p
  rw [hP, hP]
  have e : g * (g⁻¹ * dU μ * g * p * (g⁻¹ * dU μ * g)⁻¹) * g⁻¹ =
      dU μ * (g * p * g⁻¹) * (dU μ)⁻¹ := by group
  rw [e, hd]
  exact SecA.diagSL_conj_iff μ.ne_zero _

@[expose] def dUHom (F : Type) [Field F] : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := dU
  map_one' := dU_one
  map_mul' a b := (dU_mul a b).symm

theorem orderOf_conj_dU {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    {μ : Fˣ} (hμ : ∀ x : Fˣ, x ∈ Subgroup.zpowers μ) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    orderOf (g⁻¹ * dU μ * g) = 2 ^ m - 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h1 : orderOf (g⁻¹ * dU μ * g) = orderOf (dU μ) := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective (dU μ)
    simpa [MulAut.conj_apply] using this
  have h2 : orderOf (dU μ) = orderOf μ := orderOf_injective (dUHom F) dU_injective μ
  rw [h1, h2, orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_eq_fintype_card,
    Fintype.card_units, ← Nat.card_eq_fintype_card, hF]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
