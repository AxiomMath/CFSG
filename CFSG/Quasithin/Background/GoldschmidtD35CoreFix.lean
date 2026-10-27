module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreOdd
public import CFSG.Quasithin.Background.GoldschmidtD35CoreAct
public import CFSG.Quasithin.Background.GoldschmidtD35CoreField

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin Equiv
open scoped Matrix LinearAlgebra.Projectivization

variable {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
variable {pt : Fin 6 → ℙ K (Fin 3 → K)}

omit [Finite K] in
theorem eq_one_of_mem_center_of_sq (hval : IsValentiner K Γ) {z : Γ}
    (hz : z ∈ Subgroup.center Γ) (hz2 : z * z = 1) : z = 1 := by
  have h3 : z ^ 3 = 1 := by
    have : (⟨z, hz⟩ : Subgroup.center Γ) ^ Nat.card (Subgroup.center Γ) = 1 := pow_card_eq_one'
    rw [hval.2.2.1.2.1] at this
    exact congrArg Subtype.val this
  calc z = z ^ 3 * (z * z)⁻¹ := by group
    _ = 1 := by rw [h3, hz2]; simp

theorem actPerm_ne_one_of_sq (hval : IsValentiner K Γ) (hO : IsSixOrbit (valL Γ) pt) {t : Γ}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : actPerm hO t ≠ 1 := fun h =>
  ht1 (eq_one_of_mem_center_of_sq hval ((actPerm_eq_one_iff hval hO t).1 h) ht2)

omit [Finite K] in
theorem lineAction_eq_of_smul (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) {p q : ℙ K (Fin 3 → K)} {c : K}
    (h : g p.rep = c • q.rep) : lineAction K (Fin 3 → K) g p = q :=
  pointAct_eq_of_smul (toGamma K (Fin 3 → K) g) ((toGamma_apply K _ g _).trans h)

theorem actPerm_fix_iff (hval : IsValentiner K Γ) (hO : IsSixOrbit (valL Γ) pt) {t : Γ}
    (ht2 : t * t = 1) (i : Fin 6) :
    actPerm hO t i = i ↔ (pt i).rep ∈ {w : Fin 3 → K | ((t : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ w = w} := by
  have hchar := charP_two_of_card_four hval.1
  have hg2 : ∀ v, glLin t.1 (glLin t.1 v) = v := fun v => by
    have h := congrArg (fun γ : Γ => glLin γ.1 v) ht2
    simpa [map_mul] using h
  constructor
  · intro h
    have h1 : lineAction K (Fin 3 → K) (glLin t.1) (pt i) = pt i := by
      rw [actPerm_spec hO, h]
    obtain ⟨c, hc0, hc⟩ := exists_smul_rep h1
    have hc2 : c * c = 1 := by
      have h2 : (pt i).rep = (c * c) • (pt i).rep := by
        calc (pt i).rep = glLin t.1 (glLin t.1 (pt i).rep) := (hg2 _).symm
          _ = (c * c) • (pt i).rep := by rw [hc, map_smul, hc, smul_smul]
      have h3 : ((c * c) - 1) • (pt i).rep = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
      have := (smul_eq_zero.1 h3).resolve_right (pt i).rep_nonzero
      exact sub_eq_zero.1 this
    have hc1 : c = 1 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have : (c - 1) * (c - 1) = 0 := by
        calc (c - 1) * (c - 1) = c * c - 2 * c + 1 := by ring
          _ = 1 - 2 * c + 1 := by rw [hc2]
          _ = 2 - 2 * c := by ring
          _ = 0 := by rw [h2]; ring
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    rw [hc1, one_smul] at hc
    show _ *ᵥ _ = _
    rw [← glLin_apply]
    exact hc
  · intro h
    have h1 : lineAction K (Fin 3 → K) (glLin t.1) (pt i) = pt i :=
      lineAction_eq_of_smul _ (c := 1) (by rw [one_smul, glLin_apply]; exact h)
    exact hO.inj ((actPerm_spec hO t i).symm.trans h1)

end CFSG.Quasithin.D35Core
