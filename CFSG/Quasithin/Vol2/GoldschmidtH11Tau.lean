module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Vol2.GoldschmidtH11Rank
public import CFSG.Quasithin.Vol2.GoldschmidtH11Field

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

theorem mem_fixV_zpowers {V : Type*} [CommGroup V] (t : MulAut V) (v : V) :
    v ∈ fixV (Subgroup.zpowers t) ↔ t v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem tau_fix_iff (h : Nat.card F = 2 ^ (2 * a)) (v : HV F a) :
    tauAut a h v = v ↔ sg a (hm a v 0 1) = hm a v 0 1 := by
  rw [← hm_eq_iff, hm_tauAut]
  constructor
  · intro hc
    exact congrFun (congrFun hc 0) 1
  · intro hc
    have h10 : hm a v 1 0 = sg a (hm a v 0 1) := (hm_entry a v 1 0).symm
    ext i j
    fin_cases i <;> fin_cases j
    · exact hm_entry a v 0 0
    · exact hc
    · simp only [frobPow_apply]
      show sg a (hm a v 1 0) = hm a v 1 0
      rw [h10, hc]
      exact hc
    · exact hm_entry a v 1 1

@[expose] noncomputable def tauFixEquiv (h : Nat.card F = 2 ^ (2 * a)) :
    fixV (Subgroup.zpowers (tauAut a h)) ≃
      ((Kf a : Subfield F) : Set F) × ((Kf a : Subfield F) : Set F) × ((Kf a : Subfield F) : Set F)
    where
  toFun v := (⟨hm a v.1 0 0, (mem_Kf a).mpr (hm_entry a v.1 0 0)⟩,
    ⟨hm a v.1 0 1, (mem_Kf a).mpr ((tau_fix_iff h v.1).mp ((mem_fixV_zpowers _ _).mp v.2))⟩,
    ⟨hm a v.1 1 1, (mem_Kf a).mpr (hm_entry a v.1 1 1)⟩)
  invFun p := ⟨hermV a h p.1.1 p.2.1.1 p.2.2.1 ((mem_Kf a).mp p.1.2) ((mem_Kf a).mp p.2.2.2),
    (mem_fixV_zpowers _ _).mpr ((tau_fix_iff h _).mpr (by
      simpa [hm_hermV] using (mem_Kf a).mp p.2.1.2))⟩
  left_inv v := by
    apply Subtype.ext
    apply hm_injective a
    rw [hm_hermV, hm_eq a v.1]
  right_inv p := by simp [hm_hermV]

theorem card_fixV_tau (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) :
    Nat.card (fixV (Subgroup.zpowers (tauAut a h))) = 2 ^ (3 * a) := by
  rw [Nat.card_congr (tauFixEquiv h), Nat.card_prod, Nat.card_prod, card_Kf a ha h,
    ← pow_add, ← pow_add]
  congr 1
  ring

theorem rkIdx_fixV_tau (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) :
    rkIdx (fixV (Subgroup.zpowers (tauAut a h))) = a := by
  have h1 := rkIdx_add_rk ha h (fixV (Subgroup.zpowers (tauAut a h)))
  have h2 := card_two_pow_rk (fixV (Subgroup.zpowers (tauAut a h)))
  rw [card_fixV_tau ha h] at h2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

@[expose] noncomputable def sgMap (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) : SL(2, F) :=
  Matrix.SpecialLinearGroup.map (sgEquiv a h).toRingHom γ

theorem tau_actHom (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) :
    tauAut a h * actHom a h γ = actHom a h (sgMap h γ) * tauAut a h := by
  refine MulEquiv.ext fun v => ?_
  exact fieldAut_actHom a h (sgEquiv a h) γ v

theorem tau_conj_actHom (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) :
    tauAut a h * actHom a h γ * (tauAut a h)⁻¹ = actHom a h (sgMap h γ) := by
  rw [tau_actHom, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.Quasithin.H11
