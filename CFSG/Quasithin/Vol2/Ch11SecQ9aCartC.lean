module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartB

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups

variable (K : Type) [Field K]

abbrev torus3 : Subgroup (SpecialLinearGroup (Fin 3) K) := (tSL (K := K)).range

variable {K}

theorem tSL_injective : Function.Injective (tSL (K := K)) := by
  intro t t' h
  have h0 := congrArg
    (fun B : SpecialLinearGroup (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) 0 0) h
  have h1 := congrArg
    (fun B : SpecialLinearGroup (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) 1 1) h
  simp only [coe_tSL, Matrix.diagonal_apply_eq, tvec, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem torus3_inf_eq (X : Subgroup (SpecialLinearGroup (Fin 3) K)) :
    torus3 K ⊓ X = (X.comap tSL).map tSL :=
  (Subgroup.map_comap_eq tSL X).symm

theorem card_torus3_inf {X : Subgroup (SpecialLinearGroup (Fin 3) K)} (φ : Kˣ →* Kˣ × Kˣ)
    (hφ : Function.Injective φ) (hX : ∀ t, tSL t ∈ X ↔ ∃ s, φ s = t) :
    Nat.card ↥(torus3 K ⊓ X) = Nat.card Kˣ := by
  have hY : X.comap tSL = φ.range := by
    ext t
    rw [Subgroup.mem_comap, hX, MonoidHom.mem_range]
  rw [torus3_inf_eq, Subgroup.card_map_of_injective tSL_injective, hY,
    ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]

theorem card_torus3_inf_stabE0 : Nat.card ↥(torus3 K ⊓ stabE0 K) = Nat.card Kˣ := by
  refine card_torus3_inf (MonoidHom.inr Kˣ Kˣ) (fun a b h => (Prod.ext_iff.mp h).2) fun t => ?_
  rw [tSL_mem_stabE0_iff]
  constructor
  · intro h
    exact ⟨t.2, Prod.ext h.symm rfl⟩
  · rintro ⟨s, rfl⟩
    rfl

theorem card_torus3_inf_stabRow2 : Nat.card ↥(torus3 K ⊓ stabRow2 K) = Nat.card Kˣ := by
  refine card_torus3_inf ((MonoidHom.id Kˣ).prod invMonoidHom)
    (fun a b h => (Prod.ext_iff.mp h).1) fun t => ?_
  rw [tSL_mem_stabRow2_iff]
  constructor
  · intro h
    refine ⟨t.1, Prod.ext rfl ?_⟩
    change t.1⁻¹ = t.2
    exact (eq_inv_of_mul_eq_one_right h).symm
  · rintro ⟨s, rfl⟩
    exact mul_inv_cancel s

theorem card_torus3_inf_sc1 :
    Nat.card ↥(torus3 K ⊓ sectionCentralizer (stabE0 K) (rad1 K)) = Nat.card Kˣ := by
  refine card_torus3_inf ((invMonoidHom.comp (powMonoidHom 2)).prod (MonoidHom.id Kˣ))
    (fun a b h => (Prod.ext_iff.mp h).2) fun t => ?_
  rw [tSL_mem_sc1_iff]
  constructor
  · intro h
    refine ⟨t.2, Prod.ext ?_ rfl⟩
    change (t.2 ^ 2)⁻¹ = t.1
    exact (eq_inv_of_mul_eq_one_left h).symm
  · rintro ⟨s, rfl⟩
    change (s ^ 2)⁻¹ * s ^ 2 = 1
    exact inv_mul_cancel _

theorem card_torus3_inf_sc2 :
    Nat.card ↥(torus3 K ⊓ sectionCentralizer (stabRow2 K) (rad2 K)) = Nat.card Kˣ := by
  refine card_torus3_inf ((MonoidHom.id Kˣ).prod (MonoidHom.id Kˣ))
    (fun a b h => (Prod.ext_iff.mp h).1) fun t => ?_
  rw [tSL_mem_sc2_iff]
  constructor
  · intro h
    exact ⟨t.1, Prod.ext rfl h⟩
  · rintro ⟨s, rfl⟩
    rfl

theorem torus3_inf_inf_sc2 :
    torus3 K ⊓ stabE0 K ⊓ sectionCentralizer (stabRow2 K) (rad2 K) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨⟨t, rfl⟩, h1⟩, h2⟩
  have h1' := (tSL_mem_stabE0_iff t).mp h1
  have h2' := (tSL_mem_sc2_iff t).mp h2
  have : t = 1 := Prod.ext h1' (h2'.symm.trans h1')
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem torus3_le_sup :
    torus3 K ≤ (torus3 K ⊓ stabE0 K) ⊔ (torus3 K ⊓ stabRow2 K) := by
  rintro _ ⟨t, rfl⟩
  have ht : t = (1, t.1 * t.2) * (t.1, t.1⁻¹) := by
    refine Prod.ext ?_ ?_
    · change t.1 = 1 * t.1
      rw [one_mul]
    · change t.2 = t.1 * t.2 * t.1⁻¹
      rw [mul_comm t.1 t.2, mul_inv_cancel_right]
  rw [ht, map_mul]
  refine Subgroup.mul_mem_sup ⟨⟨_, rfl⟩, (tSL_mem_stabE0_iff _).mpr rfl⟩
    ⟨⟨_, rfl⟩, (tSL_mem_stabRow2_iff _).mpr (mul_inv_cancel _)⟩

variable [Finite K] [CharP K 2]

theorem torus3_le_sc1_sup :
    torus3 K ≤ (torus3 K ⊓ sectionCentralizer (stabE0 K) (rad1 K)) ⊔ (torus3 K ⊓ stabE0 K) := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' ((t.1⁻¹ : Kˣ) : K)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact Units.ne_zero _ hr
  set s : Kˣ := Units.mk0 r hr0 with hs
  have hs2 : s ^ 2 = t.1⁻¹ := Units.ext (by rw [Units.val_pow_eq_pow_val, hs, Units.val_mk0, hr,
    pow_two])
  have ht : t = (t.1, s) * (1, t.2 * s⁻¹) := by
    refine Prod.ext ?_ ?_
    · change t.1 = t.1 * 1
      rw [mul_one]
    · change t.2 = s * (t.2 * s⁻¹)
      rw [mul_comm t.2, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [ht, map_mul]
  refine Subgroup.mul_mem_sup ⟨⟨_, rfl⟩, (tSL_mem_sc1_iff _).mpr ?_⟩
    ⟨⟨_, rfl⟩, (tSL_mem_stabE0_iff _).mpr rfl⟩
  change t.1 * s ^ 2 = 1
  rw [hs2, mul_inv_cancel]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
