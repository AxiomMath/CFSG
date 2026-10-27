module

public import CFSG.Quasithin.Background.SmithB45J2Comm

public section

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.CharacterTheory.SteinbergBY.FieldFour
open CFSG.Quasithin.H
open scoped Matrix

abbrev W6 := StdMod (Fin 6) FieldFour

noncomputable abbrev L6 : Subgroup (MulAut W6) := natImage Γ₆

@[expose] noncomputable def normConj : ↥(natNorm Γ₆) →* MulAut ↥L6 where
  toFun t :=
    { toFun := fun x => ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp t.2 x).mp x.2⟩
      invFun := fun x => ⟨t⁻¹ * x * t, by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ t.2) x).mp x.2
        simpa using h⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' s t := MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc])

theorem normConj_apply (t : ↥(natNorm Γ₆)) (x : ↥L6) :
    ((normConj t x : ↥L6) : MulAut W6) = t * x * t⁻¹ := rfl

theorem exists_smul_of_comm {u : MulAut W6} (hu : ∀ x ∈ L6, u * x = x * u) :
    ∃ c : FieldFour, ∀ v, toAddMap u v = c • v := by
  let f : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour) :=
    AddMonoidHom.mk' (toAddMap u) (toAddMap_add u)
  refine hasScalarCommutant_Γ₆ f fun γ hγ v => ?_
  have h := hu (natAut Γ₆ ⟨γ, hγ⟩) ⟨⟨γ, hγ⟩, rfl⟩
  have h1 := congrArg (fun y => toAddMap y v) h
  change toAddMap u _ = _ *ᵥ toAddMap u v
  simpa only [toAddMap_mul, toAddMap_natAut] using h1

theorem isSemilinear_of_smul {u : MulAut W6} {c : FieldFour} (hc : ∀ v, toAddMap u v = c • v) :
    IsSemilinear u (RingEquiv.refl FieldFour) := by
  intro d v
  rw [hc, hc, smul_comm]
  rfl

theorem isSemilinear_of_mem_L6 {x : MulAut W6} (hx : x ∈ L6) :
    IsSemilinear x (RingEquiv.refl FieldFour) :=
  natImage_le_linSub Γ₆ hx

theorem normConj_psi0_notMem :
    normConj ⟨psi0, psi0_mem_natNorm⟩ ∉ (MulAut.conj : ↥L6 →* MulAut ↥L6).range := by
  rintro ⟨ℓ, hℓ⟩
  have hcomm : ∀ x ∈ L6, ((ℓ : MulAut W6)⁻¹ * psi0) * x = x * ((ℓ : MulAut W6)⁻¹ * psi0) := by
    intro x hx
    have h := congrArg (fun φ : MulAut ↥L6 => ((φ ⟨x, hx⟩ : ↥L6) : MulAut W6)) hℓ
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, normConj_apply] at h
    calc (ℓ : MulAut W6)⁻¹ * psi0 * x = (ℓ : MulAut W6)⁻¹ * (psi0 * x * psi0⁻¹) * psi0 := by
          group
      _ = (ℓ : MulAut W6)⁻¹ * (ℓ * x * (ℓ : MulAut W6)⁻¹) * psi0 := by rw [h]
      _ = x * ((ℓ : MulAut W6)⁻¹ * psi0) := by group
  obtain ⟨c, hc⟩ := exists_smul_of_comm hcomm
  have h1 : IsSemilinear psi0 (RingEquiv.refl FieldFour) := by
    have e : psi0 = (ℓ : MulAut W6) * ((ℓ : MulAut W6)⁻¹ * psi0) := by group
    rw [e]
    have := (isSemilinear_of_mem_L6 ℓ.2).mul (isSemilinear_of_smul hc)
    exact this
  exact frobE_ne_refl (isSemilinear_psi0.unique h1)

section Index

variable (hAut : Nat.card (MulAut ↥L6) ≤ 2 * Nat.card ↥L6)
  (hZ : Subgroup.center ↥L6 = ⊥)

include hZ in
theorem conj_injective_L6 : Function.Injective (MulAut.conj : ↥L6 →* MulAut ↥L6) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxz : x ∈ Subgroup.center ↥L6 := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut ↥L6 => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * x = x * y * x⁻¹ * x := by rw [this]
      _ = x * y := by group
  rw [hZ] at hxz
  exact Subgroup.mem_bot.mp hxz

include hAut hZ in
theorem index_inner_le : (MulAut.conj : ↥L6 →* MulAut ↥L6).range.index ≤ 2 := by
  have : Finite ↥L6 := inferInstance
  have hfin : Finite (MulAut ↥L6) := MulEquiv.finite_left
  have h1 := Subgroup.card_mul_index (MulAut.conj : ↥L6 →* MulAut ↥L6).range
  have h2 : Nat.card ↥(MulAut.conj : ↥L6 →* MulAut ↥L6).range = Nat.card ↥L6 :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_L6 hZ)).toEquiv).symm
  rw [h2] at h1
  have hpos : 0 < Nat.card ↥L6 := Nat.card_pos
  by_contra h
  push Not at h
  have : 3 * Nat.card ↥L6 ≤ Nat.card ↥L6 * (MulAut.conj : ↥L6 →* MulAut ↥L6).range.index := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ h
  omega

include hAut hZ in
theorem normConj_mem_inner_of_linear {t : ↥(natNorm Γ₆)}
    (ht : IsSemilinear (t : MulAut W6) (RingEquiv.refl FieldFour)) :
    normConj t ∈ (MulAut.conj : ↥L6 →* MulAut ↥L6).range := by
  by_contra hnot
  set H := (MulAut.conj : ↥L6 →* MulAut ↥L6).range with hH
  have hidx : H.index = 2 := by
    have h1 : H.index ≤ 2 := index_inner_le hAut hZ
    have h2 : H.index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      intro htop
      exact hnot (htop ▸ Subgroup.mem_top _)
    have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hψ := normConj_psi0_notMem
  have hmem : normConj t * (normConj ⟨psi0, psi0_mem_natNorm⟩)⁻¹ ∈ H := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff]
    exact iff_of_false hnot hψ
  rw [← map_inv, ← map_mul] at hmem
  obtain ⟨ℓ, hℓ⟩ := hmem
  set s : MulAut W6 := (t : MulAut W6) * psi0⁻¹ with hs
  have hcomm : ∀ x ∈ L6, ((ℓ : MulAut W6)⁻¹ * s) * x = x * ((ℓ : MulAut W6)⁻¹ * s) := by
    intro x hx
    have h := congrArg (fun φ : MulAut ↥L6 => ((φ ⟨x, hx⟩ : ↥L6) : MulAut W6)) hℓ
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, normConj_apply] at h
    calc (ℓ : MulAut W6)⁻¹ * s * x = (ℓ : MulAut W6)⁻¹ * (s * x * s⁻¹) * s := by group
      _ = (ℓ : MulAut W6)⁻¹ * (ℓ * x * (ℓ : MulAut W6)⁻¹) * s := by rw [← h]
      _ = x * ((ℓ : MulAut W6)⁻¹ * s) := by group
  obtain ⟨c, hc⟩ := exists_smul_of_comm hcomm
  have h1 : IsSemilinear psi0 (RingEquiv.refl FieldFour) := by
    have e : psi0 = ((ℓ : MulAut W6) * ((ℓ : MulAut W6)⁻¹ * s))⁻¹ * t := by
      rw [hs]
      group
    rw [e]
    have hu := (isSemilinear_of_mem_L6 ℓ.2).mul (isSemilinear_of_smul hc)
    have := hu.inv.mul ht
    exact this
  exact frobE_ne_refl (isSemilinear_psi0.unique h1)

include hAut hZ in
theorem mem_natImage_of_linear {t : MulAut W6} (htN : t ∈ natNorm Γ₆)
    (ht : IsSemilinear t (RingEquiv.refl FieldFour)) (ht2 : t * t = 1) : t ∈ L6 := by
  obtain ⟨ℓ, hℓ⟩ := normConj_mem_inner_of_linear hAut hZ (t := ⟨t, htN⟩) ht
  set u : MulAut W6 := (ℓ : MulAut W6)⁻¹ * t with hu
  have hcomm : ∀ x ∈ L6, u * x = x * u := by
    intro x hx
    have h := congrArg (fun φ : MulAut ↥L6 => ((φ ⟨x, hx⟩ : ↥L6) : MulAut W6)) hℓ
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, normConj_apply] at h
    calc u * x = (ℓ : MulAut W6)⁻¹ * (t * x * t⁻¹) * t := by rw [hu]; group
      _ = (ℓ : MulAut W6)⁻¹ * (ℓ * x * (ℓ : MulAut W6)⁻¹) * t := by rw [← h]
      _ = x * u := by rw [hu]; group
  obtain ⟨c, hc⟩ := exists_smul_of_comm hcomm
  have ht' : t = ℓ * u := by rw [hu]; group
  have hℓu : (ℓ : MulAut W6) * u = u * ℓ := (hcomm ℓ ℓ.2).symm
  have hsq : ((ℓ : MulAut W6) * ℓ) * (u * u) = 1 := by
    calc ((ℓ : MulAut W6) * ℓ) * (u * u) = (ℓ * u) * (ℓ * u) := by
          calc ((ℓ : MulAut W6) * ℓ) * (u * u) = ℓ * ((ℓ * u) * u) := by group
            _ = ℓ * ((u * ℓ) * u) := by rw [hℓu]
            _ = (ℓ * u) * (ℓ * u) := by group
      _ = 1 := by rw [← ht', ht2]
  have hℓ2 : ℓ * ℓ ∈ Subgroup.center ↥L6 := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have e : ((ℓ * ℓ : ↥L6) : MulAut W6) = (u * u)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    simp only [Subgroup.coe_mul]
    rw [show (ℓ : MulAut W6) * ℓ = ((ℓ * ℓ : ↥L6) : MulAut W6) from rfl, e]
    have hy := hcomm y y.2
    have hy' : (u * u) * y = y * (u * u) := by
      calc (u * u) * y = u * (u * y) := by group
        _ = u * (y * u) := by rw [hy]
        _ = (u * y) * u := by group
        _ = (y * u) * u := by rw [hy]
        _ = y * (u * u) := by group
    calc (y : MulAut W6) * (u * u)⁻¹ = (u * u)⁻¹ * ((u * u) * y) * (u * u)⁻¹ := by group
      _ = (u * u)⁻¹ * (y * (u * u)) * (u * u)⁻¹ := by rw [hy']
      _ = (u * u)⁻¹ * y := by group
  rw [hZ, Subgroup.mem_bot] at hℓ2
  have huu : u * u = 1 := by
    have e : ((ℓ * ℓ : ↥L6) : MulAut W6) = 1 := by rw [hℓ2]; rfl
    simp only [Subgroup.coe_mul] at e
    rw [e, one_mul] at hsq
    exact hsq
  have hc2 : c * c = 1 := by
    have h1 := congrArg (fun y => toAddMap y v0.toVec) huu
    simp only [toAddMap_mul, hc, toAddMap_one, smul_smul] at h1
    have h2 : (c * c - 1) • v0.toVec = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 toVec_v0_ne
  have hc1 : c = 1 := by
    have key : ∀ d : FieldFour, d * d = 1 → d = 1 := by decide
    exact key c hc2
  have hu1 : u = 1 := toAddMap_injective fun v => by rw [hc, hc1, one_smul, toAddMap_one]
  rw [ht', hu1, mul_one]
  exact ℓ.2

end Index

end CFSG.Quasithin.J2Row
