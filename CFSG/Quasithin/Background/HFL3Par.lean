module

public import CFSG.Quasithin.Background.HFL3Exp
public import CFSG.Quasithin.Background.HFL3Lift

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag SU3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem commutator_mem_linImg (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {x y : MulAut (HMod n K)} (hx : x ∈ norm hK) (hy : y ∈ norm hK) :
    x * y * x⁻¹ * y⁻¹ ∈ linImg hK := by
  obtain ⟨A, σ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK hx
  obtain ⟨B, τ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK hy
  obtain ⟨fr, -, -, htop, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega : 1 ≤ 2 * n)
      (SU3.card_eq_two_pow hK)
  have hστ : σ * τ = τ * σ := by
    have hσ : σ ∈ Subgroup.zpowers fr := htop ▸ Subgroup.mem_top σ
    have hτ : τ ∈ Subgroup.zpowers fr := htop ▸ Subgroup.mem_top τ
    obtain ⟨i, rfl⟩ := hσ
    obtain ⟨j, rfl⟩ := hτ
    exact (Commute.zpow_zpow_self fr i j).eq
  have hc : Commute (fldAut (n := n) τ) (fldAut σ) := by
    show fldAut τ * fldAut σ = fldAut σ * fldAut τ
    rw [← fldAut_mul, ← fldAut_mul, hστ]
  have key : rhoT hK A * fldAut σ * (rhoT hK B * fldAut τ) * (rhoT hK A * fldAut σ)⁻¹ *
      (rhoT hK B * fldAut τ)⁻¹ = rhoT hK A * (fldAut σ * rhoT hK B * (fldAut σ)⁻¹) *
        (fldAut τ * rhoT hK A⁻¹ * (fldAut τ)⁻¹) * (rhoT hK B)⁻¹ := by
    rw [map_inv (rhoT hK) A]
    simp only [_root_.mul_inv_rev, mul_assoc]
    rw [← mul_assoc (fldAut τ) (fldAut σ)⁻¹, hc.inv_right.eq, mul_assoc]
  rw [key, fldAut_conj_rhoT, fldAut_conj_rhoT]
  exact mul_mem (mul_mem (mul_mem ⟨A, rfl⟩ ⟨_, rfl⟩) ⟨_, rfl⟩) (inv_mem ⟨B, rfl⟩)

theorem mem_img_of_isPGroup_zpowers (hK : Nat.card K = (2 ^ n) ^ 2) {w : MulAut (HMod n K)}
    (hw : w ∈ linImg hK) (h2 : IsPGroup 2 (Subgroup.zpowers w)) : w ∈ img hK :=
  le_img_of_isPGroup hK ((Subgroup.zpowers_le).2 hw) h2 (Subgroup.mem_zpowers w)

theorem exists_mul_eq_of_normalizes (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hP2 : IsPGroup 2 P) {C : GL (Fin 3) K}
    (hC : rhoT hK C ∈ Subgroup.normalizer ((P.map (rho hK) : Subgroup (MulAut (HMod n K))) :
      Set (MulAut (HMod n K)))) {p : SpecialLinearGroup (Fin 3) K} (hp : p ∈ P) :
    ∃ p' ∈ P, SpecialLinearGroup.toGL p * C = C * SpecialLinearGroup.toGL p' := by
  have h1 : (rhoT hK C)⁻¹ * rho hK p * ((rhoT hK C)⁻¹)⁻¹ ∈ P.map (rho hK) :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hC) _).mp ⟨p, hp, rfl⟩
  obtain ⟨p', hp', hpe⟩ := h1
  refine ⟨p', hp', ?_⟩
  set a := SpecialLinearGroup.toGL p with ha
  set a' := SpecialLinearGroup.toGL p' with ha'
  set Z := C⁻¹ * a * C * a'⁻¹ with hZ
  have hZ1 : rhoT hK Z = 1 := by
    have e1 : rhoT hK a = rho hK p := rfl
    have e2 : rhoT hK a' = rho hK p' := rfl
    rw [hZ, map_mul, map_mul, map_mul, map_inv, map_inv, e1, e2, hpe, inv_inv]
    group
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK hZ1
  have hZc : Commute Z a' := Units.ext (by
    show (Z : Matrix (Fin 3) (Fin 3) K) * a' = a' * Z
    rw [hd, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
  have hpow : ∀ q ∈ P, ∃ k : ℕ, SpecialLinearGroup.toGL q ^ 2 ^ k = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := hP2 ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow, this, map_one]
  obtain ⟨k₁, hk₁⟩ := hpow p hp
  obtain ⟨k₂, hk₂⟩ := hpow p' hp'
  have hak : a ^ 2 ^ (k₁ + k₂) = 1 := by rw [pow_add, pow_mul, hk₁, one_pow]
  have ha'k : a' ^ 2 ^ (k₁ + k₂) = 1 := by rw [pow_add, mul_comm, pow_mul, hk₂, one_pow]
  have he : C⁻¹ * a * C = Z * a' := by rw [hZ]; group
  have hZk : Z ^ 2 ^ (k₁ + k₂) = 1 := by
    have h1 : (C⁻¹ * a * C) ^ 2 ^ (k₁ + k₂) = 1 := by
      have h2 : (C⁻¹ * a * C⁻¹⁻¹) ^ 2 ^ (k₁ + k₂) = C⁻¹ * a ^ 2 ^ (k₁ + k₂) * C⁻¹⁻¹ := conj_pow
      rw [inv_inv] at h2
      rw [h2, hak, mul_one, inv_mul_cancel]
    rw [he, hZc.mul_pow, ha'k, mul_one] at h1
    exact h1
  have hZ1' : Z = 1 := eq_one_of_scalar_of_pow hd hZk
  rw [hZ1', one_mul] at he
  calc a * C = C * (C⁻¹ * a * C) := by group
    _ = C * a' := by rw [he]

theorem pow_four_mul_card_sq_of_normalizes (hK : Nat.card K = (2 ^ n) ^ 2) {C : GL (Fin 3) K}
    {R : Subgroup (MulAut (HMod n K))} (hR : R ≤ img hK) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hC : rhoT hK C ∈ Subgroup.normalizer (R : Set (MulAut (HMod n K)))) :
    rhoT hK C ^ (4 * Nat.card K ^ 2) = rhoT hK C ^ 4 := by
  classical
  obtain ⟨g, P, hPU, hP2, -, hmap⟩ := exists_conj_uni3 hK (hR.trans (img_le_linImg hK)) hR2
  set c := rho hK g with hc
  set C' := SpecialLinearGroup.toGL g * C * (SpecialLinearGroup.toGL g)⁻¹ with hC'
  have hc' : rhoT hK C' = c * rhoT hK C * c⁻¹ := by
    rw [hC', map_mul, map_mul, map_inv]
    rfl
  have hC'N : rhoT hK C' ∈ Subgroup.normalizer
      ((P.map (rho hK) : Subgroup (MulAut (HMod n K))) : Set (MulAut (HMod n K))) := by
    rw [hmap, ← Subgroup.map_equiv_normalizer_eq R (MulAut.conj c)]
    exact ⟨rhoT hK C, hC, (MulAut.conj_apply c _).trans hc'.symm⟩
  let W : Submodule K (Fin 3 → K) :=
    { carrier := {v | ∀ p ∈ P, (p : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
      add_mem' := fun {u v} hu hv p hp => by
        show (p : Matrix (Fin 3) (Fin 3) K) *ᵥ (u + v) = u + v
        rw [Matrix.mulVec_add, hu p hp, hv p hp]
      zero_mem' := fun p _ => Matrix.mulVec_zero _
      smul_mem' := fun a v hv p hp => by
        show (p : Matrix (Fin 3) (Fin 3) K) *ᵥ (a • v) = a • v
        rw [Matrix.mulVec_smul, hv p hp] }
  have hCW : ∀ v ∈ W, (C' : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro v hv p hp
    obtain ⟨p', hp', hpe⟩ := exists_mul_eq_of_normalizes hK hP2 hC'N hp
    have h1 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) *ᵥ v) hpe
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h1
    have h2 : ((SpecialLinearGroup.toGL p' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v :=
      hv p' hp'
    rw [h2] at h1
    exact h1
  have he₀ : (Pi.single 0 1 : Fin 3 → K) ∈ W := by
    intro p hp
    obtain ⟨x00, -, -, x10, x20, -⟩ := uni3_entries (hPU hp)
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, x00, x10, x20]
  have hP1 : ∃ p ∈ P, p ≠ 1 := by
    by_contra h
    push Not at h
    apply hR1
    have hPb : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 h
    have : R.map (MulAut.conj c).toMonoidHom = ⊥ := by rw [← hmap, hPb, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c).injective).mp this
  obtain ⟨p₀, hp₀, hp₀1⟩ := hP1
  have hWt : W ≠ ⊤ := by
    intro hW
    apply hp₀1
    have h1 : ∀ v : Fin 3 → K, (p₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := fun v =>
      (show v ∈ W from hW ▸ Submodule.mem_top) p₀ hp₀
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have := congrFun (h1 (Pi.single j 1)) i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    rw [this]
    exact (Matrix.one_apply (n := Fin 3) (α := K) (i := i) (j := j)).symm
  have hfin3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hW₁ : Module.finrank K W ≤ 2 := by
    have := Submodule.finrank_lt hWt
    omega
  have hW₂ : Module.finrank K ((Fin 3 → K) ⧸ W) ≤ 2 := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank K W ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro hb
      have h3 : (Pi.single 0 1 : Fin 3 → K) ∈ (⊥ : Submodule K (Fin 3 → K)) := hb ▸ he₀
      rw [Submodule.mem_bot] at h3
      have := congrFun h3 0
      simp at this
    omega
  have hQ : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hT := pow_four_mul_card_sq_eq hQ (Matrix.toLin' (C' : Matrix (Fin 3) (Fin 3) K)) (W := W)
    (fun v hv => by rw [Matrix.toLin'_apply]; exact hCW v hv) hW₁ hW₂
  have hM : (C' : Matrix (Fin 3) (Fin 3) K) ^ (4 * Nat.card K ^ 2) =
      (C' : Matrix (Fin 3) (Fin 3) K) ^ 4 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_pow, Matrix.toLin'_pow, hT]
  have hG : C' ^ (4 * Nat.card K ^ 2) = C' ^ 4 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hM])
  have h1 : rhoT hK C' ^ (4 * Nat.card K ^ 2) = rhoT hK C' ^ 4 := by
    rw [← map_pow, ← map_pow, hG]
  rw [hc', conj_pow, conj_pow] at h1
  exact mul_left_cancel (mul_right_cancel h1)

theorem orderOf_dvd_of_normalizes (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {x : MulAut (HMod n K)} (hx : x ∈ norm hK) (hodd : Odd (orderOf x))
    {R : Subgroup (MulAut (HMod n K))} (hR : R ≤ img hK) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hxR : x ∈ Subgroup.normalizer (R : Set (MulAut (HMod n K)))) :
    orderOf x ∣ (2 ^ (4 * n) - 1) * n := by
  obtain ⟨D, σ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK hx
  have hσm : σ ^ orderOf (rhoT hK D * fldAut σ) = 1 := by
    obtain ⟨C, hC⟩ := rhoT_mul_fldAut_pow hK D σ (orderOf (rhoT hK D * fldAut σ))
    rw [pow_orderOf_eq_one] at hC
    refine eq_one_of_fldAut_eq_rhoT hK (B := C⁻¹) ?_
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right hC.symm
  have hσ2n : σ ^ (2 * n) = 1 := by
    rw [← card_ringAut hn hK]
    exact pow_card_eq_one'
  have hσn : σ ^ n = 1 := by
    have h1 : orderOf σ ∣ orderOf (rhoT hK D * fldAut σ) := orderOf_dvd_of_pow_eq_one hσm
    have h2 : orderOf σ ∣ 2 * n := orderOf_dvd_of_pow_eq_one hσ2n
    have hcop : Nat.Coprime (orderOf σ) 2 :=
      Nat.Coprime.symm ((Nat.coprime_two_left).mpr (Odd.of_dvd_nat hodd h1))
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h2)
  obtain ⟨C, hC⟩ := rhoT_mul_fldAut_pow hK D σ n
  rw [hσn, fldAut_one, mul_one] at hC
  have hyN : rhoT hK C ∈ Subgroup.normalizer (R : Set (MulAut (HMod n K))) :=
    hC ▸ Subgroup.pow_mem _ hxR n
  have h4 := pow_four_mul_card_sq_of_normalizes hK hR hR2 hR1 hyN
  have hQ1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hy4 : rhoT hK C ^ (4 * (Nat.card K ^ 2 - 1)) = 1 := by
    have h5 : rhoT hK C ^ 4 * rhoT hK C ^ (4 * (Nat.card K ^ 2 - 1)) = rhoT hK C ^ 4 * 1 := by
      rw [← pow_add, mul_one, ← h4]
      congr 1
      omega
    exact mul_left_cancel h5
  have hyodd : Odd (orderOf (rhoT hK C)) := by
    rw [← hC]
    exact Odd.of_dvd_nat hodd (orderOf_pow_dvd n)
  have hy : rhoT hK C ^ (Nat.card K ^ 2 - 1) = 1 := by
    have h1 : orderOf (rhoT hK C) ∣ 4 * (Nat.card K ^ 2 - 1) := orderOf_dvd_of_pow_eq_one hy4
    have hcop : Nat.Coprime (orderOf (rhoT hK C)) 4 := by
      have h2 : Nat.Coprime (orderOf (rhoT hK C)) 2 :=
        Nat.Coprime.symm ((Nat.coprime_two_left).mpr hyodd)
      exact Nat.Coprime.pow_right 2 h2
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h1)
  have hQ2 : Nat.card K ^ 2 = 2 ^ (4 * n) := by rw [hK, ← pow_mul, ← pow_mul]; ring_nf
  have hx1 : (rhoT hK D * fldAut σ) ^ ((2 ^ (4 * n) - 1) * n) = 1 := by
    rw [mul_comm, pow_mul, hC, ← hQ2, hy]
  exact orderOf_dvd_of_pow_eq_one hx1

end CFSG.Quasithin.H.L3Nine
