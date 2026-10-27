module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix

theorem apply_commutator_eq_of_mem_center {S : Type*} [Group S] (ν : MulAut S) {x y zx zy : S}
    (hzx : zx ∈ Subgroup.center S) (hzy : zy ∈ Subgroup.center S) (hx : ν x = zx * x)
    (hy : ν y = zy * y) : ν (x * y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by
  have cx : ∀ g, g * zx = zx * g := Subgroup.mem_center_iff.mp hzx
  have cy : ∀ g, g * zy = zy * g := Subgroup.mem_center_iff.mp hzy
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy]
  have e1 : x * (zy * y) = zy * (x * y) := by rw [← mul_assoc, cy x, mul_assoc]
  have hA : zx * x * (zy * y) * (zx * x)⁻¹ = zy * (x * y * x⁻¹) := by
    calc zx * x * (zy * y) * (zx * x)⁻¹ = zx * (x * (zy * y) * x⁻¹) * zx⁻¹ := by group
      _ = x * (zy * y) * x⁻¹ := by rw [← cx, mul_inv_cancel_right]
      _ = zy * (x * y * x⁻¹) := by rw [e1]; group
  calc zx * x * (zy * y) * (zx * x)⁻¹ * (zy * y)⁻¹ = zy * (x * y * x⁻¹) * (zy * y)⁻¹ := by
        rw [hA]
    _ = zy * (x * y * x⁻¹ * y⁻¹) * zy⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [← cy, mul_inv_cancel_right]

section Field

variable {K : Type} [Field K]

theorem diag3_one_cube_mem (h : UnitaryFieldData 2 3 K) {τ : Kˣ} (hτ3 : τ ^ 3 = 1) :
    diag3 1 τ (τ ^ 2) ∈ unitarySU 2 3 K 3 := by
  have h9 : ∀ x : Kˣ, x ^ 3 = 1 → x ^ (2 ^ 3 + 1) = 1 := fun x hx => by
    rw [show 2 ^ 3 + 1 = 3 * 3 by norm_num, pow_mul, hx, one_pow]
  refine diag3_mem_unitarySU h (one_pow _) (h9 τ hτ3) (h9 _ ?_) ?_
  · rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow]
  · rw [one_mul, ← pow_succ', hτ3]

theorem conj_eq_one_of_le_fixed (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {H : Subgroup (unitarySU 2 3 K 3)} (hHC : ∀ x ∈ H, suField h σ x = x)
    (hHn : ∀ c, suField h σ c = c → ∀ x ∈ H, c * x * c⁻¹ ∈ H)
    (hH3 : ¬ 3 ∣ Nat.card
      (H.map (MulAut.conj : unitarySU 2 3 K 3 →* MulAut (unitarySU 2 3 K 3)))) :
    ∀ x ∈ H, MulAut.conj x = 1 := by
  have := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 2 < 2 ^ 3 := by norm_num
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  obtain rfl : f₀ = 1 := by omega
  have h₀ : UnitaryFieldData 2 1 (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  have hC216 : Nat.card (suIncl h h₀ hbar).range = 216 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (suIncl_injective h h₀ hbar)).toEquiv]
    exact CFSG.RankThree.CentralLiftU.card_statedSU_three_two h₀ rfl
  have hHle : H ≤ (suIncl h h₀ hbar).range := fun x hx =>
    (mem_range_suIncl_iff h h₀ hbar x).2 (hHC x hx)
  have hH216 : Nat.card H ∣ 216 := hC216 ▸ Subgroup.card_dvd_of_le hHle
  set φ : H →* MulAut (unitarySU 2 3 K 3) := MulAut.conj.comp H.subtype with hφ
  have hφrange : φ.range = H.map MulAut.conj := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hrange3 : ¬ 3 ∣ Nat.card φ.range := by rwa [hφrange]
  have hcardH : Nat.card φ.ker * Nat.card φ.range = Nat.card H := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index φ.ker
  have hrange8 : Nat.card φ.range ∣ 2 ^ 3 := by
    have h1 : Nat.card φ.range ∣ 2 ^ 3 * 3 ^ 3 :=
      dvd_trans ⟨Nat.card φ.ker, by rw [mul_comm]; exact hcardH.symm⟩ hH216
    have hcop : Nat.Coprime (Nat.card φ.range) (3 ^ 3) :=
      Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hrange3).symm
    exact hcop.dvd_of_dvd_mul_right h1
  have hZ3 : ∀ z ∈ φ.ker, z ^ 3 = 1 := by
    intro z hz
    have h1 : MulAut.conj (z : unitarySU 2 3 K 3) = 1 := hz
    obtain ⟨c, hc3, hzc⟩ := exists_scalar_of_conj_eq_one h hq h1
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one]
    rfl
  have hZp : IsPGroup 3 φ.ker := fun z => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hZ3 _ z.2)⟩
  have hZcop : Nat.Coprime (Nat.card φ.ker) φ.ker.index := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZp
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrange8
    rw [Subgroup.index_ker, hm, hj]
    exact Nat.Coprime.pow m j (by norm_num)
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime hZcop
  have hQcard : Nat.card Q = Nat.card φ.range := by
    have h1 := hQ.card_mul_card
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hcardH.symm)
  have hQ8 : ∀ q : H, q ∈ Q → q ^ 8 = 1 := by
    intro q hq
    have h1 := pow_card_eq_one' (G := Q) (x := ⟨q, hq⟩)
    obtain ⟨k, hk⟩ := show Nat.card Q ∣ 8 from hQcard ▸ hrange8
    have h2 : q ^ Nat.card Q = 1 := by
      have := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [hk, pow_mul, h2, one_pow]
  have hQ2 : IsPGroup 2 Q := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrange8
    exact IsPGroup.of_card (hQcard.trans hj)
  have hQall : ∀ x : H, x ^ 8 = 1 → x ∈ Q := by
    intro x hx8
    obtain ⟨⟨z, q⟩, hzq, -⟩ := (Subgroup.isComplement'_def.mp hQ).existsUnique x
    have hz : (z : H) ∈ φ.ker := z.2
    have hq : (q : H) ∈ Q := q.2
    have hz3 := hZ3 _ hz
    have hq8 := hQ8 _ hq
    have hzq' : Commute (z : H) (q : H) := by
      have h1 : MulAut.conj ((z : H) : unitarySU 2 3 K 3) = 1 := hz
      apply Subtype.ext
      have h2 := DFunLike.congr_fun h1 ((q : H) : unitarySU 2 3 K 3)
      rw [MulAut.conj_apply, MulAut.one_apply] at h2
      change ((z : H) : unitarySU 2 3 K 3) * ((q : H) : unitarySU 2 3 K 3) =
        ((q : H) : unitarySU 2 3 K 3) * ((z : H) : unitarySU 2 3 K 3)
      calc ((z : H) : unitarySU 2 3 K 3) * ((q : H) : unitarySU 2 3 K 3) =
          ((z : H) : unitarySU 2 3 K 3) * ((q : H) : unitarySU 2 3 K 3) *
            ((z : H) : unitarySU 2 3 K 3)⁻¹ * ((z : H) : unitarySU 2 3 K 3) := by group
        _ = ((q : H) : unitarySU 2 3 K 3) * ((z : H) : unitarySU 2 3 K 3) := by rw [h2]
    have hz8 : (z : H) ^ 8 = 1 := by
      have h1 : x ^ 8 = (z : H) ^ 8 * (q : H) ^ 8 := by rw [← hzq, hzq'.mul_pow]
      rw [hq8, mul_one, hx8] at h1
      exact h1.symm
    have hz1 : (z : H) = 1 := by
      calc (z : H) = ((z : H) ^ 3) ^ 3 * ((z : H) ^ 8)⁻¹ := by group
        _ = 1 := by rw [hz3, hz8, one_pow, inv_one, one_mul]
    rw [← hzq, hz1, one_mul]
    exact hq
  have hPi : PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [h.card]; rfl⟩
  have hq3 : ModThree false (2 ^ 3) := by
    show 2 ^ 3 % 3 = 2
    norm_num
  obtain ⟨τ, hτ3, hτ1⟩ := exists_primitive_cube_root hPi
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0, zero_pow (by norm_num)] at hτ3; exact zero_ne_one hτ3
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ3,
    Units.val_one])
  set v : unitarySU 2 3 K 3 := ⟨_, diag3_one_cube_mem h hτu3⟩ with hv
  have hστ : σ τ = τ := apply_eq_of_pow_three_eq_one hσ3 hτ3
  have hvfix : suField h σ v = v := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut, hv]
    change (diagonal ![((1 : Kˣ) : K), (τu : K), ((τu ^ 2 : Kˣ) : K)]).map σ =
      diagonal ![((1 : Kˣ) : K), (τu : K), ((τu ^ 2 : Kˣ) : K)]
    rw [diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [hτu, hστ]
  have hv3 : (v : GL (Fin 3) K) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hv]
    change (diagonal ![((1 : Kˣ) : K), (τu : K), ((τu ^ 2 : Kˣ) : K)]) ^ 3 = 1
    rw [diagonal_pow, ← diagonal_one]
    congr 1
    funext i
    have hτ6 : τ ^ 6 = 1 := by rw [show 6 = 3 * 2 by norm_num, pow_mul, hτ3, one_pow]
    fin_cases i <;> simp [hτu, hτ3, hτ6, ← pow_mul]
  have hvs : ∀ c : K, ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1) hc
    simp [hv, hτu] at h0 h1
    exact hτ1 (h1.trans h0.symm)
  set X : Subgroup (GL (Fin 3) K) := (Q.map H.subtype).map (unitarySU 2 3 K 3).subtype with hX
  have hX2 : IsPGroup 2 X := (hQ2.map H.subtype).map (unitarySU 2 3 K 3).subtype
  have hXu : X ≤ glPi false 3 (2 ^ 3) K := by
    rintro _ ⟨_, ⟨q, -, rfl⟩, rfl⟩
    exact (mem_glPi_false h).2 ((mem_unitarySU_iff h).mp (q : unitarySU 2 3 K 3).2).2
  have hXv : ∀ x ∈ X, (v : GL (Fin 3) K) * x * (v : GL (Fin 3) K)⁻¹ ∈ X := by
    rintro _ ⟨_, ⟨q, hqQ, rfl⟩, rfl⟩
    have hmem : v * (q : unitarySU 2 3 K 3) * v⁻¹ ∈ H := hHn v hvfix _ q.2
    have hQmem : (⟨_, hmem⟩ : H) ∈ Q := by
      apply hQall
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (v * (q : unitarySU 2 3 K 3) * v⁻¹) ^ 8 = 1
      rw [conj_pow, show (q : unitarySU 2 3 K 3) ^ 8 = 1 from by
        have := congrArg Subtype.val (hQ8 q hqQ)
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at this, mul_one, mul_inv_cancel]
    exact ⟨_, ⟨_, hQmem, rfl⟩, rfl⟩
  have hX1 := eq_bot_of_normalizes hPi hq3 v.2 hv3 hvs hXu hX2 hXv
  have hQ1 : Nat.card Q = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro q hq
    have h1 : ((q : unitarySU 2 3 K 3) : GL (Fin 3) K) ∈ X := ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rw [hX1, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hrange1 : φ.range = ⊥ := by
    rw [← Subgroup.card_eq_one, ← hQcard, hQ1]
  intro x hx
  have h1 : φ ⟨x, hx⟩ ∈ φ.range := ⟨_, rfl⟩
  rw [hrange1, Subgroup.mem_bot] at h1
  exact h1

@[expose] def swap01Mat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def swap12Mat : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem swap01Mat_mul_self : (swap01Mat : Matrix (Fin 3) (Fin 3) K) * swap01Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap01Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12Mat_mul_self : (swap12Mat : Matrix (Fin 3) (Fin 3) K) * swap12Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap12Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem mem_unitarySU_of_perm (h : UnitaryFieldData 2 3 K) {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M * M = 1) (hMt : Mᵀ = M) (hbar : M.map h.bar = M) (hdet : M.det = 1) :
    GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero) ∈ unitarySU 2 3 K 3 := by
  refine (mem_unitarySU_iff h).mpr ⟨hdet, ?_⟩
  change (M.map h.bar)ᵀ * M = 1
  rw [hbar, hMt, hM]

theorem eq_smul_one_of_commute_swaps {P : Matrix (Fin 3) (Fin 3) K} {τ : K} (hτ1 : τ ≠ 1)
    (h01 : P * swap01Mat = swap01Mat * P) (h12 : P * swap12Mat = swap12Mat * P)
    (ht : P * (diagonal ![τ, τ ^ 2, 1] * swap01Mat) =
      (diagonal ![τ, τ ^ 2, 1] * swap01Mat) * P) :
    P = P 0 0 • 1 := by
  have e : ∀ (A B : Matrix (Fin 3) (Fin 3) K), A = B → ∀ i j, A i j = B i j :=
    fun A B hAB i j => by rw [hAB]
  have a1 := e _ _ h01 0 0
  have a2 := e _ _ h01 0 1
  have a3 := e _ _ h01 0 2
  have a4 := e _ _ h01 2 0
  have b1 := e _ _ h12 1 1
  have b2 := e _ _ h12 1 2
  have b3 := e _ _ h12 0 1
  have b4 := e _ _ h12 1 0
  have c1 := e _ _ ht 0 2
  simp [swap01Mat, Matrix.mul_apply, Fin.sum_univ_three] at a1 a2 a3 a4
  simp [swap12Mat, Matrix.mul_apply, Fin.sum_univ_three] at b1 b2 b3 b4
  simp [swap01Mat, Matrix.mul_apply, Fin.sum_univ_three] at c1
  have hβ : P 0 2 = 0 := by
    have h1 : P 0 2 * (1 - τ) = 0 := by linear_combination c1 - τ * a3
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (sub_eq_zero.mp h2).symm hτ1
  have z01 : P 0 1 = 0 := by linear_combination hβ - b3
  have z10 : P 1 0 = 0 := by linear_combination z01 - a1
  have z12 : P 1 2 = 0 := by linear_combination hβ - a3
  have z21 : P 2 1 = 0 := by linear_combination z12 - b1
  have z20 : P 2 0 = 0 := by linear_combination z21 - a4
  have d11 : P 1 1 = P 0 0 := a2.symm
  have d22 : P 2 2 = P 0 0 := b2.symm.trans d11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [z01, z10, z12, z21, z20, d11, d22, hβ]

theorem eq_bot_of_commute_suField (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {N : Subgroup (MulAut (unitarySU 2 3 K 3))}
    (hNc : ∀ ν ∈ N, ν * suField h σ = suField h σ * ν) (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ, suField h σ ℓ = ℓ → ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) :
    N = ⊥ := by
  have := h.finite
  have : CharP K 2 := h.charP
  have hq : 2 < 2 ^ 3 := by norm_num
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  set H : Subgroup (unitarySU 2 3 K 3) :=
    (suField h σ : unitarySU 2 3 K 3 ≃* unitarySU 2 3 K 3).toMonoidHom.eqLocus
      (MonoidHom.id _) ⊓ N.comap MulAut.conj with hH
  have hHcen : ∀ x ∈ H, MulAut.conj x = 1 := by
    refine conj_eq_one_of_le_fixed h hσ (H := H) (fun x hx => hx.1) (fun c hc x hx => ⟨?_, ?_⟩)
      ?_
    · change suField h σ (c * x * c⁻¹) = c * x * c⁻¹
      have hx1 : suField h σ x = x := hx.1
      rw [map_mul, map_mul, map_inv, hc, hx1]
    · change MulAut.conj (c * x * c⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hNn c hc _ hx.2
    · have hle : H.map MulAut.conj ≤ N := by
        rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      intro h3
      exact hN3 (dvd_trans h3 (Subgroup.card_dvd_of_le hle))
  have hkey : ∀ ν ∈ N, ∀ ℓ, suField h σ ℓ = ℓ →
      ∃ z ∈ Subgroup.center (unitarySU 2 3 K 3), ν ℓ = z * ℓ := by
    intro ν hν ℓ hℓ
    have hνℓ : suField h σ (ν ℓ) = ν ℓ := apply_apply_eq_of_commute (hNc ν hν) hℓ
    have hmem : ℓ * (ν ℓ)⁻¹ ∈ H := by
      refine ⟨?_, conj_mul_inv_apply_mem hν (hNn ℓ hℓ)⟩
      change suField h σ (ℓ * (ν ℓ)⁻¹) = ℓ * (ν ℓ)⁻¹
      rw [map_mul, map_inv, hℓ, hνℓ]
    have h1 := hHcen _ hmem
    refine ⟨(ℓ * (ν ℓ)⁻¹)⁻¹, ?_, by group⟩
    refine Subgroup.inv_mem _ (Subgroup.mem_center_iff.mpr fun g => ?_)
    have h2 := DFunLike.congr_fun h1 g
    rw [MulAut.conj_apply, MulAut.one_apply] at h2
    calc g * (ℓ * (ν ℓ)⁻¹) = (ℓ * (ν ℓ)⁻¹) * g * (ℓ * (ν ℓ)⁻¹)⁻¹ * (ℓ * (ν ℓ)⁻¹) := by
          rw [h2]
      _ = (ℓ * (ν ℓ)⁻¹) * g := by group
  have hPi : PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [h.card]; rfl⟩
  obtain ⟨τ, hτ3, hτ1⟩ := exists_primitive_cube_root hPi
  have hτ0 : τ ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by norm_num)] at hτ3
    exact zero_ne_one hτ3
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ3, Units.val_one])
  have hστ : σ τ = τ := apply_eq_of_pow_three_eq_one hσ3 hτ3
  have hbar01 : (swap01Mat : Matrix (Fin 3) (Fin 3) K).map h.bar = swap01Mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap01Mat]
  have hbar12 : (swap12Mat : Matrix (Fin 3) (Fin 3) K).map h.bar = swap12Mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap12Mat]
  have hdet01 : (swap01Mat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    simp [swap01Mat, Matrix.det_fin_three, CharTwo.neg_eq]
  have hdet12 : (swap12Mat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    simp [swap12Mat, Matrix.det_fin_three, CharTwo.neg_eq]
  have ht01 : (swap01Mat : Matrix (Fin 3) (Fin 3) K)ᵀ = swap01Mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap01Mat]
  have ht12 : (swap12Mat : Matrix (Fin 3) (Fin 3) K)ᵀ = swap12Mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap12Mat]
  set s01 : unitarySU 2 3 K 3 :=
    ⟨_, mem_unitarySU_of_perm h swap01Mat_mul_self ht01 hbar01 hdet01⟩ with hs01
  set s12 : unitarySU 2 3 K 3 :=
    ⟨_, mem_unitarySU_of_perm h swap12Mat_mul_self ht12 hbar12 hdet12⟩ with hs12
  set v : unitarySU 2 3 K 3 := ⟨_, diag3_one_cube_mem h hτu3⟩ with hv
  have hdτ : diag3 τu (τu ^ 2) 1 ∈ unitarySU 2 3 K 3 := by
    have h9 : ∀ x : Kˣ, x ^ 3 = 1 → x ^ (2 ^ 3 + 1) = 1 := fun x hx => by
      rw [show 2 ^ 3 + 1 = 3 * 3 by norm_num, pow_mul, hx, one_pow]
    refine diag3_mem_unitarySU h (h9 τu hτu3) (h9 _ ?_) (one_pow _) ?_
    · rw [← pow_mul, mul_comm, pow_mul, hτu3, one_pow]
    · rw [mul_one, ← pow_succ', hτu3]
  set t : unitarySU 2 3 K 3 := ⟨_, hdτ⟩ * s01 with ht
  have hzmem : GeneralLinearGroup.scalar (Fin 3) τu ∈ unitarySU 2 3 K 3 := by
    refine scalar_mem_unitarySU h (by norm_num) ?_ hτu3
    rw [h.norm_eq_pow, show 2 ^ 3 + 1 = 3 * 3 by norm_num, pow_mul, Units.val_mk0, hτ3,
      one_pow]
  set z : unitarySU 2 3 K 3 := ⟨_, hzmem⟩ with hz
  have hfixMat : ∀ ℓ : unitarySU 2 3 K 3,
      ((ℓ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
        ((ℓ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → suField h σ ℓ = ℓ := by
    intro ℓ hℓ
    apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut, hℓ]
  have hs01M : ((s01 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swap01Mat := rfl
  have hs12M : ((s12 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swap12Mat := rfl
  have hτK : ((τu : Kˣ) : K) = τ := Units.val_mk0 hτ0
  have hτ2K : ((τu ^ 2 : Kˣ) : K) = τ ^ 2 := by rw [Units.val_pow_eq_pow_val, hτK]
  have hvM : ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, τ, τ ^ 2] := by
    rw [hv]
    change diagonal ![((1 : Kˣ) : K), (τu : K), ((τu ^ 2 : Kˣ) : K)] = _
    rw [Units.val_one, hτK, hτ2K]
  have htM : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![τ, τ ^ 2, 1] * swap01Mat := by
    rw [ht, Subgroup.coe_mul, Units.val_mul, hs01M]
    change diagonal ![(τu : K), ((τu ^ 2 : Kˣ) : K), ((1 : Kˣ) : K)] * swap01Mat = _
    rw [Units.val_one, hτK, hτ2K]
  have hzM : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = τ • 1 := by
    rw [hz]
    change ((GeneralLinearGroup.scalar (Fin 3) τu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hτK, Matrix.smul_one_eq_diagonal]
  have hs01fix : suField h σ s01 = s01 := hfixMat _ (by
    rw [hs01M]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap01Mat])
  have hs12fix : suField h σ s12 = s12 := hfixMat _ (by
    rw [hs12M]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap12Mat])
  have hvfix : suField h σ v = v := hfixMat _ (by
    rw [hvM, diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [hστ])
  have htfix : suField h σ t = t := hfixMat _ (by
    rw [htM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap01Mat, Matrix.mul_apply, diagonal, hστ])
  have hπfix : suField h σ (s01 * s12) = s01 * s12 := by rw [map_mul, hs01fix, hs12fix]
  have hvπ : v * (s01 * s12) = z * ((s01 * s12) * v) := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hvM, hs01M, hs12M, hzM, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [swap01Mat, swap12Mat, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
      first
        | linear_combination (-1 : K) * hτ3
        | linear_combination hτ3
        | ring
  have hs01sq : s01 * s01 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hs01M, swap01Mat_mul_self]
    rfl
  have hs12sq : s12 * s12 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hs12M, swap12Mat_mul_self]
    rfl
  have htsq : t * t = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, htM]
    change _ = (1 : Matrix (Fin 3) (Fin 3) K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap01Mat, Matrix.mul_apply, Fin.sum_univ_three] <;>
      linear_combination hτ3
  rw [eq_bot_iff]
  intro ν hν
  rw [Subgroup.mem_bot]
  obtain ⟨B, δ, rfl⟩ := exists_suConj_mul_suField h hq ν
  have hνn : (suConj h B * suField h δ) ^ Nat.card N = 1 := by
    have h1 := pow_card_eq_one' (G := N) (x := ⟨_, hν⟩)
    exact congrArg Subtype.val h1
  have hδ2 : δ ^ 2 = 1 := sq_eq_one_of_pow_eq_one h hN3
    (pow_eq_one_of_suConj_mul_suField_pow_eq_one h hq hνn)
  have hzc : z = v * (s01 * s12) * v⁻¹ * (s01 * s12)⁻¹ := by
    rw [hvπ]
    group
  obtain ⟨zv, hzv, hνv⟩ := hkey _ hν v hvfix
  obtain ⟨zπ, hzπ, hνπ⟩ := hkey _ hν (s01 * s12) hπfix
  have hνz : (suConj h B * suField h δ) z = z := by
    rw [hzc]
    exact apply_commutator_eq_of_mem_center _ hzv hzπ hνv hνπ
  have hδτ : δ τ = τ := by
    have h1 := congrArg (fun x : unitarySU 2 3 K 3 => (x : GL (Fin 3) K)) hνz
    simp only [MulAut.mul_apply, coe_suConj, coe_suField, Subgroup.coe_inv] at h1
    have h2 : glAut δ (z : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) (Units.map (δ : K →* K) τu) := by
      apply Units.ext
      rw [coe_glAut, hzM, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal, diagonal_map (map_zero δ), Units.coe_map]
      congr 1
    rw [h2, (commute_scalar (Units.map (δ : K →* K) τu) (B : GL (Fin 3) K)).eq,
      mul_inv_cancel_right] at h1
    have h3 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
      Units.coe_map, MonoidHom.coe_ofClass, hτK, hzM, Matrix.smul_apply, one_apply_eq,
      smul_eq_mul, mul_one] at h3
    exact h3
  have hδ1 : δ = 1 := by
    rcases eq_one_or_apply_eq_pow_of_sq_eq_one h hδ2 with h1 | h1
    · exact h1
    · exfalso
      apply hτ1
      have h2 := h1 τ
      rw [hδτ] at h2
      have h3 : τ ^ 2 ^ 3 = τ ^ 2 := by
        rw [show 2 ^ 3 = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hτ3, one_pow, one_mul]
      rw [h3] at h2
      have h4 : τ * (τ - 1) = 0 := by rw [mul_sub, mul_one, ← sq, ← h2, sub_self]
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 hτ0
      · exact sub_eq_zero.mp h5
  subst hδ1
  rw [map_one, mul_one] at hν ⊢
  have hcommB : ∀ ℓ : unitarySU 2 3 K 3, suField h σ ℓ = ℓ → ℓ * ℓ = 1 →
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((ℓ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((ℓ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro ℓ hℓ hℓ2
    obtain ⟨zℓ, hzℓ, hνℓ⟩ := hkey _ hν ℓ hℓ
    have hc : ∀ g, g * zℓ = zℓ * g := Subgroup.mem_center_iff.mp hzℓ
    have hz2 : zℓ * zℓ = 1 := by
      have h1 : suConj h B (ℓ * ℓ) = 1 := by rw [hℓ2, map_one]
      rw [map_mul, hνℓ] at h1
      calc zℓ * zℓ = zℓ * zℓ * (ℓ * ℓ) := by rw [hℓ2, mul_one]
        _ = zℓ * (zℓ * ℓ) * ℓ := by group
        _ = zℓ * (ℓ * zℓ) * ℓ := by rw [← hc ℓ]
        _ = zℓ * ℓ * (zℓ * ℓ) := by group
        _ = 1 := h1
    have hz1 : zℓ = 1 := by
      have hcz : MulAut.conj zℓ = 1 := MulEquiv.ext fun g => by
        rw [MulAut.conj_apply, MulAut.one_apply, ← hc g, mul_inv_cancel_right]
      obtain ⟨c, hc3, hzc⟩ := exists_scalar_of_conj_eq_one h hq hcz
      have hz3 : zℓ ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one]
        rfl)
      calc zℓ = zℓ ^ 3 * (zℓ * zℓ)⁻¹ := by group
        _ = 1 := by rw [hz3, hz2, inv_one, one_mul]
    rw [hz1, one_mul] at hνℓ
    have h1 := congrArg (fun x : unitarySU 2 3 K 3 => (x : GL (Fin 3) K)) hνℓ
    simp only [coe_suConj, Subgroup.coe_inv] at h1
    have h2 : (B : GL (Fin 3) K) * ℓ = ℓ * B := by
      calc (B : GL (Fin 3) K) * ℓ = (B : GL (Fin 3) K) * ℓ * (B : GL (Fin 3) K)⁻¹ * B := by
            group
        _ = ℓ * B := by rw [h1]
    have h3 := congrArg Units.val h2
    rwa [Units.val_mul, Units.val_mul] at h3
  have h01 := hcommB s01 hs01fix hs01sq
  have h12 := hcommB s12 hs12fix hs12sq
  have htt := hcommB t htfix htsq
  rw [hs01M] at h01
  rw [hs12M] at h12
  rw [htM] at htt
  have hP := eq_smul_one_of_commute_swaps hτ1 h01 h12 htt
  set b := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 with hb
  have hb0 : b ≠ 0 := fun hb0 => by
    have h1 := (B : GL (Fin 3) K).ne_zero
    rw [hP, hb0, zero_smul] at h1
    exact h1 rfl
  set bu : Kˣ := Units.mk0 b hb0 with hbu
  have hBs : (B : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) bu := by
    apply Units.ext
    rw [hP, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hbu, Units.val_mk0,
      Matrix.smul_one_eq_diagonal]
  have hsc : GeneralLinearGroup.scalar (Fin 3) bu ∈ unitaryIsom3 h := hBs ▸ B.2
  have hB : B = ⟨_, hsc⟩ := Subtype.ext hBs
  rw [hB]
  exact suConj_scalar_eq_one h hsc

end Field

end CFSG.RankThree.PartTwo.KFacts
