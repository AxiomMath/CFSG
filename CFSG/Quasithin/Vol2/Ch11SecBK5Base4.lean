module

public import CFSG.Quasithin.Background.HSL3PairNPrime
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base1
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base2
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank K8
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {K : Type} [Field K]


@[expose] noncomputable def dgRho : Matrix.SpecialLinearGroup (Fin 3) K →* MulAut (W6 K) :=
  (matHom.comp dgHom).comp Matrix.SpecialLinearGroup.toGL

theorem dgRho_injective : Function.Injective (dgRho (K := K)) := fun _ _ h =>
  Matrix.SpecialLinearGroup.toGL_injective (matAut_dgHom_injective h)

theorem range_dgRho : (dgRho (K := K)).range = diagSL K := by
  rw [dgRho, MonoidHom.range_comp, diagSL, statedSL_eq_range_toGL]

theorem dgRho_mem_diagSL (g : Matrix.SpecialLinearGroup (Fin 3) K) : dgRho g ∈ diagSL K := by
  rw [← range_dgRho]
  exact ⟨g, rfl⟩

noncomputable abbrev tau (K : Type) [Field K] : GL (Fin 3) K × GL (Fin 2) K →* MulAut (W6 K) :=
  matHom.comp tensHom

theorem tau_apply (p : GL (Fin 3) K × GL (Fin 2) K) : tau K p = matAut (tensHom p) := rfl

theorem tau_eq_one {p : GL (Fin 3) K × GL (Fin 2) K} (h : tau K p = 1) : tensHom p = 1 :=
  matHom_injective (h.trans (map_one matHom).symm)

theorem fst_eq_smul_of_tens_eq {A A' : GL (Fin 3) K} {M M' : GL (Fin 2) K}
    (h : tensHom (A, M) = tensHom (A', M')) :
    ∃ ν : K, ν ≠ 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) = ν • (A' : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : tensHom (A * A'⁻¹, M * M'⁻¹) = 1 := by
    have e : (A * A'⁻¹, M * M'⁻¹) = (A, M) * (A', M')⁻¹ := rfl
    rw [e, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨ν, hν, -, hA⟩ := tens_eq_one h1
  refine ⟨ν⁻¹, inv_ne_zero hν, ?_⟩
  have e : (A : Matrix (Fin 3) (Fin 3) K) =
      ((A * A'⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A' := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  rw [e, hA, Matrix.smul_mul, one_mul]

theorem pow_eq_one_of_lin [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {B₁ : Subgroup (MulAut (W6 K))} (hBN : B₁ ≤ normD K) (hBL : B₁ ≤ linSub)
    (hBab : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a) (hBodd : Odd (Nat.card B₁))
    (hBU : (B₁ : Set (MulAut (W6 K))) * ((Tri.uni3 K).map (matHom.comp dgHom) :
      Subgroup (MulAut (W6 K))) =
      ((Tri.uni3 K).map (matHom.comp dgHom) : Subgroup (MulAut (W6 K))) * B₁)
    {x : MulAut (W6 K)} (hx : x ∈ B₁) : x ^ (Nat.card K ^ 2 - 1) = 1 := by
  classical
  have : Finite (MulAut (W6 K)) := MulEquiv.finite_left
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set Bh := B₁.comap (tau K) with hBh
  set Bt := Bh.map (MonoidHom.fst _ _) with hBt
  have hrange : ∀ y ∈ B₁, ∃ p : GL (Fin 3) K × GL (Fin 2) K, tau K p = y := fun y hy => by
    obtain ⟨A, M, rfl⟩ := exists_tensHom (hBN hy) (hBL hy)
    exact ⟨(A, M), rfl⟩
  have hker : ∀ p : GL (Fin 3) K × GL (Fin 2) K, tensHom p = 1 → p ∈ Bh := fun p hp => by
    change tau K p ∈ B₁
    rw [tau_apply, hp]
    have h1 : matAut (1 : GL I6 K) = 1 := map_one (matHom : GL I6 K →* MulAut (StdMod I6 K))
    rw [h1]
    exact B₁.one_mem
  have hBtab : ∀ a ∈ Bt, ∀ b ∈ Bt, a * b = b * a := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
    have h1 := hBab _ hp _ hp'
    have h2 : tensHom p * tensHom p' = tensHom p' * tensHom p := by
      apply matHom_injective
      rw [map_mul, map_mul]
      exact h1
    exact fst_comm h2
  set k := Nat.card B₁ with hk
  have hpowk : ∀ p ∈ Bh, ∃ ν : K, ν ≠ 0 ∧ ((p.2 ^ k : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = ν • 1 ∧ ((p.1 ^ k : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ν⁻¹ • 1 := by
    intro p hp
    have h1 : tau K p ^ k = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B₁ hp)
    rw [← map_pow] at h1
    exact tens_eq_one (tau_eq_one h1)
  have hBtodd : Odd (Nat.card Bt) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨a, ha2⟩ := exists_prime_orderOf_dvd_card' 2 hev
    obtain ⟨p, hp, hpa⟩ := a.2
    have hA2' : orderOf p.1 = 2 := by
      have h5 := congrArg orderOf hpa
      rw [Subgroup.orderOf_coe, ha2] at h5
      exact h5
    obtain ⟨ν, hν, -, hp1⟩ := hpowk p hp
    have h1 : p.1 ^ (k * (Nat.card K - 1)) = 1 := by
      apply Units.ext
      have := Fintype.ofFinite K
      rw [pow_mul, Units.val_pow_eq_pow_val, hp1, smul_pow, one_pow, Units.val_one,
        Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one _ (inv_ne_zero hν),
        one_smul]
    have h2 : orderOf p.1 ∣ k * (Nat.card K - 1) := orderOf_dvd_of_pow_eq_one h1
    rw [hA2'] at h2
    have hq : Odd (Nat.card K - 1) := by
      rw [hK]
      have h3 : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
      have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      obtain ⟨r, hr⟩ := h3
      exact ⟨r - 1, by omega⟩
    exact absurd (hBodd.mul hq) (by rw [Nat.not_odd_iff_even]; exact even_iff_two_dvd.mpr h2)
  have hBtU : (Bt : Set (GL (Fin 3) K)) * (Tri.uni3 K : Set (GL (Fin 3) K)) =
      (Tri.uni3 K : Set (GL (Fin 3) K)) * Bt := by
    apply SL3Pair.mul_comm_of_subset
    rintro _ ⟨u, hu, A, ⟨p, hp, rfl⟩, rfl⟩
    have h1 : matAut (dgHom u) * tau K p ∈
        ((Tri.uni3 K).map (matHom.comp dgHom) : Set (MulAut (W6 K))) * B₁ :=
      Set.mul_mem_mul ⟨u, hu, rfl⟩ hp
    rw [← hBU] at h1
    obtain ⟨b, hb, _, ⟨u', hu', rfl⟩, hbu⟩ := h1
    obtain ⟨p', rfl⟩ := hrange b hb
    have h2 : tensHom ((u, 1) * p) = tensHom (p' * (u', 1)) := by
      apply matHom_injective
      rw [map_mul, map_mul, map_mul, map_mul]
      exact hbu.symm
    have h2' : tensHom (u * p.1, p.2) = tensHom (p'.1 * u', p'.2) := by
      have e1 : ((u, 1) * p : GL (Fin 3) K × GL (Fin 2) K) = (u * p.1, p.2) :=
        Prod.ext rfl (one_mul _)
      have e2 : (p' * (u', 1) : GL (Fin 3) K × GL (Fin 2) K) = (p'.1 * u', p'.2) :=
        Prod.ext rfl (mul_one _)
      rw [← e1, ← e2]
      exact h2
    obtain ⟨ν, hν, hA⟩ := fst_eq_smul_of_tens_eq h2'
    set c := Matrix.GeneralLinearGroup.mkOfDetNeZero (ν • (1 : Matrix (Fin 3) (Fin 3) K))
      (by rw [Matrix.det_smul, Matrix.det_one]; simp [hν]) with hc
    set d := Matrix.GeneralLinearGroup.mkOfDetNeZero (ν⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K))
      (by rw [Matrix.det_smul, Matrix.det_one]; simp [hν]) with hd
    have hcd : (c, d) ∈ Bh := by
      refine hker _ (Units.ext ?_)
      rw [coe_tensHom, Units.val_one]
      change tensMat (ν • (1 : Matrix (Fin 3) (Fin 3) K)) (ν⁻¹ • 1) = 1
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [tensMat, Matrix.fromBlocks, Matrix.one_apply, smul_smul, inv_mul_cancel₀ hν]
    refine ⟨c * p'.1, ⟨(c, d) * p', Bh.mul_mem hcd hb, rfl⟩, u', hu', ?_⟩
    apply Units.ext
    change (ν • (1 : Matrix (Fin 3) (Fin 3) K)) * (p'.1 : Matrix (Fin 3) (Fin 3) K) *
      (u' : Matrix (Fin 3) (Fin 3) K) = ((u * p.1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hA, Units.val_mul, Matrix.smul_mul, one_mul, Matrix.smul_mul]
  have htri : Bt ≤ Tri.borGL 3 K := Tri.triangular_three hK4 hBtab hBtodd hBtU
  obtain ⟨p, rfl⟩ := hrange x hx
  have hpBh : p ∈ Bh := hx
  have hp1Bt : p.1 ∈ Bt := ⟨p, hpBh, rfl⟩
  have hodd1 : Odd (orderOf p.1) :=
    Odd.of_dvd_nat hBtodd (Subgroup.orderOf_dvd_natCard Bt hp1Bt)
  have hA := SL3Pair.pow_eq_one_of_mem_borGL (htri hp1Bt) hodd1
  obtain ⟨ν, hν, hM, -⟩ := hpowk p hpBh
  have hMq := pow_card_sq_of_odd (p.2 : Matrix (Fin 2) (Fin 2) K) hBodd hν
    (by rw [← Units.val_pow_eq_pow_val]; exact hM)
  have hq1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hM1 : p.2 ^ (Nat.card K ^ 2 - 1) = 1 := by
    have h1 : p.2 ^ (Nat.card K ^ 2 - 1) * p.2 = p.2 := by
      rw [← pow_succ, Nat.sub_add_cancel hq1]
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hMq])
    exact mul_eq_right.mp h1
  have hA1 : p.1 ^ (Nat.card K ^ 2 - 1) = 1 := by
    have e : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := K)).ne'
      rw [hr]
      have e1 : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
      rw [Nat.succ_eq_add_one, e1, Nat.add_sub_cancel, Nat.add_sub_cancel]

    rw [e, pow_mul, hA, one_pow]
  have hp : p ^ (Nat.card K ^ 2 - 1) = 1 := Prod.ext hA1 hM1
  rw [← map_pow, hp, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
