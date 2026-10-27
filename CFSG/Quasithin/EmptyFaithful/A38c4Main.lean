module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.Background.HSU3Defs
public import CFSG.Quasithin.EmptyFaithful.A38c4Num
public import CFSG.Quasithin.EmptyFaithful.A38c4G2Center
import CFSG.Quasithin.EmptyFaithful.R3c6Psl

public section

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin

namespace CFSG.Quasithin.A318Excl

private theorem bijective_of_surjective_of_simple {Γ Q : Type*} [Group Γ] [Group Q]
    [IsSimpleGroup Γ] [Nontrivial Q] (π : Γ →* Q) (hπ : Function.Surjective π) :
    Function.Bijective π := by
  refine ⟨(MonoidHom.ker_eq_bot_iff π).mp ?_, hπ⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    obtain ⟨g, rfl⟩ := hπ x
    exact hx (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g))

private theorem psl3_data {X : Type} [Group X] {r e : ℕ} (h : IsPSL 3 r e X) :
    Finite X ∧ IsSimpleGroup X ∧ r.Prime ∧ 1 ≤ e ∧
      Nat.card X * Nat.gcd 3 (r ^ e - 1) =
        (r ^ e) ^ 3 * (((r ^ e) ^ 2 - 1) * ((r ^ e) ^ 3 - 1)) :=
  CFSG.Quasithin.R3c6.psl3Data h

private theorem psu3_data {X : Type} [Group X] {r e : ℕ} (h : IsPSU 3 r e X) :
    Finite X ∧ IsSimpleGroup X ∧ r.Prime ∧ 1 ≤ e ∧
      Nat.card X * Nat.gcd 3 (r ^ e + 1) =
        (r ^ e) ^ 3 * (((r ^ e) ^ 2 - 1) * ((r ^ e) ^ 3 + 1)) :=
  CFSG.Quasithin.R3c6.psu3Data h

private theorem card_center_statedSL3 {K : Type} [Field K] [Finite K] :
    Nat.card (Subgroup.center ↥(StatedSL 3 K)) = Nat.gcd (Nat.card K - 1) 3 := by
  rw [← Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 K)).toEquiv,
    Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := K) (0 : Fin 3)).toEquiv]
  simp only [Fintype.card_fin]
  exact CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd 3

private theorem center_le_scalars_of_hasScalarCommutant {K : Type} [Field K]
    {Γ : Subgroup (GL (Fin 3) K)} (hΓ : CFSG.Quasithin.H.HasScalarCommutant Γ) :
    Subgroup.center ↥Γ ≤ (StatedScalars (Fin 3) K).subgroupOf Γ := by
  intro z hz
  set M : Matrix (Fin 3) (Fin 3) K := ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  let f : (Fin 3 → K) →+ (Fin 3 → K) :=
    AddMonoidHom.mk' (fun v => M.mulVec v) (fun v w => Matrix.mulVec_add M v w)
  obtain ⟨c, hc⟩ := hΓ f (fun γ hγ v => by
    have h1 := Subgroup.mem_center_iff.mp hz ⟨γ, hγ⟩
    have h2 : ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun w : ↥Γ => ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
      simpa [hM] using this
    show M.mulVec (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v) =
      ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec (M.mulVec v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2])
  have hM' : M = Matrix.scalar (Fin 3) c := by
    ext i j
    have := congrFun (hc (Pi.single j 1)) i
    simpa [f, Matrix.mulVec_single_one, Matrix.scalar_apply, Matrix.diagonal_apply,
      Pi.single_apply, eq_comm] using this
  have hz0 : M ≠ 0 := Units.ne_zero _
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hz0
    rw [hM']
    simp
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  exact hM'.symm

private theorem center_statedSU3_eq {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Subgroup.center ↥(StatedSU 3 (p ^ f) K) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hq : (3, p ^ f) = (3, 2)
  · have hq2 : p ^ f = 2 := by simpa using hq
    have hK4 : Nat.card K = 2 ^ 2 := by rw [hK, hq2]
    have : CharP K 2 := Vol2.KGNat.charP_two_of_card (by norm_num) hK4
    have hΓ : CFSG.Quasithin.H.HasScalarCommutant (StatedSU 3 (p ^ f) K) :=
      CFSG.Quasithin.H.SU3.hasScalarCommutant hK (by rw [hq2])
    exact le_antisymm (center_le_scalars_of_hasScalarCommutant hΓ)
      (CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (p ^ f))
  · exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 3) hK
      (by norm_num) hq).2

private theorem exists_prime_pow_of_card_sq {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) : ∃ p f : ℕ, p.Prime ∧ q = p ^ f := by
  have := Fintype.ofFinite K
  have h1 : IsPrimePow (q ^ 2) := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card K
  have h2 : IsPrimePow q := (isPrimePow_pow_iff (two_ne_zero)).mp h1
  obtain ⟨p, f, hp, -, hpf⟩ := (isPrimePow_nat_iff q).mp h2
  exact ⟨p, f, hp, hpf.symm⟩

private theorem card_center_of_isSU3 {q : ℕ} {X : Type} [Group X] (h : IsSU3 q X) :
    Nat.card (Subgroup.center X) = Nat.gcd 3 (q + 1) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  obtain ⟨p, f, hp, rfl⟩ := exists_prime_pow_of_card_sq hK
  rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv, center_statedSU3_eq hp hK]
  exact (CFSG.LinearGroups.unitary_scalar_kernel hp hK (n := 3) (by norm_num)).2.2

private theorem card_center_of_isSL3 {q : ℕ} {X : Type} [Group X] (h : IsSL3 q X) :
    Nat.card (Subgroup.center X) = Nat.gcd (q - 1) 3 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv, card_center_statedSL3, hK]

theorem card_center_of_A318Case3Group {X : Type} [Group X] (h : A318Case3Group X) :
    Nat.card (Subgroup.center X) = 3 := by
  rcases h with ⟨s, q, hmod, hX⟩ | h6 | h7 | hM
  · cases s
    · rw [card_center_of_isSU3 (q := q) hX]
      have h3 : 3 ∣ q + 1 := by
        simp only [Bool.false_eq_true, ↓reduceIte] at hmod
        unfold Int.ModEq at hmod
        omega
      exact Nat.gcd_eq_left h3
    · rw [card_center_of_isSL3 (q := q) hX]
      have h3 : 3 ∣ q - 1 := by
        simp only [↓reduceIte] at hmod
        unfold Int.ModEq at hmod
        omega
      exact Nat.gcd_eq_right h3
  · exact h6.2.1
  · exact h7.2.1
  · exact hM.2.1

private theorem sixteen_le_two_pow_two_mul_of_two_le {n : ℕ} (hn : 2 ≤ n) : 16 ≤ 2 ^ (2 * n) := by
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem card_sp4_form {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSp 2 K) =
      (2 ^ (2 * n)) ^ 2 * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n)) ^ 2 - 1)) := by
  rw [Vol2.Ch10.SecA.card_Sp4_pow hK]
  have : (2 ^ (2 * n)) ^ 2 = 2 ^ (4 * n) := by rw [← pow_mul]; congr 1; ring
  rw [this]

private theorem card_g2_form {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ =
      (2 ^ (2 * n)) ^ 3 * (((2 ^ (2 * n)) ^ 3 - 1) * (2 ^ (2 * n) - 1)) := by
  rw [Vol2.KGNat.factG2DerivedOrder_holds K n hn hK]
  have h6 : (2 ^ n) ^ 6 = (2 ^ (2 * n)) ^ 3 := by rw [← pow_mul, ← pow_mul]; congr 1; ring
  have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul]; congr 1; ring
  rw [h6, h2]

private theorem one_lt_sp4_form {y : ℕ} (hy : 16 ≤ y) : 1 < y ^ 2 * ((y - 1) * (y ^ 2 - 1)) := by
  have h4 : 16 ≤ y ^ 2 := by nlinarith
  have h1 : 1 ≤ y - 1 := by omega
  have h2 : 1 ≤ y ^ 2 - 1 := by omega
  have h3 : 0 < (y - 1) * (y ^ 2 - 1) := Nat.mul_pos h1 h2
  calc 1 < y ^ 2 := by omega
    _ = y ^ 2 * 1 := (mul_one _).symm
    _ ≤ y ^ 2 * ((y - 1) * (y ^ 2 - 1)) := Nat.mul_le_mul_left _ h3

private theorem one_lt_g2_form {y : ℕ} (hy : 16 ≤ y) :
    1 < y ^ 3 * ((y ^ 3 - 1) * (y - 1)) := by
  have h4 : 16 ≤ y ^ 3 := hy.trans (Nat.le_self_pow (by norm_num) y)
  have h1 : 1 ≤ y - 1 := by omega
  have h2 : 1 ≤ y ^ 3 - 1 := by omega
  have h3 : 0 < (y ^ 3 - 1) * (y - 1) := Nat.mul_pos h2 h1
  calc 1 < y ^ 3 := by omega
    _ = y ^ 3 * 1 := (mul_one _).symm
    _ ≤ y ^ 3 * ((y ^ 3 - 1) * (y - 1)) := Nat.mul_le_mul_left _ h3

private theorem not_surjective_of_isPSLEps3 {G : Type} [Group G] [Nontrivial G] {N : ℕ}
    (hG : Nat.card G = N)
    (hL : ∀ Q : ℕ, (∃ r e : ℕ, r.Prime ∧ 1 ≤ e ∧ Q = r ^ e) →
      Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) ≠ Nat.gcd 3 (Q - 1) * N)
    (hU : ∀ Q : ℕ, (∃ r e : ℕ, r.Prime ∧ 1 ≤ e ∧ Q = r ^ e) →
      Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) ≠ Nat.gcd 3 (Q + 1) * N)
    {X : Type} [Group X] {s : Bool} {r e : ℕ} (h : IsPSLEps3 s r e X) (f : X →* G) :
    ¬ Function.Surjective f := by
  intro hf
  cases s
  · obtain ⟨-, hsimp, hr, he, heq⟩ := psu3_data (r := r) (e := e) h
    have hb := @bijective_of_surjective_of_simple X G _ _ hsimp _ f hf
    have hcard : Nat.card X = N := (Nat.card_congr (Equiv.ofBijective f hb)).trans hG
    exact hU (r ^ e) ⟨r, e, hr, he, rfl⟩ (by rw [← heq, hcard, mul_comm])
  · obtain ⟨-, hsimp, hr, he, heq⟩ := psl3_data (r := r) (e := e) h
    have hb := @bijective_of_surjective_of_simple X G _ _ hsimp _ f hf
    have hcard : Nat.card X = N := (Nat.card_congr (Equiv.ofBijective f hb)).trans hG
    exact hL (r ^ e) ⟨r, e, hr, he, rfl⟩ (by rw [← heq, hcard, mul_comm])

private theorem center_statedSp_eq_bot {K : Type} [Field K] [CharP K 2] (n : ℕ) :
    Subgroup.center ↥(StatedSp n K) = ⊥ := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
    CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq,
    ← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
  exact CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot n

end CFSG.Quasithin.A318Excl

namespace CFSG.Quasithin

theorem factA318Excl_holds : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl := by
  refine ⟨?_, fun X _ _ h => A318Excl.card_center_of_A318Case3Group h⟩
  intro K _ _ n hn hK
  have hcp : CharP K 2 := Vol2.KGNat.charP_two_of_card (by omega) hK
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc0, hc1⟩ := Vol2.KGNat.exists_ne_zero_ne_one (K := K) (by rw [hK]; omega)
  have hy := A318Excl.sixteen_le_two_pow_two_mul_of_two_le hn
  have hSp : Nontrivial ↥(StatedSp 2 K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, A318Excl.card_sp4_form hK]
    exact A318Excl.one_lt_sp4_form hy
  have hG2 : Nontrivial ↥⁅quasithinG2 K, quasithinG2 K⁆ := by
    rw [← Finite.one_lt_card_iff_nontrivial, A318Excl.card_g2_form hn hK]
    exact A318Excl.one_lt_g2_form hy
  refine ⟨A318Excl.center_statedSp_eq_bot 2,
    A318Excl.center_commutator_quasithinG2_eq_bot hc0 hc1, ?_⟩
  intro X _ s r e h
  refine ⟨fun f => ?_, fun f => ?_⟩
  · exact A318Excl.not_surjective_of_isPSLEps3 (A318Excl.card_sp4_form hK)
      (fun Q hQ => A318Excl.no_psl3_sp4 hn hQ) (fun Q hQ => A318Excl.no_psu3_sp4 hn hQ) h f
  · exact A318Excl.not_surjective_of_isPSLEps3 (A318Excl.card_g2_form hn hK)
      (fun Q hQ => A318Excl.no_psl3_g2 hn hQ) (fun Q hQ => A318Excl.no_psu3_g2 hn hQ) h f

end CFSG.Quasithin
