module

public import CFSG.Quasithin.Vol2.F134LieOddToral
public import CFSG.Quasithin.Vol2.F134LieOddHeisMain
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover

public section

namespace CFSG.Quasithin.F134.LieOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

namespace OddModel

variable (h : OddModel H M)
include h

theorem e9Inv [Finite K] : E9Inv (StatedProj H) := by
  intro P U hP hexp hU hidx hcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU16 : 16 ≤ Nat.card U := by
    have hS : Nat.card H = Nat.card (StatedProj H) * 3 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (scal H), h.card_scal]
    have h16 : 16 ∣ Nat.card (StatedProj H) := by
      have := h.sixteen
      rw [hS] at this
      exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) this)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hU
    have hmul := U.card_mul_index
    rw [hk] at hmul
    have hcop : Nat.Coprime (2 ^ 4) U.index :=
      Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hidx)
    have h2k : 2 ^ 4 ∣ 2 ^ k := by
      rw [← hmul] at h16
      exact hcop.dvd_of_dvd_mul_right h16
    rw [hk]
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2k
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
  have hE3 : IsPGroup 3 (P.comap (proj H)) := by
    rw [IsPGroup.iff_card]
    exact ⟨3, by rw [h.card_comap, hP]; norm_num⟩
  obtain ⟨g, hg⟩ := h.exists_conj_le_torus3_sup_cyc hE3
  set φ : StatedProj H ≃* StatedProj H := MulAut.conj (proj H g)⁻¹ with hφdef
  apply exists_invariant_of_map φ
  have hP₁ : Nat.card (P.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hP]
  have hexp₁ : ∀ x ∈ P.map φ.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hstd : ∀ x : H, proj H x ∈ P.map φ.toMonoidHom →
      (x : GL (Fin 3) K) ∈ torus3 M ⊔ Subgroup.zpowers cycGL := by
    intro x hx
    rw [Subgroup.mem_map_equiv, hφdef, MulAut.conj_symm_apply, inv_inv, ← map_inv, ← map_mul,
      ← map_mul] at hx
    have := hg (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  have hPab₁ : ∀ a ∈ P.map φ.toMonoidHom, ∀ b ∈ P.map φ.toMonoidHom, a * b = b * a := by
    intro a ha b hb
    have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P.map φ.toMonoidHom)
      (by rw [hP₁]; norm_num)
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases htor : ∀ x : H, proj H x ∈ P.map φ.toMonoidHom → (x : GL (Fin 3) K) ∈ torus3 M
  · obtain ⟨Q, hQP, hQ3, hQ⟩ := h.toral hP₁ hexp₁ htor
    exact ⟨Q, hQP, hQ3, fun α hαP _ => hQ α hαP⟩
  · push Not at htor
    obtain ⟨x₀, hx₀, hx₀T⟩ := htor
    refine h.nontoral hPab₁ hstd hx₀ hx₀T hP₁ hexp₁ (hU.map _) ?_ ?_
    · rw [Subgroup.card_map_of_injective φ.injective]
      exact hU16
    · rw [← Subgroup.map_sup, Subgroup.card_map_of_injective φ.injective,
        Subgroup.card_map_of_injective φ.injective, hcard]

end OddModel

theorem sixteen_dvd_of_odd {q : ℕ} (hq : q % 2 = 1) :
    16 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ∧ 16 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have h8 : 8 ∣ q ^ 2 - 1 := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : q ^ 2 % 8 = 1 := by
      have : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
      rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
    omega
  have h3 : q ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hq]
  have h31 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hm : 2 ∣ q ^ 3 - 1 := by omega
  have hp : 2 ∣ q ^ 3 + 1 := by omega
  constructor
  · rw [mul_assoc]
    exact Dvd.dvd.mul_left (by simpa using Nat.mul_dvd_mul h8 hm) _
  · rw [mul_assoc]
    exact Dvd.dvd.mul_left (by simpa using Nat.mul_dvd_mul h8 hp) _

theorem two_three_ne_zero {p : ℕ} [CharP K p] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp1 : p ≠ 1) :
    (2 : K) ≠ 0 ∧ (3 : K) ≠ 0 := by
  constructor
  · intro h2
    have := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h2)
    have := (Nat.dvd_prime Nat.prime_two).1 this
    omega
  · intro h3
    have := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h3)
    have := (Nat.dvd_prime Nat.prime_three).1 this
    omega

theorem exists_prim_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [card_units_eq]; exact h3)
  refine ⟨ω, by rw [← hω]; exact pow_orderOf_eq_one ω, fun h1 => ?_⟩
  rw [h1, orderOf_one] at hω
  norm_num at hω

theorem oddModel_statedSL [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1)
    (hK : Nat.card K = p) : OddModel (StatedSL 3 K) ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have hchar : CharP K p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hp2 := hp.two_le
  have hpne2 : p ≠ 2 := by omega
  have hpne3 : p ≠ 3 := by omega
  have hq1 : 1 ≤ p := by omega
  have hM : Nat.card (⊤ : Subgroup Kˣ) = p - 1 := by rw [Subgroup.card_top, card_units_eq, hK]
  obtain ⟨h2K, h3K⟩ := two_three_ne_zero (K := K) hpne2 hpne3 (by omega)
  refine ⟨monomialData_statedSL, fun _ _ _ => Subgroup.mem_top _, fun _ _ => Subgroup.mem_top _,
    ?_, ?_, h2K, h3K, exists_prim_three (by rw [hK]; omega)⟩
  · have h3e : 3 ∣ p - 1 := by omega
    rw [card_statedSL_three, hK, hM,
      ← factorization_six_mul_three (x := (p - 1) ^ 2) (pow_ne_zero 2 (by omega))]
    have e1 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      zify [hq1, Nat.one_le_pow 2 _ hq1]
      ring
    have e2 : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
      zify [hq1, Nat.one_le_pow 3 _ hq1]
      ring
    rw [e1, e2]
    exact factorization_order_eq Nat.prime_three (by norm_num) (by positivity) (by omega)
      (by omega) (by positivity)
      (fun h => hpne3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h).symm)
      (by omega) (factorization_sq_add_add_one Nat.prime_three hq1 h3e)
  · rw [card_statedSL_three, hK]
    exact (sixteen_dvd_of_odd (Nat.odd_iff.1 (hp.odd_of_ne_two hpne2))).1

theorem oddModel_statedSU [Finite K] {p : ℕ} (hp : p.Prime) (hpne2 : p ≠ 2) (hp3 : p % 3 = 2)
    (hK : Nat.card K = (p ^ 1) ^ 2) : OddModel (StatedSU 3 (p ^ 1) K) (normOne K (p ^ 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have hK' : Nat.card K = p ^ 2 := by rw [hK, pow_one]
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK'])
  have hp2 := hp.two_le
  have hpne3 : p ≠ 3 := by omega
  have hq1 : 1 ≤ p := by omega
  obtain ⟨h2K, h3K⟩ := two_three_ne_zero (K := K) hpne2 hpne3 (by omega)
  refine ⟨monomialData_statedSU, ?_, ?_, ?_, ?_, h2K, h3K, exists_prim_three ?_⟩
  · intro d hd i
    have hu := unitary_of_mem_statedSU hK hd
    rw [coe_diagHom, Matrix.diagonal_map (by simp [hp.ne_zero]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at hu
    have hii := congrFun (congrFun hu i) i
    rw [diagonal_apply_eq, Matrix.one_apply_eq] at hii
    rw [mem_normOne]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
    exact hii
  · intro c hc
    rw [mem_normOne]
    obtain ⟨k, hk⟩ : 3 ∣ p ^ 1 + 1 := by rw [pow_one]; omega
    rw [hk, pow_mul, hc, one_pow]
  · have h3e : 3 ∣ p ^ 1 + 1 := by rw [pow_one]; omega
    rw [card_statedSU_three hK, card_normOne hK, ← factorization_six_mul_three (by positivity)]
    have hq1' : 1 ≤ p ^ 1 := by rw [pow_one]; exact hq1
    have hqq : p ^ 1 ≤ (p ^ 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have e1 : (p ^ 1) ^ 2 - 1 = (p ^ 1 + 1) * (p ^ 1 - 1) := sq_sub_one_eq hq1'
    have e2 : (p ^ 1) ^ 3 + 1 = (p ^ 1 + 1) * ((p ^ 1) ^ 2 - p ^ 1 + 1) := by
      zify [hqq]
      ring
    rw [e1, e2]
    exact factorization_order_eq Nat.prime_three (by norm_num) (by positivity) (by omega)
      (by rw [pow_one]; omega) (by omega)
      (fun h => hpne3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow h)).symm)
      (by rw [pow_one]; omega) (factorization_sq_sub_add_one Nat.prime_three h3e)
  · rw [card_statedSU_three hK]
    exact (sixteen_dvd_of_odd (by rw [pow_one]; exact Nat.odd_iff.1 (hp.odd_of_ne_two hpne2))).2
  · rw [hK']
    have : p ^ 2 % 3 = 1 := by simp [Nat.pow_mod, hp3]
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega

end CFSG.Quasithin.F134.LieOdd

namespace CFSG.Quasithin.P134

open CFSG.Quasithin.F134.LieOdd CFSG.Assembly.LowTwoRank

theorem facts134E9_psl3Plus : ∀ p : ℕ, p.Prime → p % 3 = 1 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1 := by
  intro p hp hp3
  refine noE9Config_of_e9Inv fun X _ hX => ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  exact E9Inv.of_mulEquiv e (oddModel_statedSL hp hp3 (by rw [hK, pow_one])).e9Inv

theorem facts134E9_psu3Minus : ∀ p : ℕ, p.Prime → p ≠ 2 → p % 3 = 2 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1 := by
  intro p hp hp2 hp3
  refine noE9Config_of_e9Inv fun X _ hX => ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  exact E9Inv.of_mulEquiv e (oddModel_statedSU hp hp2 hp3 hK).e9Inv

end CFSG.Quasithin.P134
