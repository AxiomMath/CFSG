module

public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin.R3c

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover

section SLTwo

variable {K : Type} [Field K]

private noncomputable def splitTorusTwo (K : Type) [Field K] : Kˣ →* ↥(StatedSL 2 K) where
  toFun a := ⟨diagHom 2 ![a, a⁻¹], Subgroup.subset_closure (by
    show ((diagHom 2 ![a, a⁻¹] : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [det_diagHom, Fin.prod_univ_two]
    simp)⟩
  map_one' := by
    apply Subtype.ext
    show diagHom 2 ![(1 : Kˣ), (1 : Kˣ)⁻¹] = 1
    rw [← map_one (diagHom (K := K) 2)]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show diagHom 2 ![a * b, (a * b)⁻¹] = diagHom 2 ![a, a⁻¹] * diagHom 2 ![b, b⁻¹]
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

private theorem splitTorusTwo_injective : Function.Injective (splitTorusTwo K) := by
  intro a b h
  have h' := congrArg Subtype.val h
  have h'' := diagHom_injective 2 h'
  simpa using congrFun h'' 0

theorem card_statedSL_two_pow [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSL 2 K) = 2 ^ n * (4 ^ n - 1) := by
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
    CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_two_pow hK]

theorem isCyclic_isPGroup_three_statedSL_two_even [Finite K] {n : ℕ} (hn : Even n)
    (hK : Nat.card K = 2 ^ n) {R : Subgroup ↥(StatedSL 2 K)} (hR : IsPGroup 3 R) :
    IsCyclic R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even hn
  set ψ := splitTorusTwo K
  set Z : Subgroup ↥(StatedSL 2 K) := ψ.range with hZdef
  have hZc : IsCyclic Z := isCyclic_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hZ : Nat.card Z = 2 ^ n - 1 := by
    rw [hZdef, ← Nat.card_congr (MonoidHom.ofInjective splitTorusTwo_injective).toEquiv,
      card_units_eq, hK]
  have hG : Nat.card ↥(StatedSL 2 K) = Nat.card Z * (2 ^ n * (2 ^ n + 1)) := by
    rw [card_statedSL_two_pow hK, hZ]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h4 : 4 ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    zify [h1, Nat.one_le_pow 2 (2 ^ n) (by omega)]
    ring
  have hm : ¬ 3 ∣ 2 ^ n * (2 ^ n + 1) := by
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h <;> omega
  exact isCyclic_of_isPGroup_of_card_eq_mul hG hm hR

theorem card_GL_two [Finite K] :
    Nat.card (GL (Fin 2) K) = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]

theorem isCyclic_isPGroup_three_statedSL_two_odd [Finite K] {n : ℕ} (hn : Odd n)
    (hK : Nat.card K = 2 ^ n) {R : Subgroup ↥(StatedSL 2 K)} (hR : IsPGroup 3 R) :
    IsCyclic R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 2 ^ n % 3 = 2 := two_pow_mod_three_of_odd hn
  obtain ⟨Z, hZc, hZ⟩ := exists_isCyclic_card_GL K 2
  have hG : Nat.card (GL (Fin 2) K) = Nat.card Z * (Nat.card K ^ 2 - Nat.card K) := by
    rw [card_GL_two, hZ]
  have hm : ¬ 3 ∣ Nat.card K ^ 2 - Nat.card K := by
    have h1 : Nat.card K ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod, hK, hq]
    have h2 : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
    have h3 : Nat.card K % 3 = 2 := by rw [hK]; exact hq
    omega
  have hcyc : IsCyclic (R.map (StatedSL 2 K).subtype) :=
    isCyclic_of_isPGroup_of_card_eq_mul hG hm (hR.map (StatedSL 2 K).subtype)
  have e := R.equivMapOfInjective _ (StatedSL 2 K).subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem isCyclic_isPGroup_three_statedSL_two [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {R : Subgroup ↥(StatedSL 2 K)} (hR : IsPGroup 3 R) : IsCyclic R := by
  rcases Nat.even_or_odd n with hn | hn
  · exact isCyclic_isPGroup_three_statedSL_two_even hn hK hR
  · exact isCyclic_isPGroup_three_statedSL_two_odd hn hK hR

theorem noElemNine_statedSL_two [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CFSG.Quasithin.F134.NoElemNine ↥(StatedSL 2 K) :=
  CFSG.Quasithin.F134.noElemNine_of_isCyclic fun _ hQ =>
    isCyclic_isPGroup_three_statedSL_two hK hQ

theorem noElemNine_specialLinear_two [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CFSG.Quasithin.F134.NoElemNine (Matrix.SpecialLinearGroup (Fin 2) K) :=
  CFSG.Quasithin.F134.NoElemNine.of_mulEquiv (specialLinearGroupEquivStatedSL 2 K)
    (noElemNine_statedSL_two hK)

theorem noElemNine_statedProj_statedSL_two [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CFSG.Quasithin.F134.NoElemNine (StatedProj (StatedSL 2 K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.Quasithin.F134.noElemNine_of_isCyclic fun Q hQ => ?_
  exact CFSG.Quasithin.F134.isCyclic_of_isPGroup_of_surjective (QuotientGroup.mk'_surjective _)
    (fun S => isCyclic_isPGroup_three_statedSL_two hK S.isPGroup') Q hQ

end SLTwo

end CFSG.Quasithin.R3c
