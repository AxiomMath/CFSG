module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerShape
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerHeis
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerTwo

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n : ℕ}

theorem TwoBlocks.inv {hKd : UnitaryFieldData 2 n K} {M : GL (Fin 6) K} (h : TwoBlocks hKd M) :
    TwoBlocks hKd M⁻¹ := by
  obtain ⟨P, hP, τ, hMP, hb, v₁, v₂, S₁, S₂, hv, hS₁, hS₂, h₁, h₂⟩ := h
  refine ⟨P, hP, τ⁻¹, ?_, ?_, v₁⁻¹, v₂⁻¹, S₁, S₂, fun h' => hv (inv_injective h'), ?_, ?_, h₁, h₂⟩
  · rw [show P⁻¹ * M⁻¹ * P = (P⁻¹ * M * P)⁻¹ by group, hMP, ← map_inv]
  · intro i S hS
    exact hb i S fun j => (hS j).trans (by rw [Pi.inv_apply, Pi.inv_apply, _root_.inv_inj])
  · intro i
    rw [hS₁ i, Pi.inv_apply, _root_.inv_inj]
  · intro i
    rw [hS₂ i, Pi.inv_apply, _root_.inv_inj]

theorem twoBlocks_of_mono (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {x y z : GL (Fin 6) K} (hxu : x ∈ primeFormUnitary hKd (idGram K 6))
    (hyu : y ∈ primeFormUnitary hKd (idGram K 6)) (hzu : z ∈ primeFormUnitary hKd (idGram K 6))
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) (hxz : x * z = z * x)
    (hyz : y * z = z * y) {i j : ℕ} (hij : i ≠ 0 ∨ j ≠ 0) (hi : i < 3) (hj : j < 3) (k : ℕ) :
    TwoBlocks hKd (x ^ i * y ^ j * z ^ k) := by
  set u : GL (Fin 6) K := GeneralLinearGroup.scalar (Fin 6) ζ with hu
  have hcu : ∀ g : GL (Fin 6) K, Commute u g := fun g => (commute_scalar ζ g).symm
  have hu3 : u ^ 3 = 1 := by rw [hu, ← map_pow, hζ.pow_eq_one, map_one]
  have hxi3 : (x ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  have hyj3 : (y ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy3, one_pow]
  have hX3 : (x ^ i * y ^ j) ^ 3 = 1 := by
    have hq : x ^ i * y ^ j = u ^ (i * j) * (y ^ j * x ^ i) := pow_mul_pow_eq_central hcu hxy i j
    have hu3' : (u ^ (i * j)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu3, one_pow]
    rw [mul_pow_three_eq_central (fun g => (hcu g).pow_left _) hq hu3', hxi3, hyj3, one_mul]
  have hXu : x ^ i * y ^ j ∈ primeFormUnitary hKd (idGram K 6) :=
    mul_mem (pow_mem hxu i) (pow_mem hyu j)
  have hXz : (x ^ i * y ^ j) * z = z * (x ^ i * y ^ j) :=
    ((Commute.pow_left (show Commute x z from hxz) i).mul_left
      (Commute.pow_left (show Commute y z from hyz) j)).eq
  by_cases hi0 : i = 0
  · have hj0 : j ≠ 0 := hij.resolve_left (not_not.mpr hi0)
    have hcop : Nat.Coprime j 3 := by
      interval_cases j <;> first | exact absurd rfl hj0 | decide
    have hζ' : IsPrimitiveRoot (ζ ^ j)⁻¹ 3 := (hζ.pow_of_coprime j hcop).inv
    have hrel : (x ^ i * y ^ j) * x = GeneralLinearGroup.scalar (Fin 6) (ζ ^ j)⁻¹ *
        (x * (x ^ i * y ^ j)) := by
      rw [map_inv, map_pow, ← hu]
      calc (x ^ i * y ^ j) * x = (u ^ j)⁻¹ * (u ^ j * ((x ^ i * y ^ j) * x)) :=
            (inv_mul_cancel_left _ _).symm
        _ = (u ^ j)⁻¹ * (x * (x ^ i * y ^ j)) := by rw [← heis_pair_x hcu hxy i j]
    exact twoBlocks_of_noncentral hKd hpq hXu hzu hX3 hz3 hζ' hrel hXz hxz k
  · have hcop : Nat.Coprime i 3 := by
      interval_cases i <;> first | exact absurd rfl hi0 | decide
    have hζ' : IsPrimitiveRoot (ζ ^ i) 3 := hζ.pow_of_coprime i hcop
    have hrel : (x ^ i * y ^ j) * y = GeneralLinearGroup.scalar (Fin 6) (ζ ^ i) *
        (y * (x ^ i * y ^ j)) := by
      rw [map_pow, ← hu]
      exact heis_pair_y hcu hxy i j
    exact twoBlocks_of_noncentral hKd hpq hXu hzu hX3 hz3 hζ' hrel hXz hyz k

theorem twoBlocks_of_central_pow (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {x y z : GL (Fin 6) K} (hxu : x ∈ primeFormUnitary hKd (idGram K 6))
    (hzu : z ∈ primeFormUnitary hKd (idGram K 6)) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3) (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) (hzs : z ∉ LargeEvenScalars (Fin 6) K) {k : ℕ}
    (hk : k < 3) (hk0 : k ≠ 0) : TwoBlocks hKd (z ^ k) := by
  have h := twoBlocks_of_central hKd hpq hxu hzu hx3 hz3 hζ hxy hxz hyz hzs
  interval_cases k
  · exact absurd rfl hk0
  · rwa [pow_one]
  · have : z ^ 2 = z⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hz3])
    rw [this]
    exact h.inv

theorem not_isComponentOf_layer_ggFix_of_twoBlocks_all (hKd : UnitaryFieldData 2 n K)
    {M : GL (Fin 6) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (h : TwoBlocks hKd M) :
    ¬ IsComponentOf (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩)) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h1 : n = 1 := le_antisymm (by omega) hKd.one_le
    subst h1
    obtain ⟨P, hP, τ, hMP, hb, -⟩ := h
    have hPN : P ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
      gu_subset_normalizer hKd (mem_guSet_of_mem_primeFormUnitary hKd hP)
    have hD : diagHom 6 τ ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) := by
      rw [← hMP]
      exact mul_mem (mul_mem (inv_mem hPN) hM) hPN
    exact not_isComponentOf_layer_ggFix_of_conj hKd hM hP hMP hD
      (not_isComponentOf_layer_ggFix_diag_two hKd hD hb)
  · exact not_isComponentOf_layer_ggFix_of_twoBlocks hKd hn hM h

theorem scalar_mem_largeEvenScalars (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin 6) c ∈ LargeEvenScalars (Fin 6) K :=
  ⟨c, rfl⟩

theorem exists_scalar_mul_of_projConj_eq' [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {M M' : GL (Fin 6) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hM' : M' ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (h : TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨M', hM'⟩) :
    ∃ c : Kˣ, M = GeneralLinearGroup.scalar (Fin 6) c * M' := by
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [hKd.card, ← pow_mul, mul_comm]
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have h1 : TableB.projConj (unitarySU 2 n K 6)
      ((⟨M, hM⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) *
        (⟨M', hM'⟩ : Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := TableBUE.mem_scalars_of_projConj_eq_one hKd hK (by norm_num) hdq Nat.prime_three hpq
    h1
  rw [largeEvenScalars_def] at h2
  obtain ⟨c, hc⟩ := h2
  refine ⟨c, ?_⟩
  have h3 : (M * M'⁻¹ : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) c := hc.symm
  rw [← h3]
  group

theorem exists_mono_of_card [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))} (hcard : Nat.card Ab = 27)
    {x y z : GL (Fin 6) K}
    (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hzN : z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ 3) (hxA : TableB.projConj (unitarySU 2 n K 6) ⟨x, hxN⟩ ∈ Ab)
    (hyA : TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩ ∈ Ab)
    (hzA : TableB.projConj (unitarySU 2 n K 6) ⟨z, hzN⟩ ∈ Ab)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hz3 : z ^ 3 = 1) (hzs : z ∉ LargeEvenScalars (Fin 6) K) :
    ∀ a ∈ Ab, ∃ (i j k : ℕ) (hM : x ^ i * y ^ j * z ^ k ∈
        Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      i < 3 ∧ j < 3 ∧ k < 3 ∧
        a = TableB.projConj (unitarySU 2 n K 6) ⟨x ^ i * y ^ j * z ^ k, hM⟩ := by
  classical
  have hNmem : ∀ i j k : ℕ, x ^ i * y ^ j * z ^ k ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) := fun i j k =>
    mul_mem (mul_mem (pow_mem hxN i) (pow_mem hyN j)) (pow_mem hzN k)
  set pc := TableB.projConj (unitarySU 2 n K 6) with hpc
  have hmono : ∀ i j k : ℕ, pc ⟨x ^ i * y ^ j * z ^ k, hNmem i j k⟩ =
      pc ⟨x, hxN⟩ ^ i * pc ⟨y, hyN⟩ ^ j * pc ⟨z, hzN⟩ ^ k := by
    intro i j k
    rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
    rfl
  have hmemAb : ∀ i j k : ℕ, pc ⟨x ^ i * y ^ j * z ^ k, hNmem i j k⟩ ∈ Ab := by
    intro i j k
    rw [hmono]
    exact mul_mem (mul_mem (pow_mem hxA i) (pow_mem hyA j)) (pow_mem hzA k)
  let F : Fin 3 × Fin 3 × Fin 3 → Ab := fun t =>
    ⟨pc ⟨x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * z ^ (t.2.2 : ℕ), hNmem _ _ _⟩, hmemAb _ _ _⟩
  have hu3 : GeneralLinearGroup.scalar (Fin 6) ζ ^ 3 = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have hu1 : GeneralLinearGroup.scalar (Fin 6) ζ ≠ 1 := fun h =>
    hζ.ne_one (by norm_num) (TypeA.PGLTor.scalar_injective (by rw [h, map_one]))
  have hinj : Function.Injective F := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hF
    have h1 := congrArg Subtype.val hF
    obtain ⟨c, hc⟩ := exists_scalar_mul_of_projConj_eq' hKd hpq (hNmem _ _ _) (hNmem _ _ _) h1
    obtain ⟨hii, hjj, hkk⟩ := mono_inj (scalar_mem_largeEvenScalars ζ) hu3 hu1 hxy hxz hyz hz3
      hzs (scalar_mem_largeEvenScalars c) j.2 j'.2 i.2 i'.2 k.2 k'.2 hc
    rw [Fin.ext hii, Fin.ext hjj, Fin.ext hkk]
  haveI : Finite Ab := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hbij : Function.Bijective F := hinj.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_eq_fintype_card]
    simp)
  intro a ha
  obtain ⟨⟨i, j, k⟩, hF⟩ := hbij.2 ⟨a, ha⟩
  exact ⟨i, j, k, hNmem _ _ _, i.2, j.2, k.2, (congrArg Subtype.val hF).symm⟩

theorem not_isComponentOf_layer_ggFix_of_heis [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))} (hcard : Nat.card Ab = 27)
    {x y z : GL (Fin 6) K}
    (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hzN : z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) {ζ : Kˣ}
    (hxu : x ∈ primeFormUnitary hKd (idGram K 6)) (hyu : y ∈ primeFormUnitary hKd (idGram K 6))
    (hzu : z ∈ primeFormUnitary hKd (idGram K 6))
    (hxA : TableB.projConj (unitarySU 2 n K 6) ⟨x, hxN⟩ ∈ Ab)
    (hyA : TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩ ∈ Ab)
    (hzA : TableB.projConj (unitarySU 2 n K 6) ⟨z, hzN⟩ ∈ Ab)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) (hxz : x * z = z * x)
    (hyz : y * z = z * y) (hzs : z ∉ LargeEvenScalars (Fin 6) K) :
    ∀ a ∈ Ab, a ≠ 1 → ¬ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
  intro a ha ha1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζ : IsPrimitiveRoot ζ 3 := by
    have := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime hζ3 hζ1] at this
  obtain ⟨i, j, k, hM, hi, hj, hk, rfl⟩ := exists_mono_of_card hKd hpq hcard hxN hyN hzN hζ hxA hyA
    hzA hxy hxz hyz hz3 hzs a ha
  by_cases hij : i ≠ 0 ∨ j ≠ 0
  · exact not_isComponentOf_layer_ggFix_of_twoBlocks_all hKd hM
      (twoBlocks_of_mono hKd hpq hxu hyu hzu hx3 hy3 hz3 hζ hxy hxz hyz hij hi hj k)
  · push Not at hij
    obtain ⟨rfl, rfl⟩ := hij
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply ha1
      have : (⟨x ^ 0 * y ^ 0 * z ^ 0, hM⟩ :
          Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = 1 :=
        Subtype.ext (by simp)
      rw [this, map_one]
    refine not_isComponentOf_layer_ggFix_of_twoBlocks_all hKd hM ?_
    rw [pow_zero, pow_zero, one_mul, one_mul]
    exact twoBlocks_of_central_pow hKd hpq hxu hzu hx3 hz3 hζ hxy hxz hyz hzs hk hk0

theorem not_isComponentOf_layer_ggFix_of_heis_alt [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K 6)))} (hcard : Nat.card Ab = 27)
    (hheis : ∃ (x y z : GL (Fin 6) K)
      (hxN : x ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
      (hyN : y ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
      (hzN : z ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) (ζ : Kˣ),
      x ∈ primeFormUnitary hKd (idGram K 6) ∧ y ∈ primeFormUnitary hKd (idGram K 6) ∧
      z ∈ primeFormUnitary hKd (idGram K 6) ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨x, hxN⟩ ∈ Ab ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩ ∈ Ab ∧
      TableB.projConj (unitarySU 2 n K 6) ⟨z, hzN⟩ ∈ Ab ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧
      x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x) ∧ x * z = z * x ∧ y * z = z * y ∧
      z ∉ LargeEvenScalars (Fin 6) K) :
    ∀ a ∈ Ab, a ≠ 1 → ¬ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
  obtain ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA, hx3, hy3, hz3, hζ3, hζ1, hxy,
    hxz, hyz, hzs⟩ := hheis
  exact not_isComponentOf_layer_ggFix_of_heis hKd hpq hcard hxN hyN hzN hxu hyu hzu hxA hyA hzA
    hx3 hy3 hz3 hζ3 hζ1 hxy hxz hyz hzs

end CFSG.StandardType.Line63.H5

end
