module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Sporadic.Recognition.JankoWong

theorem exists_orderOf_eq_four_of_card_eq_four {K : Type*} [Group K] (P : Subgroup K)
    (hP : Nat.card P = 4)
    (hno : ∀ u v : K, u ≠ 1 → v ≠ 1 → u ≠ v → u * v = v * u → u ^ 2 = 1 → v ^ 2 = 1 → False) :
    ∃ g : P, orderOf g = 4 := by
  by_contra hcon
  have hsq : ∀ x : P, x ^ 2 = 1 := by
    intro x
    have hdvd : orderOf x ∣ 2 ^ 2 := by simpa [hP] using orderOf_dvd_natCard x
    obtain ⟨k, hk, hxk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hk2 : k ≠ 2 := by
      rintro rfl
      exact hcon ⟨x, by simpa using hxk⟩
    have hk1 : k ≤ 1 := by omega
    exact orderOf_dvd_iff_pow_eq_one.1 (hxk ▸ (pow_dvd_pow 2 hk1).trans (by simp))
  have hinv : ∀ x : P, x⁻¹ = x := fun x =>
    inv_eq_of_mul_eq_one_right ((pow_two x).symm.trans (hsq x))
  have hcomm : ∀ x y : P, x * y = y * x := fun x y => by
    calc x * y = (x * y)⁻¹ := (hinv (x * y)).symm
      _ = y * x := by rw [mul_inv_rev, hinv, hinv]
  classical
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype P := Fintype.ofFinite P
  have hcard : 1 < (Finset.univ.erase (1 : P)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_eq_nat_card,
      hP]
    norm_num
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu hv
  exact hno u v (fun h => hu (OneMemClass.coe_eq_one.1 h))
    (fun h => hv (OneMemClass.coe_eq_one.1 h)) (fun h => huv (Subtype.coe_injective h))
    (by simpa using congrArg Subtype.val (hcomm u v))
    (by simpa using congrArg Subtype.val (hsq u)) (by simpa using congrArg Subtype.val (hsq v))

theorem le_ker_of_isPGroup_three {K L : Type*} [Group K] [Group L] (φ : K →* L)
    (hL : Nat.card L = 4) {R : Subgroup K} (hR : IsPGroup 3 R) : R ≤ φ.ker := by
  intro r hr
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hR ⟨r, hr⟩
  have h3 : orderOf (φ r) ∣ 3 ^ k := by
    rw [← hk, ← Subgroup.orderOf_coe]
    exact orderOf_map_dvd φ r
  have h2 : orderOf (φ r) ∣ 2 ^ 2 := by simpa [hL] using orderOf_dvd_natCard (φ r)
  have hcop : Nat.Coprime (2 ^ 2) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  exact MonoidHom.mem_ker.2
    (orderOf_eq_one_iff.1 ((hcop.coprime_dvd_left h2).eq_one_of_dvd h3))

theorem exists_orderOf_four_and_normal_sylow_three {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 2916)
    (hno : ∀ u v : K, u ≠ 1 → v ≠ 1 → u ≠ v → u * v = v * u → u ^ 2 = 1 → v ^ 2 = 1 → False) :
    (∃ g : K, orderOf g = 4) ∧
      ∃ X : Subgroup K, X.Normal ∧ Nat.card X = 3 ^ 6 ∧ ∀ R : Subgroup K, IsPGroup 3 R → R ≤ X := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hfac : (Nat.card K).factorization 2 = 2 := by
    have h : (2916 : ℕ) = 2 ^ 2 * 3 ^ 6 := by norm_num
    rw [hK, h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hP : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hfac]
    norm_num
  obtain ⟨g, hg⟩ := exists_orderOf_eq_four_of_card_eq_four (P : Subgroup K) hP hno
  have hcyc : IsCyclic P := isCyclic_of_orderOf_eq_card g (hg.trans hP.symm)
  have hmin : (Nat.card K).minFac = 2 := by
    rw [hK]
    norm_num
  have hcompl := IsCyclic.isComplement' hmin hcyc
  refine ⟨⟨(g : K), (Subgroup.orderOf_coe g).trans hg⟩,
    (MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hmin)).ker,
    MonoidHom.normal_ker _, ?_, fun R hR => le_ker_of_isPGroup_three _ hP hR⟩
  have hmul := hcompl.card_mul_card
  rw [hP, hK] at hmul
  rw [show (3 : ℕ) ^ 6 = 729 by norm_num]
  omega

end CFSG.Sporadic.Recognition.JankoWong
