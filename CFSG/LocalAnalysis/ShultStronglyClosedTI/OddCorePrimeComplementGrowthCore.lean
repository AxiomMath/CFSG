module

public import CFSG.Foundations.Basic
public import CFSG.Assembly.OrderReductions.ThompsonSolvableOdd
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Foundations.MaxOrderThompson

public section

namespace CFSG.ShultStronglyClosedTI

variable {D : Type*} [Group D] [Finite D]

theorem primeComplementGrowth_native_core_eq (p : ℕ) [Fact p.Prime] :
    CFSG.OrderReductions.PrimeComplementCore.primeComplementCore p D =
      pPrimeCore p D := by
  apply le_antisymm
  · unfold pPrimeCore
    exact le_sSup ⟨inferInstance,
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (CFSG.OrderReductions.PrimeComplementCore.primeComplementCore_coprime p D)⟩
  · unfold pPrimeCore
    apply sSup_le
    rintro K ⟨hnormal, hcoprime⟩
    let : K.Normal := hnormal
    exact CFSG.OrderReductions.PrimeComplementCore.normal_le_primeComplementCore p K
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcoprime)

theorem primeComplementGrowth_native_ambient_core_eq (p : ℕ) [Fact p.Prime]
    (J : Subgroup D) :
    CFSG.OrderReductions.PrimeComplementCore.ambientCore p J =
      (piCore {q : Nat.Primes | q.val ≠ p} J).map J.subtype := by
  unfold CFSG.OrderReductions.PrimeComplementCore.ambientCore
  rw [primeComplementGrowth_native_core_eq, pPrimeCore_eq_piCore]

theorem primeComplementGrowth_native_maximum_iff (A : Subgroup D) :
    CFSG.OrderReductions.ThompsonCenter.MaximumOrderAbelian D A ↔
      A ∈ maxOrderAbelianFamily D :=
  isMaxCardAbelian_iff_mem_maxOrderAbelianFamily

theorem primeComplementGrowth_native_thompson_eq :
    CFSG.OrderReductions.ThompsonCenter.thompson D = orderThompson D :=
  maxCardThompson_eq_orderThompson

theorem primeComplementGrowth_native_zj_eq :
    CFSG.OrderReductions.ThompsonCenter.thompsonCenter D = orderZJ D :=
  maxCardZJ_eq_orderZJ

theorem primeComplementGrowth_native_product_eq (p : ℕ) [Fact p.Prime]
    (P : Sylow p D) :
    CFSG.OrderReductions.ThompsonCoreProduct.coreProduct p P =
      pPrimeCore p D ⊔ (orderZJ (P : Subgroup D)).map (P : Subgroup D).subtype := by
  unfold CFSG.OrderReductions.ThompsonCoreProduct.coreProduct
  rw [primeComplementGrowth_native_core_eq, primeComplementGrowth_native_zj_eq]

theorem primeComplementGrowth_full_prime_part_core_le (p : ℕ) [Fact p.Prime]
    (V J : Subgroup D) [Group.IsSolvable J] (hVJ : V ≤ J)
    (hpart : CFSG.OrderReductions.PrimePart.primePart p (Nat.card V) =
      CFSG.OrderReductions.PrimePart.primePart p (Nat.card J)) :
    (piCore {q : Nat.Primes | q.val ≠ p} V).map V.subtype ≤
      (piCore {q : Nat.Primes | q.val ≠ p} J).map J.subtype := by
  rw [← primeComplementGrowth_native_ambient_core_eq,
    ← primeComplementGrowth_native_ambient_core_eq]
  exact CFSG.OrderReductions.SolvableComplementContainment.full_primePart_ambientCore_le
    p V J hVJ hpart

omit [Finite D] in
theorem primeComplementGrowth_order_zj_characteristic [Finite D] :
    (orderZJ D).Characteristic :=
  inferInstance

theorem primeComplementGrowth_order_zj_ne_bot [Nontrivial D]
    (p : ℕ) [Fact p.Prime] (hD : IsPGroup p D) : orderZJ D ≠ ⊥ :=
  orderZJ_ne_bot_of_isPGroup Fact.out hD

theorem primeComplementGrowth_odd_product_characteristic (p : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hDodd : Odd (Nat.card D)) (P : Sylow p D) :
    (pPrimeCore p D ⊔
      (orderZJ (P : Subgroup D)).map (P : Subgroup D).subtype).Characteristic := by
  let : Group.IsSolvable D := CFSG.FeitThompson.isSolvable_of_odd_natCard D hDodd
  rw [← primeComplementGrowth_native_product_eq]
  exact CFSG.OrderReductions.ThompsonSolvableOdd.coreProduct_characteristic_of_solvable_odd
    p hpodd hDodd P

theorem primeComplementGrowth_product_ne_bot [Nontrivial D]
    (p : ℕ) [Fact p.Prime] (P : Sylow p D) :
    pPrimeCore p D ⊔
      (orderZJ (P : Subgroup D)).map (P : Subgroup D).subtype ≠ ⊥ := by
  rw [← primeComplementGrowth_native_product_eq]
  exact CFSG.OrderReductions.ThompsonCoreProduct.coreProduct_nontrivial p P

end CFSG.ShultStronglyClosedTI
