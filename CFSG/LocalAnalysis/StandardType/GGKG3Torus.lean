module

public import CFSG.LocalAnalysis.StandardType.GGKG3ExData
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def k3Tor {L : Type} [Field L] (ζ : Lˣ) (y : Fin 6 → ZMod 7) :
    Fin Tag.E6.rank → Lˣ :=
  fun i => ζ ^ (y i).val

@[expose] def k3Chi {L : Type} [Field L] (ζ : Lˣ) (a : ZMod 7) : Lˣ := ζ ^ a.val

private theorem kg3_pow_val_add {L : Type} [Field L] {ζ : Lˣ} (h7 : ζ ^ 7 = 1) (a b : ZMod 7) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  have key : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 7) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 7]
    rw [pow_add, pow_mul, h7, one_pow, mul_one]
  rw [← pow_add, ZMod.val_add, ← key]

theorem k3Chi_add {L : Type} [Field L] {ζ : Lˣ} (h7 : ζ ^ 7 = 1) (a b : ZMod 7) :
    k3Chi ζ (a + b) = k3Chi ζ a * k3Chi ζ b :=
  kg3_pow_val_add h7 a b

theorem k3Chi_zero {L : Type} [Field L] (ζ : Lˣ) : k3Chi ζ (0 : ZMod 7) = 1 := by
  simp [k3Chi]

theorem k3Chi_injective {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 7) :
    Function.Injective (k3Chi ζ) := by
  intro a b h
  have h2 : ζ ^ a.val = ζ ^ b.val := h
  rw [pow_eq_pow_iff_modEq, hζ] at h2
  have hx := ZMod.val_lt a
  have hy := ZMod.val_lt b
  have : a.val = b.val := by
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  exact ZMod.val_injective _ this

private theorem kg3_prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private theorem kg3_zpow_eq_k3Chi {L : Type} [Field L] {ζ : Lˣ} (h7 : ζ ^ 7 = 1) (z : ℤ) :
    ζ ^ z = k3Chi ζ (z : ZMod 7) := by
  have h1 : (((z : ZMod 7).val : ℕ) : ℤ) = z % 7 := ZMod.val_intCast z
  have h7z : ζ ^ (7 : ℤ) = 1 := by
    rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) from rfl, zpow_natCast, h7]
  rw [k3Chi, ← zpow_natCast, h1]
  conv_lhs => rw [← Int.emod_add_mul_ediv z 7]
  rw [zpow_add, zpow_mul, h7z, one_zpow, mul_one]

theorem rootChar_k3Tor {L : Type} [Field L] {ζ : Lˣ} (h7 : ζ ^ 7 = 1) (y : Fin 6 → ZMod 7)
    (v : Fin Tag.E6.rank → ℤ) : rootChar (k3Tor ζ y) v = k3Chi ζ (k3Pair y v) := by
  have h1 : rootChar (k3Tor ζ y) v = ζ ^ (∑ i, (((y i).val : ℕ) : ℤ) * v i) := by
    rw [rootChar, ← kg3_prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [k3Tor, ← zpow_natCast, ← zpow_mul]
  rw [h1, kg3_zpow_eq_k3Chi h7]
  congr 1
  simp [k3Pair]

theorem k3Tor_injective {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 7) :
    Function.Injective (k3Tor ζ : (Fin 6 → ZMod 7) → Fin Tag.E6.rank → Lˣ) := by
  intro y z h
  funext i
  exact k3Chi_injective hζ (congrFun h i)

theorem exists_eq_k3Tor {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 7)
    (a : Fin Tag.E6.rank → Lˣ) (ha : ∀ i, a i ^ 7 = 1) : ∃ y : Fin 6 → ZMod 7, a = k3Tor ζ y := by
  have hprim : IsPrimitiveRoot ζ 7 := IsPrimitiveRoot.iff_orderOf.2 hζ
  have hprimL : IsPrimitiveRoot (ζ : L) 7 := IsPrimitiveRoot.coe_units_iff.2 hprim
  have : ∀ i, ∃ k : ℕ, k < 7 ∧ ζ ^ k = a i := fun i => by
    have h1 : ((a i : Lˣ) : L) ^ 7 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ha i, Units.val_one]
    obtain ⟨k, hk, hk'⟩ := hprimL.eq_pow_of_pow_eq_one h1
    exact ⟨k, hk, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk')⟩
  choose k hk hka using this
  refine ⟨fun i => (k i : ZMod 7), funext fun i => ?_⟩
  rw [k3Tor, ZMod.val_natCast_of_lt (hk i), hka i]

theorem k3_exists_zeta {L : Type} [Field L] [IsAlgClosed L] (h2 : ((2 : ℕ) : L) = 0) :
    ∃ ζ : Lˣ, orderOf ζ = 7 := by
  haveI : CharP L 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have : NeZero ((7 : ℕ) : L) := NeZero.of_not_dvd L (p := 2) (by norm_num)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 7
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  have hζu : IsPrimitiveRoot hu.unit 7 := IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)
  exact ⟨hu.unit, hζu.eq_orderOf.symm⟩

end CFSG.StandardType.GGKG3
