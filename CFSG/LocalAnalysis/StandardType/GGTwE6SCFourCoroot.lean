module

public import CFSG.LieType.Chevalley.Braid
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


variable {Ω : Type} [Field Ω]

private theorem torusElt_pow_eq (i : Fin Tag.E6.rank) (s : Ωˣ) (k : ℕ) :
    torusElt Tag.E6 Ω i s ^ k = torusElt Tag.E6 Ω i (s ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, torusElt_one]
  | succ k ih => rw [pow_succ, ih, pow_succ, torusElt_mul]

private theorem prod_zpow_eq {G : Type*} [CommGroup G] (y : G) (e : Fin Tag.E6.rank → ℤ) :
    ∏ k, y ^ e k = y ^ ∑ k, e k := by
  have h : ∀ m : ℤ, y ^ m = zpowersHom G y (Multiplicative.ofAdd m) := fun _ => rfl
  simp only [h, ofAdd_sum, map_prod]

private theorem cartanChar_pow_val (ζ : Ωˣ) (x : Fin Tag.E6.rank → ZMod 3) (l : Fin Tag.E6.rank) :
    cartanChar (fun j => ζ ^ (x j).val) l = ζ ^ ∑ j, ((x j).val : ℤ) * Tag.E6.cartan j l := by
  simp only [cartanChar]
  rw [← prod_zpow_eq]
  exact Finset.prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul]

private theorem eq_of_cartan_eq {y y' : Fin 5 → ZMod 3}
    (h : ∀ l : Fin Tag.E6.rank,
      ∑ j, (![0, y 0, y 1, y 2, y 3, y 4] : Fin Tag.E6.rank → ZMod 3) j *
          ((Tag.E6.cartan j l : ℤ) : ZMod 3) =
        ∑ j, (![0, y' 0, y' 1, y' 2, y' 3, y' 4] : Fin Tag.E6.rank → ZMod 3) j *
          ((Tag.E6.cartan j l : ℤ) : ZMod 3)) : y = y' := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have e0 := h (0 : Fin 6)
  have e1 := h (1 : Fin 6)
  have e2 := h (2 : Fin 6)
  have e3 := h (3 : Fin 6)
  have e5 := h (5 : Fin 6)
  simp [Fin.sum_univ_six, Tag.cartan, Tag.cartanE] at e0 e1 e2 e3 e5
  have hy2 : y 2 = y' 2 := by linear_combination 2 * e0 - e2
  have hy0 : y 0 = y' 0 := by linear_combination 2 * (2 * e0 - e2 + e1) - (y 0 - y' 0) * h3
  have hy3 : y 3 = y' 3 := by linear_combination -hy0 - e0 + 2 * hy2 - e3
  have hy4 : y 4 = y' 4 := by linear_combination 2 * (hy3 + e5) - (y 4 - y' 4) * h3
  funext k
  fin_cases k
  exacts [hy0, e0, hy2, hy3, hy4]

private theorem weylElt_mul_self_of_two (h2 : (2 : Ω) = 0) (i : Fin Tag.E6.rank) :
    weylElt Tag.E6 Ω i 1 * weylElt Tag.E6 Ω i 1 = 1 := by
  have h : (-1 : Ωˣ) = 1 := Units.ext (by
    rw [Units.val_neg, Units.val_one]
    linear_combination -h2)
  rw [weylElt_one_mul_self, h, torusElt_one]

private theorem weylElt_conj_torusElt (i : Fin Tag.E6.rank) (s : Ωˣ) :
    weylElt Tag.E6 Ω i 1 * torusElt Tag.E6 Ω i s * (weylElt Tag.E6 Ω i 1)⁻¹ =
      (torusElt Tag.E6 Ω i s)⁻¹ := by
  rw [weylElt_one_mul_torusElt_mul_inv, Tag.E6.cartan_self, eq_inv_iff_mul_eq_one,
    ← torusElt_mul, ← torusElt_mul, show s * s ^ (-(2 : ℤ)) * s = 1 by group, torusElt_one]

theorem inverts_conj_torusElt (h2 : (2 : Ω) = 0) (g : ModGL Tag.E6 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (i : Fin Tag.E6.rank) :
    (g * torusElt Tag.E6 Ω i ζ * g⁻¹) ^ 3 = 1 ∧
      g * weylElt Tag.E6 Ω i 1 * g⁻¹ * (g * weylElt Tag.E6 Ω i 1 * g⁻¹) = 1 ∧
      g * weylElt Tag.E6 Ω i 1 * g⁻¹ * (g * torusElt Tag.E6 Ω i ζ * g⁻¹) *
          (g * weylElt Tag.E6 Ω i 1 * g⁻¹)⁻¹ = (g * torusElt Tag.E6 Ω i ζ * g⁻¹)⁻¹ := by
  refine ⟨by rw [conj_pow, torusElt_pow_eq, hζ, torusElt_one, mul_one, mul_inv_cancel], ?_, ?_⟩
  · rw [show g * weylElt Tag.E6 Ω i 1 * g⁻¹ * (g * weylElt Tag.E6 Ω i 1 * g⁻¹) =
      g * (weylElt Tag.E6 Ω i 1 * weylElt Tag.E6 Ω i 1) * g⁻¹ by group,
      weylElt_mul_self_of_two h2, mul_one, mul_inv_cancel]
  · rw [show g * weylElt Tag.E6 Ω i 1 * g⁻¹ * (g * torusElt Tag.E6 Ω i ζ * g⁻¹) *
        (g * weylElt Tag.E6 Ω i 1 * g⁻¹)⁻¹ = g * (weylElt Tag.E6 Ω i 1 *
          torusElt Tag.E6 Ω i ζ * (weylElt Tag.E6 Ω i 1)⁻¹) * g⁻¹ by group,
      weylElt_conj_torusElt]
    group

theorem conj_rootDiagUnit_conj_weylElt (g : ModGL Tag.E6 Ω) {b : Fin Tag.E6.rank → Ωˣ}
    (hb : ∀ j, b j ^ 3 = 1) {ζ : Ωˣ} (hζ : orderOf ζ = 3) (i : Fin Tag.E6.rank) :
    g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * torusElt Tag.E6 Ω i ζ * g⁻¹) =
        g * torusElt Tag.E6 Ω i ζ * g⁻¹ * (g * rootDiagUnit Tag.E6 b * g⁻¹) ∧
      ∃ k : ℕ, g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
          (g * rootDiagUnit Tag.E6 b * g⁻¹)⁻¹ =
        g * weylElt Tag.E6 Ω i 1 * g⁻¹ * (g * torusElt Tag.E6 Ω i ζ * g⁻¹) ^ k := by
  have hprim : IsPrimitiveRoot ζ 3 := hζ ▸ IsPrimitiveRoot.orderOf ζ
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_mem_rootsOfUnity
    ((mem_rootsOfUnity 3 (b i)⁻¹).2 (by rw [inv_pow, hb i, inv_one]))
  refine ⟨?_, k, ?_⟩
  · rw [show g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * torusElt Tag.E6 Ω i ζ * g⁻¹) =
        g * (rootDiagUnit Tag.E6 b * torusElt Tag.E6 Ω i ζ) * g⁻¹ by group,
      rootDiagUnit_mul_comm_of_mem_torusGroup b (torusElt_mem_torusGroup i ζ)]
    group
  · have hinv : (torusElt Tag.E6 Ω i (b i)⁻¹)⁻¹ = torusElt Tag.E6 Ω i (b i) := by
      rw [inv_eq_iff_mul_eq_one, ← torusElt_mul, inv_mul_cancel, torusElt_one]
    have h1 : torusElt Tag.E6 Ω i (b i) * weylElt Tag.E6 Ω i 1 =
        weylElt Tag.E6 Ω i 1 * torusElt Tag.E6 Ω i (b i)⁻¹ := by
      have h := weylElt_conj_torusElt i (b i)⁻¹
      rw [hinv] at h
      rw [← h]
      group
    rw [show g * rootDiagUnit Tag.E6 b * g⁻¹ * (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
          (g * rootDiagUnit Tag.E6 b * g⁻¹)⁻¹ = g * (rootDiagUnit Tag.E6 b *
            weylElt Tag.E6 Ω i 1 * (rootDiagUnit Tag.E6 b)⁻¹) * g⁻¹ by group,
      rootDiagUnit_conj_weylElt_one, h1, ← hk, ← torusElt_pow_eq, conj_pow]
    group

theorem three_pow_five_le_card_of_conj_torusElt_mem {X : Subgroup (ModGL Tag.E6 Ω)} [Finite X]
    {g : ModGL Tag.E6 Ω} {ζ : Ωˣ} (hζ : orderOf ζ = 3)
    (hX : ∀ i, g * torusElt Tag.E6 Ω i ζ * g⁻¹ ∈ X) : 3 ^ 5 ≤ Nat.card X := by
  let x : (Fin 5 → ZMod 3) → Fin Tag.E6.rank → ZMod 3 := fun y => ![0, y 0, y 1, y 2, y 3, y 4]
  have hmem : ∀ y, g * rootDiagUnit Tag.E6 (cartanChar fun j => ζ ^ (x y j).val) * g⁻¹ ∈ X := by
    intro y
    have e : ∀ l : List (ModGL Tag.E6 Ω),
        g * l.prod * g⁻¹ = (l.map fun m => g * m * g⁻¹).prod := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]; group
    rw [← list_prod_torusElt_eq_rootDiagUnit, e, List.map_map]
    refine Subgroup.list_prod_mem _ fun m hm => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
    rw [Function.comp_apply, ← torusElt_pow_eq, ← conj_pow]
    exact pow_mem (hX j) _
  let e : (Fin 5 → ZMod 3) → X := fun y => ⟨_, hmem y⟩
  have he : Function.Injective e := by
    intro y y' hyy
    have h1 : g * rootDiagUnit Tag.E6 (cartanChar fun j => ζ ^ (x y j).val) * g⁻¹ =
        g * rootDiagUnit Tag.E6 (cartanChar fun j => ζ ^ (x y' j).val) * g⁻¹ :=
      congrArg Subtype.val hyy
    have h2 := rootDiagUnit_injective (mul_left_cancel (mul_right_cancel h1))
    refine eq_of_cartan_eq fun l => ?_
    have hl := congrFun h2 l
    rw [cartanChar_pow_val, cartanChar_pow_val, zpow_eq_zpow_iff_modEq, hζ,
      ← ZMod.intCast_eq_intCast_iff] at hl
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at hl
    exact hl
  have hcard := Nat.card_le_card_of_injective e he
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at hcard

end CFSG.StandardType.SCFourCover

end
