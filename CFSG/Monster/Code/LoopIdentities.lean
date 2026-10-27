module

public import CFSG.Monster.Code.Cocycle
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Monster.Code

open scoped Finset

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

structure IsMoufangLoop (M : Type*) [Mul M] [One M] : Prop where
  one_mul : ∀ x : M, 1 * x = x
  mul_one : ∀ x : M, x * 1 = x
  existsUnique_mul_left : ∀ a b : M, ∃! x, a * x = b
  existsUnique_mul_right : ∀ a b : M, ∃! y, y * a = b
  moufang : ∀ x y z : M, x * y * (z * x) = x * (y * z * x)

theorem add_self_C (d : C) : d + d = 0 := by
  apply Subtype.ext
  funext i
  simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_zero, Pi.zero_apply]
  rcases zmod2_cases ((d : Fin 24 → ZMod 2) i) with h | h <;> rw [h] <;> rfl

theorem θ_swap (d e : C) : θ e d = θ d e + K d e := by
  have := θ_add_θ_swap d e
  linear_combination this - (θ d e) * two_eq_zero'

namespace Parker

theorem isMoufangLoop : IsMoufangLoop Parker where
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  existsUnique_mul_left a b := by
    refine ⟨⟨b.code - a.code, b.sign - a.sign - θ a.code (b.code - a.code)⟩, ?_, ?_⟩
    · ext
      · simp
      · simp only [mul_sign]; ring
    · rintro x rfl
      ext
      · simp
      · simp only [mul_code, mul_sign, add_sub_cancel_left]
        ring
  existsUnique_mul_right a b := by
    refine ⟨⟨b.code - a.code, b.sign - a.sign - θ (b.code - a.code) a.code⟩, ?_, ?_⟩
    · ext
      · simp
      · simp only [mul_sign]; ring
    · rintro x rfl
      ext
      · simp
      · simp only [mul_code, mul_sign, add_sub_cancel_right]
        ring
  moufang x y z := by
    ext
    · simp only [mul_code]; abel_nf
    · simp only [mul_code, mul_sign]
      have e1 := θ_add_left x.code y.code (z.code + x.code)
      have e2 := θ_add_right x.code z.code x.code
      have e3 := θ_add_right y.code z.code x.code
      have e4 := θ_add_left y.code z.code x.code
      have e5 := θ_add_right x.code (y.code + z.code) x.code
      have e6 := θ_add_right x.code y.code z.code
      have hA1 : A x.code y.code ↑(z.code + x.code) = A x.code y.code z.code := by
        rw [Submodule.coe_add, A_add_right, A_self_mid x.code.2 y.code.2, add_zero]
      have hA2 : A y.code z.code x.code = A x.code y.code z.code := by
        simp only [A_eq_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      linear_combination e1 + e2 + e3 + hA1 - e4 - hA2 - e5 - e6

theorem card : Nat.card Parker = 8192 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_congr basisC.equivFun.toEquiv,
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem negOne_central (x y : Parker) :
    negOne * x = x * negOne ∧ negOne * x * y = negOne * (x * y) ∧
      x * negOne * y = x * (negOne * y) ∧ x * y * negOne = x * (y * negOne) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp [negOne] <;> ring

theorem mul_inv (x : Parker) :
    x * ⟨x.code, x.sign + P x.code⟩ = 1 ∧ ⟨x.code, x.sign + P x.code⟩ * x = 1 := by
  constructor <;> ext <;> simp only [mul_code, mul_sign, one_code, one_sign, add_self_C, θ_self]
  · linear_combination (x.sign + P x.code) * two_eq_zero'
  · linear_combination (x.sign + P x.code) * two_eq_zero'

theorem mul_self (x : Parker) : x * x = ⟨0, P x.code⟩ := by
  ext
  · simp [add_self_C]
  · simp only [mul_sign, θ_self]
    linear_combination x.sign * two_eq_zero'

theorem mul_comm' (x y : Parker) : y * x = x * y * ⟨0, K x.code y.code⟩ := by
  ext
  · simp only [mul_code, add_zero]; exact add_comm _ _
  · simp only [mul_sign, mul_code, θ_zero_right, add_zero, θ_swap x.code y.code]
    ring

theorem mul_assoc' (x y z : Parker) :
    x * (y * z) = x * y * z * ⟨0, A x.code y.code z.code⟩ := by
  ext
  · simp only [mul_code, add_zero]; exact (add_assoc _ _ _).symm
  · simp only [mul_sign, mul_code, θ_zero_right, add_zero, θ_add_left, θ_add_right]
    linear_combination -(A x.code y.code z.code) * two_eq_zero'

end Parker

theorem P_bvec (a : ℕ) : P (bvec 24 a) = ((popc 24 a / 4 : ℕ) : ZMod 2) := by
  rw [P, hammingNorm_bvec]

theorem K_bvec (a b : ℕ) : K (bvec 24 a) (bvec 24 b) = ((popc 24 (a &&& b) / 2 : ℕ) : ZMod 2) := by
  rw [K_eq, ← bvec_and, hammingNorm_bvec]

theorem β_bvec (i j : Fin 12) : β i j = if i < j then 0 else if i = j then
    ((popc 24 (Bmask i) / 4 : ℕ) : ZMod 2) else ((popc 24 (Bmask i &&& Bmask j) / 2 : ℕ) : ZMod 2) := by
  rw [β, B_eq_bvec, B_eq_bvec, P_bvec, K_bvec]

@[expose] def ι6 : Fin 6 → Fin 12 := Fin.castLE (by norm_num)

theorem B_ι6 : ∀ j, B (ι6 j) = g j := by decide

theorem β_grey : ∀ (i : Fin 6) (j : Fin 12), β (ι6 i) j = 0 := by
  intro i j
  rw [β_bvec]
  revert i j
  decide

@[expose] def greyWeight (μ : Fin 6 → ZMod 2) : ℕ := ∑ j, (μ j).val

@[expose] def greyGamma (μ : Fin 6 → ZMod 2) : Fin 24 → ZMod 2 := ∑ j, μ j • γ j

@[expose] def greyVec (μ : Fin 6 → ZMod 2) : Fin 24 → ZMod 2 :=
  (((greyWeight μ : ℤ) - 1 : ℤ) : ZMod 2) • greyGamma μ +
    (((greyWeight μ).choose 2 : ℕ) : ZMod 2) • ωInf

@[expose] def greyCoords (μ : Fin 6 → ZMod 2) : Fin 12 → ZMod 2 := ∑ j, μ j • Pi.single (ι6 j) 1

theorem ι6_injective : Function.Injective ι6 := Fin.castLE_injective _

theorem greyCoords_ι6 (μ : Fin 6 → ZMod 2) (j : Fin 6) : greyCoords μ (ι6 j) = μ j := by
  rw [greyCoords, Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [ι6_injective.ne (Ne.symm hk)]
  · simp

theorem greyCoords_of_not_mem (μ : Fin 6 → ZMod 2) {i : Fin 12} (hi : i ∉ Set.range ι6) :
    greyCoords μ i = 0 := by
  rw [greyCoords, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : i ≠ ι6 k := fun h => hi ⟨k, h.symm⟩
  simp [this]

theorem repr_grey (μ : Fin 6 → ZMod 2) (e : C) (he : (e : Fin 24 → ZMod 2) = ∑ j, μ j • g j) :
    ⇑(basisC.repr e) = greyCoords μ := by
  funext i
  rw [repr_apply, he, map_sum, greyCoords]
  simp only [map_smul, ← B_ι6, ψ_B]

private theorem g_mul_g : ∀ i j : Fin 6, i ≠ j → g i * g j = ωInf + γ i + γ j := by decide

private theorem ZMod2_six : ∀ a b c d e f : ZMod 2,
    (∑ i : Fin 6, ∑ j : Fin 6,
      (if i < j then ![a, b, c, d, e, f] i * ![a, b, c, d, e, f] j else 0) • (ωInf + γ i + γ j)) =
      greyVec ![a, b, c, d, e, f] := by
  decide +kernel

theorem greyVec_eq (μ : Fin 6 → ZMod 2) :
    (∑ i : Fin 6, ∑ j : Fin 6, (if i < j then μ i * μ j else 0) • (ωInf + γ i + γ j)) =
      greyVec μ := by
  have hμ : μ = ![μ 0, μ 1, μ 2, μ 3, μ 4, μ 5] := by
    funext i; fin_cases i <;> rfl
  rw [hμ]
  exact ZMod2_six _ _ _ _ _ _

theorem θc_greyCoords (μ : Fin 6 → ZMod 2) (ν : Fin 12 → ZMod 2) :
    θc (greyCoords μ) ν = ∑ i : Fin 6, ∑ j : Fin 6,
      (if i < j then μ i * μ j else 0) * A (g i) (g j) (∑ k, ν k • B k) := by
  rw [θc_eq]
  have h1 : ∑ i, ∑ j, greyCoords μ i * ν j * β i j = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hi : i ∈ Set.range ι6
    · obtain ⟨i', rfl⟩ := hi
      rw [β_grey, mul_zero]
    · rw [greyCoords_of_not_mem μ hi, zero_mul, zero_mul]
  rw [h1, zero_add]
  have h2 : ∀ i j, ∑ k, lt01 i j * greyCoords μ i * greyCoords μ j * ν k * Ab i j k =
      lt01 i j * greyCoords μ i * greyCoords μ j * A (B i) (B j) (∑ k, ν k • B k) := by
    intro i j
    rw [A_sum_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Ab]; ring
  simp only [h2]
  symm
  refine Fintype.sum_of_injective ι6 ι6_injective _ _ (fun i hi => ?_) (fun i => ?_)
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [greyCoords_of_not_mem μ hi, mul_zero, zero_mul, zero_mul]
  · refine Fintype.sum_of_injective ι6 ι6_injective _ _ (fun j hj => ?_) (fun j => ?_)
    · rw [greyCoords_of_not_mem μ hj, mul_zero, zero_mul]
    · rw [greyCoords_ι6, greyCoords_ι6, B_ι6, B_ι6]
      simp only [lt01, ι6, Fin.castLE_lt_castLE_iff]
      split_ifs <;> ring

theorem A_eq_dotProduct (x y z : Fin 24 → ZMod 2) : A x y z = z ⬝ᵥ (x * y) := by
  rw [A_eq_sum, dotProduct]
  exact Finset.sum_congr rfl fun k _ => by simp only [Pi.mul_apply]; ring

theorem θ_grey (μ : Fin 6 → ZMod 2) (e f : C)
    (he : (e : Fin 24 → ZMod 2) = ∑ j, μ j • g j) :
    θ e f = (f : Fin 24 → ZMod 2) ⬝ᵥ greyVec μ := by
  rw [θ, repr_grey μ e he, θc_greyCoords, ← coe_eq_sum, ← greyVec_eq, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  split_ifs with h
  · rw [A_eq_dotProduct, g_mul_g i j (ne_of_lt h)]
  · rw [zero_mul, zero_mul]

private theorem greyVec_one : greyVec (fun _ => 1) = 0 := by decide

theorem θ_Ω (f : C) : θ ⟨Ω, Ω_mem_C⟩ f = 0 := by
  have hΩ : ((⟨Ω, Ω_mem_C⟩ : C) : Fin 24 → ZMod 2) = ∑ j, (fun _ => (1 : ZMod 2)) j • g j := by
    simp only [one_smul]
    exact Ω_eq_sum_g
  rw [θ_grey (fun _ => 1) _ f hΩ, greyVec_one, dotProduct_zero]

theorem θ_add_Ω (d f : C) : θ (d + ⟨Ω, Ω_mem_C⟩) f = θ d f := by
  rw [θ_add_left, θ_Ω, add_zero]
  have : A d Ω f = 0 := by
    calc A d Ω f = ∑ i, (d : Fin 24 → ZMod 2) i * (f : Fin 24 → ZMod 2) i := by
          rw [A_eq_sum]
          exact Finset.sum_congr rfl fun i _ => by simp [Ω]
      _ = (d : Fin 24 → ZMod 2) ⬝ᵥ f := rfl
      _ = 0 := dotProduct_eq_zero d.2 f.2
  rw [this, add_zero]

@[expose] def colourGamma (h : Fin 24 → ZMod 2) : Fin 24 → ZMod 2 :=
  fun i => if row i = 0 ∧ ∃ r, h (coord r (col i)) ≠ 0 then 1 else 0

theorem l_dotProduct_greyVec (y : Fin 6 → F4) (μ : Fin 6 → ZMod 2) : l y ⬝ᵥ greyVec μ = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : row i = 0
  · rw [l_apply, hi, show lCol (y (col i)) 0 = 0 by
      rcases F4.mem_cases (y (col i)) with h | h | h | h <;> rw [h] <;> decide, zero_mul]
  · have hγ : ∀ j, γ j i = 0 := by
      intro j
      have hne : i ≠ coord 0 j := by
        rintro rfl
        exact hi (row_coord 0 j)
      simp [γ, hne]
    have : greyVec μ i = 0 := by
      simp [greyVec, greyGamma, Finset.sum_apply, hγ, ωInf, hi]
    rw [this, mul_zero]

theorem θ_grey_colour {e h : C} (he : (e : Fin 24 → ZMod 2) ∈ G) (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    θ e h = 0 := by
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 he
  obtain ⟨y, -, hy⟩ := hh
  rw [θ_grey μ e h hμ.symm, ← hy, l_dotProduct_greyVec]

private theorem K_colour : ∀ a b c : F4, ∀ j : Fin 6,
    K (l (a • v₁ + b • v₂ + c • v₃)) (g j) = g j ⬝ᵥ colourGamma (l (a • v₁ + b • v₂ + c • v₃)) := by
  decide +kernel

noncomputable def θRight (d : C) : C →ₗ[ZMod 2] ZMod 2 where
  toFun := θ d
  map_add' := θ_add_right d
  map_smul' c e := by rw [θ_smul_right, smul_eq_mul, RingHom.id_apply]

theorem θ_colour_grey {e h : C} (he : (e : Fin 24 → ZMod 2) ∈ G) (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    θ h e = (e : Fin 24 → ZMod 2) ⬝ᵥ colourGamma h := by
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 he
  obtain ⟨y, hy, hyh⟩ := hh
  have hy' := (mem_H₆_iff y).1 hy
  let gC : Fin 6 → C := fun j => ⟨g j, g_mem_C j⟩
  have he' : e = ∑ j, μ j • gC j := by
    apply Subtype.ext
    rw [← hμ, Submodule.coe_sum]
    rfl
  have hgj : ∀ j, θ h (gC j) = g j ⬝ᵥ colourGamma h := by
    intro j
    rw [θ_swap (gC j) h, θ_grey_colour (Submodule.subset_span ⟨j, rfl⟩) ⟨y, hy, hyh⟩, zero_add,
      K_comm, ← hyh, hy']
    exact K_colour _ _ _ j
  rw [he']
  calc θ h (∑ j, μ j • gC j) = θRight h (∑ j, μ j • gC j) := rfl
    _ = ∑ j, μ j * θ h (gC j) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      rfl
    _ = ∑ j, μ j * (g j ⬝ᵥ colourGamma h) := by simp only [hgj]
    _ = ((∑ j, μ j • gC j : C) : Fin 24 → ZMod 2) ⬝ᵥ colourGamma h := by
      rw [Submodule.coe_sum, sum_dotProduct]
      simp only [Submodule.coe_smul, smul_dotProduct, smul_eq_mul]
      rfl

theorem mog_loop_and_cocycle_identities :
    (∀ d : C, θ d d = P d) ∧
    (∀ d e : C, θ d e + θ e d = K d e) ∧
    (∀ d e f : C, θ (d + e) f = θ d f + θ e f + A d e f) ∧
    (∀ d e f : C, θ d (e + f) = θ d e + θ d f) ∧
    IsMoufangLoop Parker ∧ Nat.card Parker = 8192 ∧
    (∀ x y : Parker, Parker.negOne * x = x * Parker.negOne ∧
      Parker.negOne * x * y = Parker.negOne * (x * y) ∧
      x * Parker.negOne * y = x * (Parker.negOne * y) ∧
      x * y * Parker.negOne = x * (y * Parker.negOne)) ∧
    (∀ x : Parker, x * ⟨x.code, x.sign + P x.code⟩ = 1 ∧ ⟨x.code, x.sign + P x.code⟩ * x = 1) ∧
    (∀ x : Parker, x * x = ⟨0, P x.code⟩) ∧
    (∀ x y : Parker, y * x = x * y * ⟨0, K x.code y.code⟩) ∧
    (∀ x y z : Parker, x * (y * z) = x * y * z * ⟨0, A x.code y.code z.code⟩) ∧
    (∀ d f : C, θ (d + ⟨Ω, Ω_mem_C⟩) f = θ d f) ∧
    (∀ (μ : Fin 6 → ZMod 2) (e f : C), (e : Fin 24 → ZMod 2) = ∑ j, μ j • g j →
      θ e f = (f : Fin 24 → ZMod 2) ⬝ᵥ ((((greyWeight μ : ℤ) - 1 : ℤ) : ZMod 2) • greyGamma μ +
        (((greyWeight μ).choose 2 : ℕ) : ZMod 2) • ωInf)) ∧
    (∀ e h : C, (e : Fin 24 → ZMod 2) ∈ G → (h : Fin 24 → ZMod 2) ∈ H →
      θ e h = 0 ∧ θ h e = (e : Fin 24 → ZMod 2) ⬝ᵥ colourGamma h) :=
  ⟨θ_self, θ_add_θ_swap, θ_add_left, θ_add_right, Parker.isMoufangLoop, Parker.card,
    Parker.negOne_central, Parker.mul_inv, Parker.mul_self, Parker.mul_comm', Parker.mul_assoc',
    θ_add_Ω, fun μ e f he => θ_grey μ e f he,
    fun _ _ he hh => ⟨θ_grey_colour he hh, θ_colour_grey he hh⟩⟩

end CFSG.Monster.Code
