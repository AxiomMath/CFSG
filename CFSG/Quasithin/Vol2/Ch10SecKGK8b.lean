module

public import CFSG.Quasithin.Vol2.Ch10SecCFacts
public import CFSG.Quasithin.Vol2.Ch10SecKGIrr

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Quasithin CFSG.Blueprint Matrix

namespace C10KG

variable (a : ℕ) {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem det_suzukiS_eq_one (u v : K) : (suzukiS a u v).det = 1 := by
  rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular]
  · simp [suzukiS, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [suzukiS]

omit [CharP K 2] in
variable (K) in
theorem suzukiW_mul_suzukiW : suzukiW K * suzukiW K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW, Matrix.mul_apply, Fin.sum_univ_four]

theorem suzukiS_mulVec_add (u v : K) (x : Fin 4 → K) : suzukiS a u v *ᵥ x + x =
    ![0, u * x 0, v * x 0 + u ^ 2 ^ (a + 1) * x 1,
      suzukiN a u v * x 0 + (u ^ (2 ^ (a + 1) + 1) + v) * x 1 + u * x 2] := by
  ext i
  fin_cases i <;> simp [suzukiS, dotProduct, Fin.sum_univ_four] <;> ring_nf <;>
    simp [CharTwo.two_eq_zero]

omit [CharP K 2] in
theorem suzukiW_mulVec (x : Fin 4 → K) : suzukiW K *ᵥ x = ![x 3, x 2, x 1, x 0] := by
  ext i
  fin_cases i <;> simp [suzukiW, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem sz_mem_of_ne {T : Set (Fin 4 → K)} (hadd : ∀ x ∈ T, ∀ y ∈ T, x + y ∈ T)
    (hS : ∀ u v : K, ∀ x ∈ T, suzukiS a u v *ᵥ x ∈ T) (hW : ∀ x ∈ T, suzukiW K *ᵥ x ∈ T)
    {x : Fin 4 → K} (hx : x ∈ T) (hx0 : x ≠ 0) (z : Fin 4 → K) : z ∈ T := by
  have hD : ∀ u v : K, ∀ y ∈ T, suzukiS a u v *ᵥ y + y ∈ T := fun u v y hy =>
    hadd _ (hS u v y hy) y hy
  have hN01 : suzukiN a (0 : K) 1 = 1 := by simp [suzukiN]
  have hN10 : suzukiN a (1 : K) 0 = 1 := by simp [suzukiN]
  have step0 : ∀ y ∈ T, y 0 ≠ 0 → ∃ y₂ y₃ : K, ![0, 0, y₂, y₃] ∈ T ∧ y₂ ≠ 0 := by
    intro y hy hy0
    refine ⟨y 0, y 0 + y 1, ?_, hy0⟩
    have := hD 0 1 y hy
    rw [suzukiS_mulVec_add, hN01] at this
    convert this using 1
    ext i
    fin_cases i <;> simp
  obtain ⟨y₂, y₃, hy, hy₂⟩ : ∃ y₂ y₃ : K, ![0, 0, y₂, y₃] ∈ T ∧ y₂ ≠ 0 := by
    by_cases h0 : x 0 = 0
    · by_cases h1 : x 1 = 0
      · by_cases h2 : x 2 = 0
        · have h3 : x 3 ≠ 0 := fun h3 => hx0 (by
            ext i
            fin_cases i <;> simp [h0, h1, h2, h3])
          refine step0 _ (hW x hx) ?_
          rw [suzukiW_mulVec]
          simpa using h3
        · refine ⟨x 2, x 3, ?_, h2⟩
          convert hx using 1
          ext i
          fin_cases i <;> simp [h0, h1]
      · refine ⟨x 1, x 1 + x 2, ?_, h1⟩
        have := hD 1 0 x hx
        rw [suzukiS_mulVec_add, hN10, h0] at this
        convert this using 1
        ext i
        fin_cases i <;> simp
    · exact step0 x hx h0
  have he₄ : ∀ c : K, ![0, 0, 0, c] ∈ T := by
    intro c
    have := hD (c / y₂) 0 _ hy
    rw [suzukiS_mulVec_add] at this
    convert this using 1
    ext i
    fin_cases i <;> simp [hy₂]
  have he₁ : ∀ c : K, ![c, 0, 0, 0] ∈ T := fun c => by
    have := hW _ (he₄ c)
    rwa [suzukiW_mulVec] at this
  have h110 : ∀ c : K, ![c, c, 0, c] ∈ T := fun c => by
    have := hS 1 0 _ (he₁ c)
    convert this using 1
    ext i
    fin_cases i <;> simp [suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hN10]
  have h101 : ∀ c : K, ![c, 0, c, c] ∈ T := fun c => by
    have := hS 0 1 _ (he₁ c)
    convert this using 1
    ext i
    fin_cases i <;> simp [suzukiS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hN01]
  have hz : z = ![z 1, z 1, 0, z 1] + ![z 2, 0, z 2, z 2] + ![z 0 + z 1 + z 2, 0, 0, 0] +
      ![0, 0, 0, z 3 + z 1 + z 2] := by
    ext i
    fin_cases i <;> simp <;> ring_nf <;> simp [CharTwo.two_eq_zero]
  rw [hz]
  exact hadd _ (hadd _ (hadd _ (h110 _) _ (h101 _)) _ (he₁ _)) _ (he₄ _)

end C10KG

theorem factK8b_holds : FactK8b := by
  intro V _ _ Hm U Z f h
  obtain ⟨a, -, -, K, _, _, hK, π, hRV⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  refine C10KG.isIrrSec_of_realizesVia hRV rfl
    ⟨Multiplicative.ofAdd ![(1 : K), 0, 0, 0], trivial, ?_⟩ ?_
  · intro h1
    have h1' : (Multiplicative.ofAdd ![(1 : K), 0, 0, 0] : Multiplicative (Fin 4 → K)) = 1 := h1
    have h2 := congrArg Multiplicative.toAdd h1'
    rw [toAdd_ofAdd, toAdd_one] at h2
    have := congrFun h2 0
    simp at this
  · intro S _ hSinv
    by_cases hbot : S = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨⟨m₀', hm₀S⟩, hm₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    let m₀ : Multiplicative (Fin 4 → K) := m₀'
    let T : Set (Fin 4 → K) := {x | Multiplicative.ofAdd x ∈ S}
    have hadd : ∀ x ∈ T, ∀ y ∈ T, x + y ∈ T := fun x hx y hy => S.mul_mem hx hy
    have hS : ∀ u v : K, ∀ x ∈ T, suzukiS a u v *ᵥ x ∈ T := fun u v x hx =>
      hSinv ⟨GeneralLinearGroup.mkOfDetNeZero (suzukiS a u v)
        (by rw [C10KG.det_suzukiS_eq_one]; exact one_ne_zero),
        Subgroup.subset_closure (Or.inl ⟨u, v, rfl⟩)⟩ _ hx
    have hW : ∀ x ∈ T, suzukiW K *ᵥ x ∈ T := fun x hx =>
      hSinv ⟨⟨suzukiW K, suzukiW K, C10KG.suzukiW_mul_suzukiW K, C10KG.suzukiW_mul_suzukiW K⟩,
        Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩ _ hx
    have hX0 : Multiplicative.toAdd m₀ ≠ 0 := fun h0 => hm₀1 (Subtype.ext (by
      change m₀ = 1
      rw [← ofAdd_toAdd m₀, h0, ofAdd_zero]))
    have hX : Multiplicative.toAdd m₀ ∈ T := by
      change Multiplicative.ofAdd (Multiplicative.toAdd m₀) ∈ S
      rw [ofAdd_toAdd]
      exact hm₀S
    change S = ⊤
    refine eq_top_iff.mpr fun m _ => ?_
    let m' : Multiplicative (Fin 4 → K) := m
    have hm' := C10KG.sz_mem_of_ne a hadd hS hW hX hX0 (Multiplicative.toAdd m')
    change Multiplicative.ofAdd (Multiplicative.toAdd m') ∈ S at hm'
    rwa [ofAdd_toAdd] at hm'

end CFSG.Quasithin.Vol2.Ch10.SecC
