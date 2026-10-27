module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Weights

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Quasithin.SmithCurtis Module

theorem injective_fin_three {α : Type*} {f : Fin 3 → α} (h01 : f 0 ≠ f 1) (h02 : f 0 ≠ f 2)
    (h12 : f 1 ≠ f 2) : Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij h01 | exact absurd hij.symm h01
    | exact absurd hij h02 | exact absurd hij.symm h02
    | exact absurd hij h12 | exact absurd hij.symm h12

theorem injective_fin_two {α : Type*} {f : Fin 2 → α} (h01 : f 0 ≠ f 1) :
    Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij h01 | exact absurd hij.symm h01

section Fields

variable {k : Type*} [Field k]

theorem mul_ne_right_of_ne_one {x y : k} (hx : x ≠ 1) (hy : y ≠ 0) : y ≠ x * y := fun h =>
  hx (by
    have := h.symm
    rwa [mul_eq_right₀ hy] at this)

theorem ne_inv_of_mul_ne_one {x y : k} (hy : y ≠ 0) (h : x * y ≠ 1) : x ≠ y⁻¹ := fun e =>
  h (by rw [e, inv_mul_cancel₀ hy])

end Fields

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
  {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {ρ : Representation k (StatedSp 3 K) V} {y₀ : V} {χ : StatedSp 3 K → k} {μ : Fin 3 → k}

theorem fin_three_zero_ne_one : (0 : Fin 3) ≠ 1 := by decide

theorem fin_three_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide

omit [CharP k 2] in
theorem three_le_finrank_of_weyl (hK : 4 ≤ Fintype.card K)
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {z : StatedSp 2 K} (hz : z ≠ 1)
    (n₀ n₁ n₂ : StatedSp 3 K) (π₀ π₁ π₂ : (Fin 3 → Kˣ) → (Fin 3 → Kˣ))
    (hπ₀ : ∀ t, n₀⁻¹ * diagHom 3 K t * n₀ = diagHom 3 K (π₀ t))
    (hπ₁ : ∀ t, n₁⁻¹ * diagHom 3 K t * n₁ = diagHom 3 K (π₁ t))
    (hπ₂ : ∀ t, n₂⁻¹ * diagHom 3 K t * n₂ = diagHom 3 K (π₂ t))
    (b₀ b₁ b₂ : Kˣ → k) (hb₀ : ∀ a, χ (diagHom 3 K (π₀ (Pi.mulSingle 0 a))) = b₀ a)
    (hb₁ : ∀ a, χ (diagHom 3 K (π₁ (Pi.mulSingle 0 a))) = b₁ a)
    (hb₂ : ∀ a, χ (diagHom 3 K (π₂ (Pi.mulSingle 0 a))) = b₂ a)
    (h01 : ∃ a, b₀ a ≠ b₁ a) (h02 : ∃ a, b₀ a ≠ b₂ a) (h12 : ∃ a, b₁ a ≠ b₂ a)
    (hm₀ : ∃ (c : Fin 2) (a : Kˣ), χ (diagHom 3 K (π₀ (Pi.mulSingle c.succ a))) ≠ 1)
    (hm₁ : ∃ (c : Fin 2) (a : Kˣ), χ (diagHom 3 K (π₁ (Pi.mulSingle c.succ a))) ≠ 1)
    (hm₂ : ∃ (c : Fin 2) (a : Kˣ), χ (diagHom 3 K (π₂ (Pi.mulSingle c.succ a))) ≠ 1) :
    3 ≤ finrank k (LinearMap.range (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) := by
  have hb : (fun (j : Fin 3) (a : Kˣ) => χ (diagHom 3 K (![π₀, π₁, π₂] j (Pi.mulSingle 0 a)))) =
      ![b₀, b₁, b₂] := by
    funext j a
    fin_cases j
    · exact hb₀ a
    · exact hb₁ a
    · exact hb₂ a
  refine le_finrank_of_weyl hK ht hz ![n₀, n₁, n₂] ![π₀, π₁, π₂] ?_ ?_ ?_
  · intro j t
    fin_cases j
    · exact hπ₀ t
    · exact hπ₁ t
    · exact hπ₂ t
  · rw [hb]
    obtain ⟨a₁, ha₁⟩ := h01
    obtain ⟨a₂, ha₂⟩ := h02
    obtain ⟨a₃, ha₃⟩ := h12
    exact injective_fin_three (fun h => ha₁ (congrFun h a₁)) (fun h => ha₂ (congrFun h a₂))
      (fun h => ha₃ (congrFun h a₃))
  · intro j
    fin_cases j
    · exact hm₀
    · exact hm₁
    · exact hm₂

omit [CharP k 2] in
theorem two_le_finrank_of_weyl (hK : 4 ≤ Fintype.card K)
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {z : StatedSp 2 K} (hz : z ≠ 1)
    (n₀ n₁ : StatedSp 3 K) (π₀ π₁ : (Fin 3 → Kˣ) → (Fin 3 → Kˣ))
    (hπ₀ : ∀ t, n₀⁻¹ * diagHom 3 K t * n₀ = diagHom 3 K (π₀ t))
    (hπ₁ : ∀ t, n₁⁻¹ * diagHom 3 K t * n₁ = diagHom 3 K (π₁ t))
    (b₀ b₁ : Kˣ → k) (hb₀ : ∀ a, χ (diagHom 3 K (π₀ (Pi.mulSingle 0 a))) = b₀ a)
    (hb₁ : ∀ a, χ (diagHom 3 K (π₁ (Pi.mulSingle 0 a))) = b₁ a) (h01 : ∃ a, b₀ a ≠ b₁ a)
    (hm₀ : ∃ (c : Fin 2) (a : Kˣ), χ (diagHom 3 K (π₀ (Pi.mulSingle c.succ a))) ≠ 1)
    (hm₁ : ∃ (c : Fin 2) (a : Kˣ), χ (diagHom 3 K (π₁ (Pi.mulSingle c.succ a))) ≠ 1) :
    2 ≤ finrank k (LinearMap.range (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) := by
  have hb : (fun (j : Fin 2) (a : Kˣ) => χ (diagHom 3 K (![π₀, π₁] j (Pi.mulSingle 0 a)))) =
      ![b₀, b₁] := by
    funext j a
    fin_cases j
    · exact hb₀ a
    · exact hb₁ a
  refine le_finrank_of_weyl hK ht hz ![n₀, n₁] ![π₀, π₁] ?_ ?_ ?_
  · intro j t
    fin_cases j
    · exact hπ₀ t
    · exact hπ₁ t
  · rw [hb]
    obtain ⟨a₁, ha₁⟩ := h01
    exact injective_fin_two (fun h => ha₁ (congrFun h a₁))
  · intro j
    fin_cases j
    · exact hm₀
    · exact hm₁

omit [Fintype K] [CharP K 2] in
theorem one_inv_conj_diagHom (t : Fin 3 → Kˣ) :
    (1 : StatedSp 3 K)⁻¹ * diagHom 3 K t * 1 = diagHom 3 K (id t) := by
  simp

omit [Fintype K] [CharP K 2] in
theorem lw_sw_inv_conj_diagHom (t : Fin 3 → Kˣ) :
    (lw 0 * sw fin_three_zero_ne_two)⁻¹ * diagHom 3 K t * (lw 0 * sw fin_three_zero_ne_two) =
      diagHom 3 K ((Function.update t 0 (t 0)⁻¹) ∘ Equiv.swap 0 2) := by
  rw [show (lw 0 * sw fin_three_zero_ne_two)⁻¹ * diagHom 3 K t * (lw 0 * sw fin_three_zero_ne_two) =
      (sw fin_three_zero_ne_two)⁻¹ * ((lw 0)⁻¹ * diagHom 3 K t * lw 0) * sw fin_three_zero_ne_two by group,
    lw_inv_conj_diagHom, sw_inv_conj_diagHom]

theorem three_le_finrank_A (hK : 4 ≤ Fintype.card K)
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {z : StatedSp 2 K} (hz : z ≠ 1)
    (h0 : ∃ a, epsChar χ 0 a ≠ 1) (h12 : (∃ a, epsChar χ 1 a ≠ 1) ∨ ∃ a, epsChar χ 2 a ≠ 1)
    (h20 : ∃ a, epsChar χ 2 a ≠ epsChar χ 0 a)
    (h20' : ∃ a, epsChar χ 2 a ≠ (epsChar χ 0 a)⁻¹) :
    3 ≤ finrank k (LinearMap.range (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) := by
  classical
  refine three_le_finrank_of_weyl hK ht hz 1 (lw 0) (sw fin_three_zero_ne_two) id
    (fun t => Function.update t 0 (t 0)⁻¹) (fun t => t ∘ Equiv.swap 0 2)
    one_inv_conj_diagHom (lw_inv_conj_diagHom 0) (sw_inv_conj_diagHom fin_three_zero_ne_two)
    (epsChar χ 0) (fun a => epsChar χ 0 a⁻¹) (epsChar χ 2) (fun a => rfl)
    (fun a => by rw [update_mulSingle_self]; rfl)
    (fun a => by rw [mulSingle_comp_swap, Equiv.swap_apply_left]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨a, ha⟩ := h0
    exact ⟨a, ne_of_mul_eq_one_charTwo ha (epsChar_mul_inv ht 0 a)⟩
  · obtain ⟨a, ha⟩ := h20
    exact ⟨a, fun h => ha h.symm⟩
  · obtain ⟨a, ha⟩ := h20'
    exact ⟨a, fun h => ha (by rw [← epsChar_inv ht]; exact h.symm)⟩
  · rcases h12 with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨0, a, ha⟩
    · exact ⟨1, a, ha⟩
  · rcases h12 with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨0, a, by rw [update_mulSingle_of_ne (by decide)]; exact ha⟩
    · exact ⟨1, a, by rw [update_mulSingle_of_ne (by decide)]; exact ha⟩
  · obtain ⟨a, ha⟩ := h0
    exact ⟨1, a, by rw [mulSingle_comp_swap]; exact ha⟩

theorem three_le_finrank_B (hK : 4 ≤ Fintype.card K)
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {z : StatedSp 2 K} (hz : z ≠ 1)
    (h0 : ∃ a, epsChar χ 0 a ≠ 1) (h12 : (∃ a, epsChar χ 1 a ≠ 1) ∨ ∃ a, epsChar χ 2 a ≠ 1)
    (h10 : ∃ a, epsChar χ 1 a ≠ epsChar χ 0 a)
    (h10' : ∃ a, epsChar χ 1 a ≠ (epsChar χ 0 a)⁻¹) :
    3 ≤ finrank k (LinearMap.range (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) := by
  classical
  refine three_le_finrank_of_weyl hK ht hz 1 (lw 0) (sw fin_three_zero_ne_one) id
    (fun t => Function.update t 0 (t 0)⁻¹) (fun t => t ∘ Equiv.swap 0 1)
    one_inv_conj_diagHom (lw_inv_conj_diagHom 0) (sw_inv_conj_diagHom fin_three_zero_ne_one)
    (epsChar χ 0) (fun a => epsChar χ 0 a⁻¹) (epsChar χ 1) (fun a => rfl)
    (fun a => by rw [update_mulSingle_self]; rfl)
    (fun a => by rw [mulSingle_comp_swap, Equiv.swap_apply_left]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨a, ha⟩ := h0
    exact ⟨a, ne_of_mul_eq_one_charTwo ha (epsChar_mul_inv ht 0 a)⟩
  · obtain ⟨a, ha⟩ := h10
    exact ⟨a, fun h => ha h.symm⟩
  · obtain ⟨a, ha⟩ := h10'
    exact ⟨a, fun h => ha (by rw [← epsChar_inv ht]; exact h.symm)⟩
  · rcases h12 with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨0, a, ha⟩
    · exact ⟨1, a, ha⟩
  · rcases h12 with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨0, a, by rw [update_mulSingle_of_ne (by decide)]; exact ha⟩
    · exact ⟨1, a, by rw [update_mulSingle_of_ne (by decide)]; exact ha⟩
  · obtain ⟨a, ha⟩ := h0
    exact ⟨0, a, by rw [mulSingle_comp_swap]; exact ha⟩

theorem three_le_finrank_C (hK : 4 ≤ Fintype.card K)
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {z : StatedSp 2 K} (hz : z ≠ 1)
    (h2 : ∃ a, epsChar χ 2 a ≠ 1) (h01 : (∃ a, epsChar χ 0 a ≠ 1) ∨ ∃ a, epsChar χ 1 a ≠ 1)
    (h02 : ∃ a, epsChar χ 0 a ≠ epsChar χ 2 a)
    (h02' : ∃ a, epsChar χ 0 a ≠ (epsChar χ 2 a)⁻¹) :
    3 ≤ finrank k (LinearMap.range (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) := by
  classical
  refine three_le_finrank_of_weyl hK ht hz (sw fin_three_zero_ne_two)
    (lw 0 * sw fin_three_zero_ne_two) 1 (fun t => t ∘ Equiv.swap 0 2)
    (fun t => (Function.update t 0 (t 0)⁻¹) ∘ Equiv.swap 0 2) id
    (sw_inv_conj_diagHom fin_three_zero_ne_two) lw_sw_inv_conj_diagHom one_inv_conj_diagHom
    (epsChar χ 2) (fun a => epsChar χ 2 a⁻¹) (epsChar χ 0)
    (fun a => by rw [mulSingle_comp_swap, Equiv.swap_apply_left]; rfl)
    (fun a => by rw [update_mulSingle_self, mulSingle_comp_swap, Equiv.swap_apply_left]; rfl)
    (fun a => rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨a, ha⟩ := h2
    exact ⟨a, ne_of_mul_eq_one_charTwo ha (epsChar_mul_inv ht 2 a)⟩
  · obtain ⟨a, ha⟩ := h02
    exact ⟨a, fun h => ha h.symm⟩
  · obtain ⟨a, ha⟩ := h02'
    exact ⟨a, fun h => ha (by rw [← epsChar_inv ht]; exact h.symm)⟩
  · rcases h01 with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨1, a, by rw [mulSingle_comp_swap]; exact ha⟩
    · exact ⟨0, a, by rw [mulSingle_comp_swap]; exact ha⟩
  · rcases h01 with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨1, a, by rw [update_mulSingle_of_ne (by decide), mulSingle_comp_swap]; exact ha⟩
    · exact ⟨0, a, by rw [update_mulSingle_of_ne (by decide), mulSingle_comp_swap]; exact ha⟩
  · obtain ⟨a, ha⟩ := h2
    exact ⟨1, a, ha⟩

omit [CharP k 2] [FiniteDimensional k V] in
theorem epsChar_two_eq (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (a : Kˣ) :
    epsChar χ 2 a = χ (corootSp 2 a) :=
  (chi_corootSp_two ht a).symm

omit [CharP k 2] [FiniteDimensional k V] in
theorem epsChar_one_eq (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (a : Kˣ) :
    epsChar χ 1 a = χ (corootSp 1 a) * epsChar χ 2 a := by
  rw [chi_corootSp_one ht, mul_assoc, inv_mul_cancel₀ (epsChar_ne_zero ht 2 a), mul_one]

omit [CharP k 2] [FiniteDimensional k V] in
theorem epsChar_zero_eq (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (a : Kˣ) :
    epsChar χ 0 a = χ (corootSp 0 a) * epsChar χ 1 a := by
  rw [chi_corootSp_zero ht, mul_assoc, inv_mul_cancel₀ (epsChar_ne_zero ht 1 a), mul_one]

theorem natural_or_spin_of_finrank_le_two (hK : 8 ≤ Fintype.card K)
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ)
    (hχ : ∀ i : Fin 3, (∀ a, χ (corootSp i a) = 1) ∨ ∃ φ : K →+* k, ∀ a, χ (corootSp i a) = φ a)
    {z : StatedSp 2 K} (hz : z ≠ 1)
    (hrk : finrank k (LinearMap.range (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) ≤ 2) :
    (∀ i a, χ (corootSp i a) = 1) ∨
      (∃ φ : K →+* k, (∀ a, χ (corootSp 0 a) = φ a) ∧ (∀ a, χ (corootSp 1 a) = 1) ∧
        ∀ a, χ (corootSp 2 a) = 1) ∨
      (∃ φ : K →+* k, (∀ a, χ (corootSp 0 a) = 1) ∧ (∀ a, χ (corootSp 1 a) = 1) ∧
        ∀ a, χ (corootSp 2 a) = φ a) := by
  have h3 : 3 ≤ Fintype.card K := by omega
  have h4 : 4 ≤ Fintype.card K := by omega
  have h5 : 5 ≤ Fintype.card K := by omega
  have e2 := epsChar_two_eq ht
  have e1 := epsChar_one_eq ht
  have e0 := epsChar_zero_eq ht
  have hne : ∀ (φ : K →+* k) (a : Kˣ), φ a ≠ 0 := fun φ a => (map_ne_zero φ).mpr a.ne_zero
  rcases hχ 0 with h0 | ⟨φ₀, h0⟩ <;> rcases hχ 1 with h1 | ⟨φ₁, h1⟩ <;>
    rcases hχ 2 with h2 | ⟨φ₂, h2⟩
  · exact Or.inl fun i a => by fin_cases i <;> simp [h0, h1, h2]
  · exact Or.inr (Or.inr ⟨φ₂, h0, h1, h2⟩)
  ·
    exfalso
    have f2 : ∀ a, epsChar χ 2 a = 1 := fun a => by rw [e2, h2]
    have f1 : ∀ a, epsChar χ 1 a = φ₁ a := fun a => by rw [e1, h1, f2, mul_one]
    have f0 : ∀ a, epsChar χ 0 a = φ₁ a := fun a => by rw [e0, h0, f1, one_mul]
    obtain ⟨a, ha⟩ := exists_ringHom_ne_one h3 φ₁
    have := three_le_finrank_A h4 ht hz ⟨a, by rwa [f0]⟩ (Or.inl ⟨a, by rwa [f1]⟩)
      ⟨a, by rw [f2, f0]; exact Ne.symm ha⟩
      ⟨a, by rw [f2, f0]; exact fun h => ha (inv_eq_one.mp h.symm)⟩
    omega
  ·
    exfalso
    have f2 : ∀ a, epsChar χ 2 a = φ₂ a := fun a => by rw [e2, h2]
    have f1 : ∀ a, epsChar χ 1 a = φ₁ a * φ₂ a := fun a => by rw [e1, h1, f2]
    have f0 : ∀ a, epsChar χ 0 a = φ₁ a * φ₂ a := fun a => by rw [e0, h0, f1, one_mul]
    obtain ⟨a, ha⟩ := exists_ringHom_mul_ne_one h5 φ₁ φ₂
    obtain ⟨b, hb⟩ := exists_ringHom_ne_one h3 φ₂
    obtain ⟨c, hc⟩ := exists_ringHom_ne_one h3 φ₁
    obtain ⟨d, hd⟩ := exists_ringHom_mul_sq_ne_one h5 φ₁ φ₂
    have := three_le_finrank_A h4 ht hz ⟨a, by rwa [f0]⟩ (Or.inr ⟨b, by rwa [f2]⟩)
      ⟨c, by rw [f2, f0]; exact mul_ne_right_of_ne_one hc (hne φ₂ c)⟩
      ⟨d, by
        rw [f2, f0]
        exact ne_inv_of_mul_ne_one (mul_ne_zero (hne φ₁ d) (hne φ₂ d))
          (by rw [show φ₂ d * (φ₁ d * φ₂ d) = φ₁ d * φ₂ d ^ 2 by ring]; exact hd)⟩
    omega
  · exact Or.inr (Or.inl ⟨φ₀, h0, h1, h2⟩)
  ·
    exfalso
    have f2 : ∀ a, epsChar χ 2 a = φ₂ a := fun a => by rw [e2, h2]
    have f1 : ∀ a, epsChar χ 1 a = φ₂ a := fun a => by rw [e1, h1, f2, one_mul]
    have f0 : ∀ a, epsChar χ 0 a = φ₀ a * φ₂ a := fun a => by rw [e0, h0, f1]
    obtain ⟨a, ha⟩ := exists_ringHom_mul_ne_one h5 φ₀ φ₂
    obtain ⟨b, hb⟩ := exists_ringHom_ne_one h3 φ₂
    obtain ⟨c, hc⟩ := exists_ringHom_ne_one h3 φ₀
    obtain ⟨d, hd⟩ := exists_ringHom_mul_sq_ne_one h5 φ₀ φ₂
    have := three_le_finrank_A h4 ht hz ⟨a, by rwa [f0]⟩ (Or.inr ⟨b, by rwa [f2]⟩)
      ⟨c, by rw [f2, f0]; exact mul_ne_right_of_ne_one hc (hne φ₂ c)⟩
      ⟨d, by
        rw [f2, f0]
        exact ne_inv_of_mul_ne_one (mul_ne_zero (hne φ₀ d) (hne φ₂ d))
          (by rw [show φ₂ d * (φ₀ d * φ₂ d) = φ₀ d * φ₂ d ^ 2 by ring]; exact hd)⟩
    omega
  ·
    exfalso
    have f2 : ∀ a, epsChar χ 2 a = 1 := fun a => by rw [e2, h2]
    have f1 : ∀ a, epsChar χ 1 a = φ₁ a := fun a => by rw [e1, h1, f2, mul_one]
    have f0 : ∀ a, epsChar χ 0 a = φ₀ a * φ₁ a := fun a => by rw [e0, h0, f1]
    obtain ⟨a, ha⟩ := exists_ringHom_mul_ne_one h5 φ₀ φ₁
    obtain ⟨b, hb⟩ := exists_ringHom_ne_one h3 φ₁
    have := three_le_finrank_A h4 ht hz ⟨a, by rwa [f0]⟩ (Or.inl ⟨b, by rwa [f1]⟩)
      ⟨a, by rw [f2, f0]; exact Ne.symm ha⟩
      ⟨a, by rw [f2, f0]; exact fun h => ha (inv_eq_one.mp h.symm)⟩
    omega
  ·
    exfalso
    have f2 : ∀ a, epsChar χ 2 a = φ₂ a := fun a => by rw [e2, h2]
    have f1 : ∀ a, epsChar χ 1 a = φ₁ a * φ₂ a := fun a => by rw [e1, h1, f2]
    obtain ⟨a, ha⟩ := exists_ringHom_mul_ne_one h5 φ₁ φ₂
    obtain ⟨b, hb⟩ := exists_ringHom_ne_one h3 φ₂
    obtain ⟨c, hc⟩ := exists_ringHom_ne_one h3 φ₁
    obtain ⟨d, hd⟩ := exists_ringHom_mul_sq_ne_one h5 φ₁ φ₂
    have hc' : epsChar χ 1 c ≠ epsChar χ 2 c := by
      rw [f1, f2]
      exact fun h => mul_ne_right_of_ne_one hc (hne φ₂ c) h.symm
    have hd' : epsChar χ 1 d ≠ (epsChar χ 2 d)⁻¹ := by
      rw [f1, f2]
      exact ne_inv_of_mul_ne_one (hne φ₂ d)
        (by rw [show φ₁ d * φ₂ d * φ₂ d = φ₁ d * φ₂ d ^ 2 by ring]; exact hd)
    by_cases hu : ∀ a, epsChar χ 0 a = 1
    · have := three_le_finrank_C h4 ht hz ⟨b, by rwa [f2]⟩ (Or.inr ⟨a, by rwa [f1]⟩)
        ⟨b, by rw [hu, f2]; exact Ne.symm hb⟩
        ⟨b, by rw [hu, f2]; exact fun h => hb (inv_eq_one.mp h.symm)⟩
      omega
    push Not at hu
    by_cases hv : (∃ a, epsChar χ 2 a ≠ epsChar χ 0 a) ∧ ∃ a, epsChar χ 2 a ≠ (epsChar χ 0 a)⁻¹
    · have := three_le_finrank_A h4 ht hz hu (Or.inr ⟨b, by rwa [f2]⟩) hv.1 hv.2
      omega
    rcases not_and_or.mp hv with hv | hv <;> push Not at hv
    ·
      have := three_le_finrank_B h4 ht hz hu (Or.inr ⟨b, by rwa [f2]⟩)
        ⟨c, by rw [← hv]; exact hc'⟩ ⟨d, by rw [← hv]; exact hd'⟩
      omega
    ·
      have hw : ∀ a, epsChar χ 0 a = (epsChar χ 2 a)⁻¹ := fun a => by rw [hv, inv_inv]
      have := three_le_finrank_B h4 ht hz hu (Or.inr ⟨b, by rwa [f2]⟩)
        ⟨d, by rw [hw]; exact hd'⟩ ⟨c, by rw [hw, inv_inv]; exact hc'⟩
      omega

theorem two_le_finrank_of_spin (hK : 4 ≤ Fintype.card K)
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (φ : K →+* k)
    (h0 : ∀ a, χ (corootSp 0 a) = 1) (h1 : ∀ a, χ (corootSp 1 a) = 1)
    (h2 : ∀ a, χ (corootSp 2 a) = φ a) {z : StatedSp 2 K} (hz : z ≠ 1) :
    2 ≤ finrank k (LinearMap.range (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) := by
  classical
  have f2 : ∀ a, epsChar χ 2 a = φ a := fun a => by rw [epsChar_two_eq ht, h2]
  have f1 : ∀ a, epsChar χ 1 a = φ a := fun a => by rw [epsChar_one_eq ht, h1, f2, one_mul]
  have f0 : ∀ a, epsChar χ 0 a = φ a := fun a => by rw [epsChar_zero_eq ht, h0, f1, one_mul]
  obtain ⟨a, ha⟩ := exists_ringHom_ne_one (by omega) φ
  refine two_le_finrank_of_weyl hK ht hz 1 (lw 0) id (fun t => Function.update t 0 (t 0)⁻¹)
    one_inv_conj_diagHom (lw_inv_conj_diagHom 0) (epsChar χ 0) (fun a => epsChar χ 0 a⁻¹)
    (fun a => rfl) (fun a => by rw [update_mulSingle_self]; rfl)
    ⟨a, ne_of_mul_eq_one_charTwo (by rwa [f0]) (epsChar_mul_inv ht 0 a)⟩
    ⟨0, a, by change epsChar χ 1 a ≠ 1; rwa [f1]⟩
    ⟨0, a, by rw [update_mulSingle_of_ne (by decide)]; change epsChar χ 1 a ≠ 1; rwa [f1]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
