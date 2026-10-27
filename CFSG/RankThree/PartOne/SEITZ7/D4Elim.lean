module

public import CFSG.RankThree.PartOne.SEITZ7.D4Rel

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3
open scoped commutatorElement

theorem le_normalizer_of_commute' {G : Type*} [Group G] {H N : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ N, x * y = y * x) : H ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h x hx y hy]
    simpa using hy
  · intro hy
    have h1 := h x⁻¹ (H.inv_mem hx) _ hy
    have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [this, h1]
    simpa using hy

theorem trace_form_eq_zero {L : Type} [Field L] (τ : L →+* L) (hτ : ∀ c, τ (τ (τ c)) = c)
    (hne : ∃ a, τ a ≠ a) {t : L}
    (h : ∀ a : L, a * τ t + τ a * τ (τ t) + τ (τ a) * t = 0) : t = 0 := by
  obtain ⟨a₀, ha₀⟩ := hne
  let f : Fin 3 → (L →* L) :=
    ![(RingHom.id L).toMonoidHom, τ.toMonoidHom, (τ.comp τ).toMonoidHom]
  have e0 : ∀ a, f 0 a = a := fun a => rfl
  have e1 : ∀ a, f 1 a = τ a := fun a => rfl
  have e2 : ∀ a, f 2 a = τ (τ a) := fun a => rfl
  have h01 : f 0 ≠ f 1 := fun e => ha₀ (by
    have := DFunLike.congr_fun e a₀
    rw [e0, e1] at this
    exact this.symm)
  have h02 : f 0 ≠ f 2 := fun e => ha₀ (by
    have := DFunLike.congr_fun e (τ a₀)
    rw [e0, e2, hτ] at this
    exact this)
  have h12 : f 1 ≠ f 2 := fun e => ha₀ (by
    have := DFunLike.congr_fun e a₀
    rw [e1, e2] at this
    have h3 := congrArg τ this
    rw [hτ] at h3
    exact this.trans h3)
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd hij h01 | exact absurd hij.symm h01
      | exact absurd hij h02 | exact absurd hij.symm h02
      | exact absurd hij h12 | exact absurd hij.symm h12
  have hli := (linearIndependent_monoidHom L L).comp f hf
  have := Fintype.linearIndependent_iff.1 hli ![τ t, τ (τ t), t] (by
    funext a
    simp only [Fin.sum_univ_three, Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    rw [e0, e1, e2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination h a)
  simpa using this 2

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] noncomputable def Upt (σ : K →+* K) : Subgroup (adjointGroup d4 K) :=
  twistedRootSubgroupD4 σ (rt 7) ⊔ twistedRootSubgroupD4 σ (rt 1)

theorem commute_xH_xA [CharP K 2] (a b : K) : xH a * xA σ b = xA σ b * xH a :=
  (((commute_22_0 a b).mul_right (commute_22_1 a (σ b))).mul_right
    (commute_22_3 a (σ (σ b)))).eq

variable {σ}

theorem mem_Upt_iff [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {g : adjointGroup d4 K} :
    g ∈ Upt σ ↔ ∃ a b : K, σ a = a ∧ g = xH a * xA σ b := by
  have hle : twistedRootSubgroupD4 σ (rt 7) ≤
      Subgroup.normalizer ((twistedRootSubgroupD4 σ (rt 1) : Subgroup (adjointGroup d4 K)) :
        Set _) := by
    refine le_normalizer_of_commute' fun x hx y hy => ?_
    obtain ⟨a, -, rfl⟩ := (mem_XH hσ x).1 hx
    obtain ⟨b, rfl⟩ := (mem_XA hσ y).1 hy
    exact commute_xH_xA σ a b
  have h := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle
  rw [← SetLike.mem_coe]
  unfold Upt
  rw [h, Set.mem_mul]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (mem_XH hσ x).1 hx
    obtain ⟨b, rfl⟩ := (mem_XA hσ y).1 hy
    exact ⟨a, b, ha, rfl⟩
  · rintro ⟨a, b, ha, rfl⟩
    exact ⟨xH a, (mem_XH hσ _).2 ⟨a, ha, rfl⟩, xA σ b, (mem_XA hσ _).2 ⟨b, rfl⟩, rfl⟩

@[expose] def mkT (x0 x1 x4 x8 x3 x7 : K) : ℕ → K := fun p =>
  if p = 0 then x0 else if p = 1 then x1 else if p = 4 then x4 else if p = 8 then x8 else
  if p = 3 then x3 else x7

theorem ordT_mkT (σ : K →+* K) (x0 x1 x4 x8 x3 x7 : K) :
    ordT σ (mkT x0 x1 x4 x8 x3 x7) =
      xB x0 * xA σ x1 * xAB σ x4 * xAAB σ x8 * xN x3 * xH x7 := by
  simp [ordT, mkT]

theorem Upt_coords [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {x0 x1 x4 x8 x3 x7 : K}
    (h : xB x0 * xA σ x1 * xAB σ x4 * xAAB σ x8 * xN x3 * xH x7 ∈ Upt σ) :
    x0 = 0 ∧ x4 = 0 ∧ x8 = 0 ∧ x3 = 0 := by
  obtain ⟨a, b, -, hab⟩ := (mem_Upt_iff hσ).1 h
  have e : xH a * xA σ b = ordT σ (mkT 0 b 0 0 0 a) := by
    rw [ordT_mkT]
    simp only [xB, xAB, xAAB, xN, xd_zero, one_mul, mul_one, map_zero, xd_zero]
    exact commute_xH_xA σ a b
  rw [e, ← ordT_mkT] at hab
  obtain ⟨h0, -, h4, h8, h3, -⟩ := ordT_inj σ hab
  simp [mkT] at h0 h4 h8 h3
  exact ⟨h0, h4, h8, h3⟩

theorem Upt_coords_A [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {u : adjointGroup d4 K}
    {x1 x4 x8 x3 x7 : K}
    (hu : u = xA σ x1 * xAB σ x4 * xAAB σ x8 * xN x3 * xH x7) (h : u ∈ Upt σ) :
    x4 = 0 ∧ x8 = 0 ∧ x3 = 0 := by
  rw [hu] at h
  have := Upt_coords hσ (x0 := 0) (x1 := x1) (x4 := x4) (x8 := x8) (x3 := x3) (x7 := x7)
    (by simpa only [xB, xd_zero, one_mul] using h)
  exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩

theorem Upt_coords_B [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {u : adjointGroup d4 K}
    {x0 x4 x8 x3 x7 : K}
    (hu : u = xB x0 * xAB σ x4 * xAAB σ x8 * xN x3 * xH x7) (h : u ∈ Upt σ) : x0 = 0 := by
  rw [hu] at h
  have := Upt_coords hσ (x0 := x0) (x1 := 0) (x4 := x4) (x8 := x8) (x3 := x3) (x7 := x7)
    (by simpa only [xA, map_zero, xd_zero, mul_one] using h)
  exact this.1

theorem Upt_coords_N [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) {u : adjointGroup d4 K}
    {x3 x7 : K} (hu : u = xN x3 * xH x7) (h : u ∈ Upt σ) : x3 = 0 := by
  rw [hu] at h
  have := Upt_coords hσ (x0 := 0) (x1 := 0) (x4 := 0) (x8 := 0) (x3 := x3) (x7 := x7)
    (by simpa only [xB, xA, xAB, xAAB, map_zero, xd_zero, one_mul] using h)
  exact this.2.2.2

theorem conj_xA_eqs [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) (hb : σ (c 0) = c 0)
    (a : K) (h : ordT σ c * xA σ a * (ordT σ c)⁻¹ ∈ Upt σ) :
    a * c 0 = 0 ∧ a * σ (c 4) + σ a * c 4 + a * σ a * c 0 = 0 ∧
      a*(σ a)*(σ (σ a))*(c 0) + a*(σ a)*(σ (σ (c 4))) + a*(σ (σ a))*(σ (c 4)) +
        a*(σ (c 1))*(σ (σ (c 4))) + a*(σ (σ (c 1)))*(σ (c 4)) + a*(σ (c 8)) +
        (σ a)*(σ (σ a))*(c 4) + (σ a)*(c 1)*(σ (σ (c 4))) + (σ a)*(σ (σ (c 1)))*(c 4) +
        (σ a)*(σ (σ (c 8))) + (σ (σ a))*(c 1)*(σ (c 4)) + (σ (σ a))*(σ (c 1))*(c 4) +
        (σ (σ a))*(c 8) = 0 := by
  exact Upt_coords_A hσ (conj_xA σ hσ c hb a) h

theorem coords_of_conj_xA [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (hne : ∃ a, σ a ≠ a)
    (c : ℕ → K) (hb : σ (c 0) = c 0)
    (h : ∀ a : K, ordT σ c * xA σ a * (ordT σ c)⁻¹ ∈ Upt σ) :
    c 0 = 0 ∧ c 4 = 0 ∧ c 8 = 0 := by
  have hc0 : c 0 = 0 := by
    have := (conj_xA_eqs hσ c hb 1 (h 1)).1
    simpa using this
  obtain ⟨a₀, ha₀⟩ := hne
  have hc4σ : σ (c 4) = c 4 := by
    have := (conj_xA_eqs hσ c hb 1 (h 1)).2.1
    rw [hc0] at this
    simp only [map_one, mul_zero, add_zero, one_mul, mul_one] at this
    exact CharTwo.add_eq_zero.1 this
  have hc4 : c 4 = 0 := by
    have := (conj_xA_eqs hσ c hb a₀ (h a₀)).2.1
    rw [hc0, hc4σ] at this
    have h2 : c 4 * (a₀ + σ a₀) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (CharTwo.add_eq_zero.1 h3).symm ha₀
  refine ⟨hc0, hc4, ?_⟩
  refine trace_form_eq_zero σ hσ ⟨a₀, ha₀⟩ (fun a => ?_)
  have := (conj_xA_eqs hσ c hb a (h a)).2.2
  rw [hc0, hc4] at this
  simp only [map_zero, mul_zero, add_zero, zero_add] at this
  linear_combination this

theorem eq_zero_of_conj_xB [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) (d : K)
    (hd : σ d = d) (h : ordT σ c * xB d * (ordT σ c)⁻¹ ∈ Upt σ) : d = 0 := by
  exact Upt_coords_B hσ (conj_xB σ hσ c d hd) h

theorem eq_zero_of_conj_xN [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) (d : K)
    (h : ordT σ c * xN d * (ordT σ c)⁻¹ ∈ Upt σ) : d = 0 := by
  exact Upt_coords_N hσ (conj_xN σ c d) h

end CFSG.RankThree.PartOne.SEITZ7
