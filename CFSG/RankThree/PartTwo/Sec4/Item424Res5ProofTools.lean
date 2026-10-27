module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item424Res5

theorem exists_normForm_eq {K : Type*} [Field K] [Finite K] (h3 : (3 : K) ≠ 0) (c : K) :
    ∃ s t : K, s ^ 2 - s * t + t ^ 2 = c := by
  have := Fintype.ofFinite K
  by_cases h2 : ringChar K = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h2 c
    exact ⟨r, 0, by rw [hr]; ring⟩
  · have hodd : Fintype.card K % 2 = 1 := by
      have := (FiniteField.even_card_iff_char_two (F := K)).not.mp h2
      omega
    have hf : (Polynomial.X ^ 2 : Polynomial K).degree = 2 := by
      rw [Polynomial.degree_X_pow]
      rfl
    have hg : (Polynomial.C 3 * Polynomial.X ^ 2 - Polynomial.C c : Polynomial K).degree = 2 := by
      rw [Polynomial.degree_sub_C (by rw [Polynomial.degree_C_mul_X_pow 2 h3]; norm_num),
        Polynomial.degree_C_mul_X_pow 2 h3]
      rfl
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at hxy
    exact ⟨x + y, 2 * y, by linear_combination hxy⟩

section Plane

variable {Y : Type*} [Group Y]

theorem closure_pair_eq {E : Subgroup Y} (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9)
    {a b : Y} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) :
    Subgroup.closure {a, b} = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.closure ({a, b} : Set Y) with hH
  have hHE : H ≤ E := (Subgroup.closure_le E).mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb)
  have haH : Subgroup.zpowers a ≤ H :=
    (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (Set.mem_insert a {b}))
  have hbH : b ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hord : orderOf a = 3 := orderOf_eq_prime (hexp a ha) ha1
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hfinH : Finite H := Finite.of_injective (Subgroup.inclusion hHE)
    (Subgroup.inclusion_injective hHE)
  have hdvd9 : Nat.card H ∣ 9 := hcard ▸ Subgroup.card_dvd_of_le hHE
  have hdvd3 : 3 ∣ Nat.card H := hza ▸ Subgroup.card_dvd_of_le haH
  have hne3 : Nat.card H ≠ 3 := by
    intro h3
    have := Subgroup.eq_of_le_of_card_ge haH (by rw [h3, hza])
    exact hba (this ▸ hbH)
  have h9 : Nat.card H = 9 := by
    have hpos : 0 < Nat.card H := Nat.card_pos
    have hle : Nat.card H ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd9
    interval_cases h : Nat.card H <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hHE (by rw [h9, hcard])

theorem weyl_of_gens {E : Subgroup Y} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcard : Nat.card E = 9) {a b g : Y} (ha : a ∈ E) (hb : b ∈ E)
    (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) (hga : g * a * g⁻¹ = b)
    (hgb : g * b * g⁻¹ = a⁻¹) :
    (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧ ∀ x ∈ E, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹ := by
  have hE := closure_pair_eq hexp hcard ha hb ha1 hba
  have hga2 : g ^ 2 * a * (g ^ 2)⁻¹ = a⁻¹ := by
    rw [pow_two, mul_inv_rev]
    calc g * g * a * (g⁻¹ * g⁻¹) = g * (g * a * g⁻¹) * g⁻¹ := by group
      _ = a⁻¹ := by rw [hga, hgb]
  have hgb2 : g ^ 2 * b * (g ^ 2)⁻¹ = b⁻¹ := by
    rw [pow_two, mul_inv_rev]
    calc g * g * b * (g⁻¹ * g⁻¹) = (g * (g * b * g⁻¹) * g⁻¹) := by group
      _ = (g * a * g⁻¹)⁻¹ := by rw [hgb]; group
      _ = b⁻¹ := by rw [hga]
  have key : ∀ x ∈ E, g * x * g⁻¹ ∈ E ∧ g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹ := by
    intro x hx
    rw [← hE] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨hga ▸ hb, hga2⟩
      · exact ⟨hgb ▸ E.inv_mem ha, hgb2⟩
    | one => exact ⟨by simp, by simp⟩
    | mul x y hx hy ihx ihy =>
      refine ⟨?_, ?_⟩
      · have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [this]
        exact E.mul_mem ihx.1 ihy.1
      · have hxE : x ∈ E := hE ▸ hx
        have hyE : y ∈ E := hE ▸ hy
        have : g ^ 2 * (x * y) * (g ^ 2)⁻¹ =
            (g ^ 2 * x * (g ^ 2)⁻¹) * (g ^ 2 * y * (g ^ 2)⁻¹) := by group
        rw [this, ihx.2, ihy.2, mul_inv_rev, hcomm _ (E.inv_mem hxE) _ (E.inv_mem hyE)]
    | inv x hx ihx =>
      refine ⟨?_, ?_⟩
      · have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [this]
        exact E.inv_mem ihx.1
      · have : g ^ 2 * x⁻¹ * (g ^ 2)⁻¹ = (g ^ 2 * x * (g ^ 2)⁻¹)⁻¹ := by group
        rw [this, ihx.2]
  exact ⟨fun x hx => (key x hx).1, fun x hx => (key x hx).2⟩

end Plane

section Automizer

variable {X : Type*} [Group X]

theorem mem_normalizer_of_sq_inv {D : Subgroup X} {h : X} (hc : ∀ x ∈ D, h * x * h⁻¹ ∈ D)
    (h2 : ∀ x ∈ D, h ^ 2 * x * (h ^ 2)⁻¹ = x⁻¹) : h ∈ Subgroup.normalizer (D : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hc x, fun hx => ?_⟩
  have hz : h ^ 2 * x⁻¹ * (h ^ 2)⁻¹ ∈ D := by
    have e : h ^ 2 * x⁻¹ * (h ^ 2)⁻¹ = h * (h * x * h⁻¹)⁻¹ * h⁻¹ := by
      rw [pow_two]
      group
    rw [e]
    exact hc _ (D.inv_mem hx)
  have h5 := h2 _ hz
  have hx' : x = h ^ 2 * x⁻¹ * (h ^ 2)⁻¹ := by
    calc x = (h ^ 2)⁻¹ * (h ^ 2 * x⁻¹ * (h ^ 2)⁻¹)⁻¹ * h ^ 2 := by group
      _ = (h ^ 2)⁻¹ * (h ^ 2 * (h ^ 2 * x⁻¹ * (h ^ 2)⁻¹) * (h ^ 2)⁻¹) * h ^ 2 := by rw [h5]
      _ = h ^ 2 * x⁻¹ * (h ^ 2)⁻¹ := by group
  rw [hx']
  exact hz

theorem exists_autIn_of_sq_inv {D : Subgroup X} {h : X} (hN : h ∈ Subgroup.normalizer (D : Set X))
    (h2 : ∀ x ∈ D, h ^ 2 * x * (h ^ 2)⁻¹ = x⁻¹) {x₀ : X} (hx₀ : x₀ ∈ D) (hx₀2 : x₀ ^ 2 ≠ 1) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  set σ : MulAut D := D.normalizerMonoidHom ⟨h, hN⟩ with hσ
  have hσ2 : ∀ y : D, ((σ ^ 2) y : X) = (y : X)⁻¹ := by
    intro y
    have e : σ ^ 2 = D.normalizerMonoidHom ⟨h ^ 2, Subgroup.pow_mem _ hN 2⟩ := by
      rw [hσ, ← map_pow]
      rfl
    rw [e, normalizerMonoidHom_apply_coe]
    exact h2 y y.2
  refine ⟨σ, mem_autIn_iff.mpr ⟨h, hN, Subgroup.mem_top h, rfl⟩, ?_, ?_⟩
  · refine MulEquiv.ext fun y => Subtype.ext ?_
    have e : σ ^ 4 = σ ^ 2 * σ ^ 2 := by rw [← pow_add]
    rw [e, MulAut.mul_apply, hσ2, hσ2, inv_inv]
    rfl
  · intro h1
    have := hσ2 ⟨x₀, hx₀⟩
    rw [h1] at this
    change x₀ = x₀⁻¹ at this
    apply hx₀2
    calc x₀ ^ 2 = x₀ * x₀ := pow_two x₀
      _ = x₀⁻¹ * x₀ := by rw [← this]
      _ = 1 := inv_mul_cancel x₀

theorem not_three_dvd_card_ker {Y : Type*} [Group Y] [Finite Y] (π : Y →* X)
    (hker : ∀ z ∈ π.ker, z ^ 4 = 1) : ¬ 3 ∣ Nat.card π.ker := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h
  have h4 : (z : Y) ^ 4 = 1 := hker z z.2
  have h3 : (z : Y) ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 : (z : Y) = 1 := by
    calc (z : Y) = (z : Y) ^ 4 * ((z : Y) ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, h3, inv_one, one_mul]
  have : z = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hz
  norm_num at hz

theorem exists_autIn_pow_four_of_cover {Y : Type*} [Group Y] [Finite Y] (π : Y →* X)
    (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, z ^ 4 = 1)
    (hY : ∀ E : Subgroup Y, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E = 9 → ∃ g : Y, (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧
        ∀ x ∈ E, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹)
    {D : Subgroup X} (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop := not_three_dvd_card_ker π hker
  have hDp : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hDexp x x.2)⟩
  obtain ⟨E, hEmap, hEdis⟩ :=
    CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker π hπ hcop D hDp
  have hEmem : ∀ x ∈ E, π x ∈ D := fun x hx => hEmap ▸ ⟨x, hx, rfl⟩
  have hDE : ∀ x ∈ D, ∃ e ∈ E, π e = x := fun x hx => by
    rw [← hEmap] at hx
    exact hx
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hDcomm _ (hEmem a ha) _ (hEmem b hb)]
      group
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.disjoint_def.mp hEdis hc hk)
  have hEexp : ∀ a ∈ E, a ^ 3 = 1 := by
    intro a ha
    have hk : a ^ 3 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hDexp _ (hEmem a ha)
    exact Subgroup.disjoint_def.mp hEdis (E.pow_mem ha 3) hk
  have hEcard : Nat.card E = 9 := by
    let fπ : E →* D := (π.comp E.subtype).codRestrict D (fun x => hEmem x.1 x.2)
    have hfπsurj : Function.Surjective fπ := by
      intro e
      obtain ⟨x, hx, hxe⟩ := hDE e e.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
    have hfπinj : Function.Injective fπ := by
      intro x y hxy
      have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
      have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h3' : x.1⁻¹ * y.1 = 1 :=
        Subgroup.disjoint_def.mp hEdis (E.mul_mem (E.inv_mem x.2) y.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3')
    rw [← hD9]
    exact Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)
  obtain ⟨g, hgE, hg2⟩ := hY E hEcomm hEexp hEcard
  have hconj : ∀ x ∈ D, π g * x * (π g)⁻¹ ∈ D := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hDE x hx
    rw [← map_inv, ← map_mul, ← map_mul]
    exact hEmem _ (hgE e he)
  have hsq : ∀ x ∈ D, π g ^ 2 * x * (π g ^ 2)⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hDE x hx
    rw [← map_pow, ← map_inv, ← map_mul, ← map_mul, hg2 e he, map_inv]
  have hN := mem_normalizer_of_sq_inv hconj hsq
  have hfin : Finite D := Nat.finite_of_card_ne_zero (by rw [hD9]; norm_num)
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by rw [hD9]; norm_num)
  obtain ⟨x₀, hx₀1⟩ := exists_ne (1 : D)
  have hx₀2 : (x₀ : X) ^ 2 ≠ 1 := by
    intro h2
    apply hx₀1
    apply Subtype.ext
    have h3 := hDexp x₀ x₀.2
    calc (x₀ : X) = (x₀ : X) ^ 3 * ((x₀ : X) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  exact exists_autIn_of_sq_inv hN hsq x₀.2 hx₀2

end Automizer

theorem census424_of_cover {X : Type} [Group X] [Finite X] {Y : Type*} [Group Y] [Finite Y]
    (π : Y →* X) (hπ : Function.Surjective π) (hker : ∀ z ∈ π.ker, z ^ 4 = 1)
    (hY : ∀ E : Subgroup Y, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E = 9 → ∃ g : Y, (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧
        ∀ x ∈ E, g ^ 2 * x * (g ^ 2)⁻¹ = x⁻¹) :
    Census424 X := by
  intro D c d K h
  have hDe := h.maximal.prop
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact (Item424Res2.false_of_pow_four h
    (exists_autIn_pow_four_of_cover π hπ hker hY hDcomm hDe.2 h.card_eq)).elim

end Item424Res5

end CFSG.RankThree.PartTwo.Sec4
