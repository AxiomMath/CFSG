module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.RankThree.PartOne.Lifting36

open CFSG
open scoped commutatorElement

variable {D : Type*} [Group D]

theorem commutator_mul_central {f : D} (hf : f ∈ Subgroup.center D) (u v : D) :
    ⁅f * u, v⁆ = ⁅u, v⁆ := by
  have h1 : ∀ w : D, f * w = w * f := fun w => (Subgroup.mem_center_iff.mp hf w).symm
  simp only [commutatorElement_def]
  calc f * u * v * (f * u)⁻¹ * v⁻¹ = f * (u * v * u⁻¹) * f⁻¹ * v⁻¹ := by group
    _ = (u * v * u⁻¹) * f * f⁻¹ * v⁻¹ := by rw [h1 (u * v * u⁻¹)]
    _ = u * v * u⁻¹ * v⁻¹ := by group

theorem commutator_mul_central_right {g : D} (hg : g ∈ Subgroup.center D) (u v : D) :
    ⁅u, g * v⁆ = ⁅u, v⁆ := by
  rw [← commutatorElement_inv, commutator_mul_central hg, commutatorElement_inv]

theorem commutator_inv_left_of_central {u v : D} (h : ⁅u, v⁆ ∈ Subgroup.center D) :
    ⁅u⁻¹, v⁆ = ⁅u, v⁆⁻¹ := by
  have hz : ⁅v, u⁆ ∈ Subgroup.center D := by
    rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ h
  have h1 := Subgroup.mem_center_iff.mp hz u⁻¹
  rw [commutatorElement_inv_left, commutatorElement_inv]
  calc u⁻¹ * ⁅v, u⁆ * u = ⁅v, u⁆ * u⁻¹ * u := by rw [h1]
    _ = ⁅v, u⁆ := by group

theorem commutator_inv_right_of_central {u v : D} (h : ⁅u, v⁆ ∈ Subgroup.center D) :
    ⁅u, v⁻¹⁆ = ⁅u, v⁆⁻¹ := by
  have hz : ⁅v, u⁆ ∈ Subgroup.center D := by
    rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ h
  rw [← commutatorElement_inv, commutator_inv_left_of_central hz, inv_inv, commutatorElement_inv]

theorem commutator_eq_one_of_closure {T : Set D} (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {u v : D} (hu : u ∈ Subgroup.closure T) (hv : v ∈ Subgroup.closure T) : ⁅u, v⁆ = 1 := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer T := by
    rw [Subgroup.closure_le]
    intro a ha b hb
    exact (hT b hb a ha)
  have h2 : T ⊆ Subgroup.centralizer ({u} : Set D) := by
    intro a ha
    show a ∈ Subgroup.centralizer ({u} : Set D)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (h1 hu) a ha
  have h3 : Subgroup.closure T ≤ Subgroup.centralizer ({u} : Set D) :=
    (Subgroup.closure_le _).mpr h2
  have := Subgroup.mem_centralizer_singleton_iff.mp (h3 hv)
  exact commutatorElement_eq_one_iff_mul_comm.mpr this.symm


theorem frattini_le_center_of_class_two {q : ℕ} [Fact q.Prime] [Finite D] [Fact (IsPGroup q D)]
    (hexp : ∀ x : D, x ^ q = 1) (hcl : commutator D ≤ Subgroup.center D) :
    frattini D ≤ Subgroup.center D := by
  rw [frattini_eq_closure_commutator_union_powers (p := q), Subgroup.closure_le]
  rintro _ (h | ⟨y, rfl⟩)
  · exact hcl h
  · show y ^ q ∈ Subgroup.center D
    rw [hexp y]
    exact Subgroup.one_mem _

theorem commutator_eq_one_of_signs {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) [Finite D]
    [Fact (IsPGroup q D)] (hexp : ∀ x : D, x ^ q = 1) (hcl : commutator D ≤ Subgroup.center D)
    {S : Type*} (σ : S → MulAut D) (hfixc : ∀ (s : S) (x y : D), σ s ⁅x, y⁆ = ⁅x, y⁆) {ι : Type*}
    (x : ι → D) (ε : ι → S → ℤˣ)
    (hact : ∀ i s, σ s (x i) * (x i ^ (ε i s : ℤ))⁻¹ ∈ frattini D)
    (hdist : ∀ i j, i ≠ j → ∃ s, ε i s ≠ ε j s)
    (hgen : ∀ d : D, ∃ u ∈ Subgroup.closure (Set.range x), u⁻¹ * d ∈ frattini D) :
    ∀ a b : D, ⁅a, b⁆ = 1 := by
  have hΦ : frattini D ≤ Subgroup.center D := frattini_le_center_of_class_two hexp hcl
  have hc : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D := fun a b => hcl (by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  have hq2' : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two (Fact.out : q.Prime)).mpr
    (Ne.symm hq2)
  have hpair : ∀ i j, i ≠ j → x i * x j = x j * x i := by
    intro i j hij
    obtain ⟨s, hs⟩ := hdist i j hij
    set a := x i
    set b := x j
    have hfa := hΦ (hact i s)
    have hfb := hΦ (hact j s)
    have hsa : σ s a = (σ s a * (a ^ (ε i s : ℤ))⁻¹) * a ^ (ε i s : ℤ) := by group
    have hsb : σ s b = (σ s b * (b ^ (ε j s : ℤ))⁻¹) * b ^ (ε j s : ℤ) := by group
    have h1 : ⁅σ s a, σ s b⁆ = ⁅a, b⁆ :=
      (map_commutatorElement (σ s).toMonoidHom a b).symm.trans (hfixc s a b)
    have h2 : ⁅σ s a, σ s b⁆ = ⁅a ^ (ε i s : ℤ), b ^ (ε j s : ℤ)⁆ := by
      rw [hsa, hsb, commutator_mul_central hfa, commutator_mul_central_right hfb]
    have h3 : ⁅a ^ (ε i s : ℤ), b ^ (ε j s : ℤ)⁆ = ⁅a, b⁆⁻¹ := by
      rcases Int.units_eq_one_or (ε i s) with hi | hi <;>
        rcases Int.units_eq_one_or (ε j s) with hj | hj
      · exact absurd (hi.trans hj.symm) hs
      · rw [hi, hj]
        simp only [Units.val_one, zpow_one, Units.val_neg, zpow_neg]
        exact commutator_inv_right_of_central (hc a b)
      · rw [hi, hj]
        simp only [Units.val_one, zpow_one, Units.val_neg, zpow_neg]
        exact commutator_inv_left_of_central (hc a b)
      · exact absurd (hi.trans hj.symm) hs
    have h4 : ⁅a, b⁆ = ⁅a, b⁆⁻¹ := h1.symm.trans (h2.trans h3)
    have h5 : ⁅a, b⁆ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h4]
      exact inv_mul_cancel _
    have h6 : ⁅a, b⁆ ^ q = 1 := hexp _
    have h7 : orderOf ⁅a, b⁆ = 1 := Nat.eq_one_of_dvd_coprimes hq2'
      (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one h6)
    exact commutatorElement_eq_one_iff_mul_comm.mp (orderOf_eq_one_iff.mp h7)
  have hT : ∀ a ∈ Set.range x, ∀ b ∈ Set.range x, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    by_cases hij : i = j
    · rw [hij]
    · exact hpair i j hij
  intro a b
  obtain ⟨u, hu, hfa⟩ := hgen a
  obtain ⟨v, hv, hfb⟩ := hgen b
  have hau : a = (u⁻¹ * a) * u := by
    have := Subgroup.mem_center_iff.mp (hΦ hfa) u
    calc a = u * (u⁻¹ * a) := by group
      _ = (u⁻¹ * a) * u := this
  have hbv : b = (v⁻¹ * b) * v := by
    have := Subgroup.mem_center_iff.mp (hΦ hfb) v
    calc b = v * (v⁻¹ * b) := by group
      _ = (v⁻¹ * b) * v := this
  rw [hau, hbv, commutator_mul_central (hΦ hfa), commutator_mul_central_right (hΦ hfb)]
  exact commutator_eq_one_of_closure hT hu hv

end CFSG.RankThree.PartOne.Lifting36
