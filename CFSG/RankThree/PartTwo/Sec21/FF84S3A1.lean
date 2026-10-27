module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09A8Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup

theorem isThreeCycle_c : (List.formPerm [0, 1, 2] : P8).IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

theorem cycleType_c : (List.formPerm [0, 1, 2] : P8).cycleType = {3} :=
  isThreeCycle_c.cycleType

theorem cycleType_m₁ : m₁.cycleType = {3, 3} := by
  have h1 : (List.formPerm [0, 1, 2] : P8).IsThreeCycle := isThreeCycle_c
  have h2 : (List.formPerm [3, 4, 5] : P8).IsThreeCycle :=
    card_support_eq_three_iff.mp (by decide +kernel)
  have hd : Equiv.Perm.Disjoint (List.formPerm [0, 1, 2] : P8) (List.formPerm [3, 4, 5]) :=
    fun z => by revert z; decide
  show (List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5] : P8).cycleType = {3, 3}
  rw [hd.cycleType_mul, h1.cycleType, h2.cycleType]
  rfl

theorem card_inf_alt_mul_two (g t : P8) (ht : t * g = g * t) (hto : Equiv.Perm.sign t = -1) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set P8) ⊓ A8s) * 2 =
      Nat.card ↥(Subgroup.centralizer ({g} : Set P8)) :=
  CFSG.LocalAnalysis.GLTheoremA.a8_card_alt_inf _ t (Subgroup.mem_centralizer_singleton_iff.2 ht) hto

theorem card_centralizer_eq_of_cycleType {g : P8} {s : Multiset ℕ} (h : g.cycleType = s) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set P8)) =
      Nat.factorial (Fintype.card (Fin 8) - s.sum) * s.prod * ∏ n ∈ s.toFinset, Nat.factorial (s.count n) := by
  rw [Equiv.Perm.nat_card_centralizer g, h]

theorem card_centralizer_cycle3 {g : P8} (h : g.cycleType = {3}) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set P8)) = 360 := by
  rw [card_centralizer_eq_of_cycleType h]
  decide

theorem card_centralizer_cycle33 {g : P8} (h : g.cycleType = {3, 3}) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set P8)) = 36 := by
  rw [card_centralizer_eq_of_cycleType h]
  decide

theorem card_centralizer_cycle2 {g : P8} (h : g.cycleType = {2}) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set P8)) = 1440 := by
  rw [card_centralizer_eq_of_cycleType h]
  decide

theorem cycleType_three_cases {x : P8} (h3 : orderOf x = 3) :
    x.cycleType = {3} ∨ x.cycleType = {3, 3} := by
  have hlcm : x.cycleType.lcm = 3 := by rw [Equiv.Perm.lcm_cycleType, h3]
  have hall : ∀ a ∈ x.cycleType, a = 3 := by
    intro a ha
    have h2 : 2 ≤ a := Equiv.Perm.two_le_of_mem_cycleType ha
    have hdvd : a ∣ x.cycleType.lcm := Multiset.dvd_lcm ha
    rw [hlcm] at hdvd
    have hle : a ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases a <;> omega
  obtain ⟨n, hn⟩ : ∃ n, x.cycleType = Multiset.replicate n 3 :=
    ⟨_, Multiset.eq_replicate_card.2 hall⟩
  have hsum := Equiv.Perm.sum_cycleType_le x
  rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  rw [hn] at hlcm
  have hn2 : n ≤ 2 := by omega
  interval_cases n
  · simp at hlcm
  · left; rw [hn]; rfl
  · right; rw [hn]; rfl

theorem exists_odd_commute {x : P8} (hx : x.cycleType = {3} ∨ x.cycleType = {3, 3}) :
    ∃ t : P8, Equiv.Perm.sign t = -1 ∧ t * x = x * t := by
  have hs : τ₀.IsSwap := ⟨6, 7, by decide, rfl⟩
  obtain ⟨y, hy, hycomm, hyc⟩ : ∃ y : P8, (y = List.formPerm [0, 1, 2] ∨ y = m₁) ∧
      τ₀ * y = y * τ₀ ∧ IsConj y x := by
    rcases hx with hx | hx
    · exact ⟨List.formPerm [0, 1, 2], Or.inl rfl, by decide,
        isConj_iff_cycleType_eq.2 (cycleType_c.trans hx.symm)⟩
    · exact ⟨m₁, Or.inr rfl, by decide, isConj_iff_cycleType_eq.2 (cycleType_m₁.trans hx.symm)⟩
  obtain ⟨σ, hσ⟩ := isConj_iff.1 hyc
  refine ⟨σ * τ₀ * σ⁻¹, ?_, ?_⟩
  · calc Equiv.Perm.sign (σ * τ₀ * σ⁻¹)
        = Equiv.Perm.sign σ * Equiv.Perm.sign τ₀ * (Equiv.Perm.sign σ)⁻¹ := by
          simp only [map_mul, map_inv]
      _ = Equiv.Perm.sign τ₀ := by
          rw [mul_comm (Equiv.Perm.sign σ), mul_assoc, mul_inv_cancel, mul_one]
      _ = -1 := hs.sign_eq
  · rw [← hσ]
    calc σ * τ₀ * σ⁻¹ * (σ * y * σ⁻¹)
        = σ * (τ₀ * y) * σ⁻¹ := by group
      _ = σ * (y * τ₀) * σ⁻¹ := by rw [hycomm]
      _ = σ * y * σ⁻¹ * (σ * τ₀ * σ⁻¹) := by group

theorem card_inf_of_cycleType3 {g : P8} (h : g.cycleType = {3}) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set P8) ⊓ A8s) = 180 := by
  obtain ⟨t, ht, htc⟩ := exists_odd_commute (Or.inl h)
  have h1 := card_inf_alt_mul_two g t htc ht
  have h2 := card_centralizer_cycle3 h
  omega

theorem card_inf_of_cycleType33 {g : P8} (h : g.cycleType = {3, 3}) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set P8) ⊓ A8s) = 18 := by
  obtain ⟨t, ht, htc⟩ := exists_odd_commute (Or.inr h)
  have h1 := card_inf_alt_mul_two g t htc ht
  have h2 := card_centralizer_cycle33 h
  omega

theorem A1_class (x : P8) (hx : x ∈ A8s) (h3 : orderOf x = 3) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set P8) ⊓ A8s) = 18 ↔ x.cycleType = {3, 3} := by
  rcases cycleType_three_cases h3 with h | h
  · have h180 := card_inf_of_cycleType3 h
    constructor
    · intro h18; omega
    · intro h'; rw [h] at h'; exact absurd h' (by decide)
  · exact ⟨fun _ => h, fun _ => card_inf_of_cycleType33 h⟩

theorem A11_tau_centralizes :
    τ₀ * m₁ = m₁ * τ₀ ∧ τ₀ * m₂ = m₂ * τ₀ ∧ τ₀ ∉ A8s ∧ τ₀ * τ₀ = 1 := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  intro h
  have h' : τ₀ ∈ alternatingGroup (Fin 8) := h
  have hs : (τ₀ : P8).IsSwap := ⟨6, 7, by decide, rfl⟩
  have h1 := Equiv.Perm.mem_alternatingGroup.1 h'
  rw [hs.sign_eq] at h1
  exact absurd h1 (by decide)

theorem sign_four_swaps {a b c d e f g h : Fin 8} (h1 : a ≠ b) (h2 : c ≠ d) (h3 : e ≠ f)
    (h4 : g ≠ h) :
    Equiv.Perm.sign (Equiv.swap a b * Equiv.swap c d * Equiv.swap e f * Equiv.swap g h) = 1 := by
  simp only [map_mul, Equiv.Perm.sign_swap h1, Equiv.Perm.sign_swap h2,
    Equiv.Perm.sign_swap h3, Equiv.Perm.sign_swap h4]
  decide

theorem mem_nor_closure_of {S : Set P8} {g : P8} (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (h2 : ∀ s ∈ S, g⁻¹ * s * g⁻¹⁻¹ ∈ S) : g ∈ Nor (Subgroup.closure S) := by
  have c1 : ∀ x ∈ Subgroup.closure S, g * x * g⁻¹ ∈ Subgroup.closure S := by
    have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro s hs
      exact Subgroup.subset_closure (h1 s hs)
    intro x hx
    exact hle hx
  have c2 : ∀ x ∈ Subgroup.closure S, g⁻¹ * x * g⁻¹⁻¹ ∈ Subgroup.closure S := by
    have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro s hs
      exact Subgroup.subset_closure (h2 s hs)
    intro x hx
    exact hle hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact c1 x hx
  · intro hx
    have := c2 _ hx
    simpa [mul_assoc] using this

theorem A9_transvections :
    ∃ s₁ s₂ : P8, s₁ ∈ A8s ∧ s₂ ∈ A8s ∧ s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧
      s₁ * m₁ * s₁⁻¹ = m₁⁻¹ ∧ s₁ * m₂ * s₁⁻¹ = m₂ ∧ s₂ * m₂ * s₂⁻¹ = m₂⁻¹ ∧ s₂ * m₁ * s₂⁻¹ = m₁ ∧
      s₁ ∈ Nor U₁ ∧ s₂ ∈ Nor U₁ := by
  refine ⟨Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 2 4 * Equiv.swap 6 7,
    Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5 * Equiv.swap 6 7, ?_, ?_, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact Equiv.Perm.mem_alternatingGroup.2 (sign_four_swaps (by decide) (by decide) (by decide)
      (by decide))
  · exact Equiv.Perm.mem_alternatingGroup.2 (sign_four_swaps (by decide) (by decide) (by decide)
      (by decide))
  · exact mem_nor_closure_of
      (S := {(Equiv.swap 0 1) * (Equiv.swap 2 6), (Equiv.swap 0 2) * (Equiv.swap 1 6),
        (Equiv.swap 3 4) * (Equiv.swap 5 7), (Equiv.swap 3 5) * (Equiv.swap 4 7)})
      (by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
        rcases hs with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
        rcases hs with rfl | rfl | rfl | rfl <;> decide)
  · exact mem_nor_closure_of
      (S := {(Equiv.swap 0 1) * (Equiv.swap 2 6), (Equiv.swap 0 2) * (Equiv.swap 1 6),
        (Equiv.swap 3 4) * (Equiv.swap 5 7), (Equiv.swap 3 5) * (Equiv.swap 4 7)})
      (by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
        rcases hs with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
        rcases hs with rfl | rfl | rfl | rfl <;> decide)

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
