module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.G2SL3

public section

namespace CFSG.Quasithin.H13.L14333

open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

variable {F : Type*} [Field F] [Finite F]

theorem index_ne_two_of_perfect {X : Type*} [Group X] (hX : Group.IsPerfect X) (S : Subgroup X) :
    S.index ≠ 2 := by
  intro h2
  have hle : commutator X ≤ S := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have key : ∀ u w : X, u * w ∈ S ↔ (u ∈ S ↔ w ∈ S) := fun u w =>
      Subgroup.mul_mem_iff_of_index_two h2
    rw [commutatorElement_def, key, key, key, inv_mem_iff (x := a), inv_mem_iff (x := b)]
    tauto
  rw [hX.commutator_eq_top, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at h2
  omega

theorem cocycle_eq_coboundary (hF : Nat.card F = 2) (δ : SL(3, F) → (Fin 3 → F))
    (hδ : ∀ g h, δ (g * h) = δ g + g • δ h) (hQ : ∀ q ∈ Qv (vE F 0), δ q = 0)
    {y : SL(3, F)} (hy : orderOf y = 3) (hyδ : δ y = 0) :
    ∃ p : Fin 3 → F, (∀ q ∈ Qv (vE F 0), q • p = p) ∧ ∀ g, δ g = p - g • p := by
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, one_smul] at h
    have h' : δ 1 + 0 = δ 1 + δ 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hδinv : ∀ g, δ g⁻¹ = -(g⁻¹ • δ g) := by
    intro g
    have h := hδ g⁻¹ g
    rw [inv_mul_cancel, hδ1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  let S₀ : Subgroup SL(3, F) :=
    { carrier := {g | δ g = 0}
      one_mem' := hδ1
      mul_mem' := fun {g h} hg hh => by
        show δ (g * h) = 0
        rw [hδ, show δ g = 0 from hg, show δ h = 0 from hh, smul_zero, add_zero]
      inv_mem' := fun {g} hg => by
        show δ g⁻¹ = 0
        rw [hδinv, show δ g = 0 from hg, smul_zero, neg_zero] }
  have hmem : ∀ g, g ∈ S₀ ↔ δ g = 0 := fun g => Iff.rfl
  have hcoset : ∀ g h, δ (h⁻¹ * g) = h⁻¹ • (δ g - δ h) := by
    intro g h
    rw [hδ, hδinv, smul_sub]
    abel
  have hsep : ∀ g h, δ g = δ h ↔ h⁻¹ * g ∈ S₀ := by
    intro g h
    rw [hmem, hcoset]
    constructor
    · intro e; rw [e, sub_self, smul_zero]
    · intro e
      have : δ g - δ h = 0 := by
        have := congrArg (h • ·) e
        simpa [smul_smul] using this
      exact sub_eq_zero.mp this
  let f : SL(3, F) ⧸ S₀ → (Fin 3 → F) := Quotient.lift δ (fun a b hab => by
    have hab' : a⁻¹ * b ∈ S₀ := QuotientGroup.leftRel_apply.mp hab
    exact ((hsep b a).mpr hab').symm)
  have hf : Function.Injective f := by
    intro u w huw
    induction u using QuotientGroup.induction_on with | H a =>
    induction w using QuotientGroup.induction_on with | H b =>
    have h1 : δ a = δ b := huw
    exact QuotientGroup.eq.mpr (by
      have := (hsep b a).mp h1.symm
      exact this)
  have hcard8 : Nat.card (Fin 3 → F) = 8 := by
    rw [Nat.card_fun, hF]
    norm_num
  have hidx : S₀.index ≤ 8 := by
    rw [Subgroup.index, ← hcard8]
    exact Nat.card_le_card_of_injective f hf
  have hcardSL : Nat.card SL(3, F) = 168 := by
    rw [card_SL3, hF]
    norm_num
  have h12 : 12 ∣ Nat.card S₀ := by
    have h4 : 4 ∣ Nat.card S₀ := by
      have : Nat.card (Qv (vE F 0)) = 4 := by rw [card_Qv, hF]; norm_num
      rw [← this]
      exact Subgroup.card_dvd_of_le fun q hq => hQ q hq
    have h3 : 3 ∣ Nat.card S₀ := by
      have := Subgroup.orderOf_dvd_natCard S₀ (x := y) hyδ
      rwa [hy] at this
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4 h3
  have hmul := Subgroup.card_mul_index S₀
  rw [hcardSL] at hmul
  obtain ⟨k, hk⟩ := h12
  have hkn : k * S₀.index = 14 := by
    rw [hk] at hmul
    have : 12 * (k * S₀.index) = 12 * 14 := by rw [← mul_assoc, hmul]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hpos : 0 < S₀.index := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hkn; omega)
  have hne2 : S₀.index ≠ 2 :=
    index_ne_two_of_perfect (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect
      le_rfl) S₀
  have hcases : S₀.index = 1 ∨ S₀.index = 7 := by
    have hdvd : S₀.index ∣ 14 := ⟨k, by rw [← hkn, mul_comm]⟩
    interval_cases h : S₀.index <;> simp_all
  rcases hcases with h1 | h7
  · refine ⟨0, fun q _ => smul_zero q, fun g => ?_⟩
    have hg : g ∈ S₀ := by rw [Subgroup.index_eq_one] at h1; rw [h1]; trivial
    rw [smul_zero, sub_zero]
    exact hg
  ·
    have hrange : Set.range δ = Set.range f := by
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨(g : SL(3, F) ⧸ S₀), rfl⟩
      · rintro ⟨u, rfl⟩
        induction u using QuotientGroup.induction_on with | H a =>
        exact ⟨a, rfl⟩
    have hcard7 : (Set.range δ).ncard = 7 := by
      rw [hrange, Set.ncard_range_of_injective hf, ← h7, Subgroup.index]
    have hcompl : (Set.range δ)ᶜ.ncard = 1 := by
      have := Set.ncard_add_ncard_compl (Set.range δ)
      rw [hcard7, hcard8] at this
      omega
    obtain ⟨p, hp⟩ := Set.ncard_eq_one.mp hcompl
    have hpn : p ∉ Set.range δ := by
      have : p ∈ (Set.range δ)ᶜ := by rw [hp]; rfl
      exact this
    have huniq : ∀ v, v ∉ Set.range δ → v = p := fun v hv => by
      have : v ∈ (Set.range δ)ᶜ := hv
      rw [hp] at this
      exact this
    have hfix : ∀ g : SL(3, F), g • p + δ g = p := by
      intro g
      apply huniq
      rintro ⟨h, hh⟩
      apply hpn
      refine ⟨g⁻¹ * h, ?_⟩
      rw [hδ, hδinv, hh, smul_add, smul_smul, inv_mul_cancel, one_smul]
      abel
    refine ⟨p, fun q hq => ?_, fun g => ?_⟩
    · have := hfix q
      rwa [hQ q hq, add_zero] at this
    · have := hfix g
      rw [eq_sub_iff_add_eq, add_comm]
      exact this

omit [Finite F] in
theorem eq_smul_e0_of_fix {p : Fin 3 → F} (hp : ∀ q ∈ Qv (vE F 0), q • p = p) :
    ∃ c : F, p = c • vE F 0 := by
  have h1 := hp (tq 1 0) (tq_mem_Qv 1 0)
  have h2 := hp (tq 0 1) (tq_mem_Qv 0 1)
  rw [show tq (1 : F) 0 • p = _ from tq_smul 1 0 p] at h1
  rw [show tq (0 : F) 1 • p = _ from tq_smul 0 1 p] at h2
  have e1 : p 1 = 0 := by
    have := congrFun h1 0
    simp at this
    exact this
  have e2 : p 2 = 0 := by
    have := congrFun h2 0
    simp at this
    exact this
  refine ⟨p 0, ?_⟩
  ext i
  fin_cases i <;> simp [vE, e1, e2]

end CFSG.Quasithin.H13.L14333
