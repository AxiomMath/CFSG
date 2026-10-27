module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin

section Orbit

variable {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω]

theorem index_stabilizer_eq_two_and_orbit {A : Type*} [Group A] [Finite A] [MulAction A Ω]
    (hA2 : IsPGroup 2 A) {ω ω' ω'' : Ω} (hne : ω ≠ ω')
    (hT : ∀ t : A, t • ω = ω ∨ t • ω = ω' ∨ t • ω = ω'')
    (ht0 : ∃ t : A, t • ω = ω') :
    (MulAction.stabilizer A ω).index = 2 ∧ ∀ t : A, t • ω = ω ∨ t • ω = ω' := by
  classical
  obtain ⟨t₀, ht₀ω⟩ := ht0
  have hsub : MulAction.orbit A ω ⊆ {ω, ω', ω''} := by
    rintro _ ⟨t, rfl⟩
    rcases hT t with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hpair : ({ω, ω'} : Set Ω) ⊆ MulAction.orbit A ω := by
    rintro x (rfl | rfl)
    · exact ⟨1, one_smul _ _⟩
    · exact ⟨t₀, ht₀ω⟩
  have hfinO : (MulAction.orbit A ω).Finite := Set.finite_range _
  have hle : (MulAction.orbit A ω).ncard ≤ 3 := by
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
    simp
  have hge : 2 ≤ (MulAction.orbit A ω).ncard := by
    have := Set.ncard_le_ncard hpair hfinO
    rwa [Set.ncard_pair hne] at this
  have hind : ∃ k : ℕ, (MulAction.stabilizer A ω).index = 2 ^ k := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hA2.index _
  rw [MulAction.index_stabilizer] at hind
  obtain ⟨k, hk⟩ := hind
  have hcard : (MulAction.orbit A ω).ncard = 2 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> omega
    · have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
  refine ⟨by rw [MulAction.index_stabilizer, hcard], fun t => ?_⟩
  have heq : MulAction.orbit A ω = {ω, ω'} := by
    symm
    refine Set.eq_of_subset_of_ncard_le hpair ?_ hfinO
    rw [hcard, Set.ncard_pair hne]
  have : t • ω ∈ MulAction.orbit A ω := ⟨t, rfl⟩
  rw [heq] at this
  exact this

end Orbit


section Index

variable {G : Type*} [Group G]

theorem relIndex_inf_eq_of_forall_mul {H₁ T H : Subgroup G} (hH₁ : H₁ ≤ H)
    (hmul : ∀ h ∈ H, ∃ a ∈ H₁, ∃ b ∈ T, h = a * b) :
    (T ⊓ H₁).relIndex H₁ = T.relIndex H := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' (fun x : ↥H₁ => (⟨x.1, hH₁ x.2⟩ : ↥H)) ?_) ⟨?_, ?_⟩)
  · intro x y hxy
    have h := QuotientGroup.leftRel_apply.mp hxy
    exact QuotientGroup.leftRel_apply.mpr (by
      refine Subgroup.mem_subgroupOf.mpr ?_
      exact (Subgroup.mem_subgroupOf.mp h).1)
  · intro x y
    refine Quotient.inductionOn₂' x y fun x y hxy => ?_
    have h := QuotientGroup.leftRel_apply.mp (Quotient.exact' hxy)
    refine Quotient.sound' (QuotientGroup.leftRel_apply.mpr ?_)
    refine Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp h), ?_⟩
    exact H₁.mul_mem (H₁.inv_mem x.2) y.2
  · intro q
    refine Quotient.inductionOn' q fun h => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := hmul h.1 h.2
    refine ⟨Quotient.mk'' ⟨a, ha⟩, ?_⟩
    refine Quotient.sound' (QuotientGroup.leftRel_apply.mpr ?_)
    refine Subgroup.mem_subgroupOf.mpr ?_
    show a⁻¹ * h.1 ∈ T
    rw [hab]
    simpa using hb

theorem not_two_dvd_relIndex_inf_of_forall_mul {H₁ H₂ T H : Subgroup G} (hH₁ : H₁ ≤ H)
    (hH₂ : H₂ ≤ H₁) (hTH₂ : T ⊓ H₁ ≤ H₂) (hmul : ∀ h ∈ H, ∃ a ∈ H₁, ∃ b ∈ T, h = a * b)
    (hodd : ¬ 2 ∣ T.relIndex H) : ¬ 2 ∣ (T ⊓ H₂).relIndex H₂ := by
  have h1 := relIndex_inf_eq_of_forall_mul hH₁ hmul
  have heq : T ⊓ H₂ = T ⊓ H₁ := le_antisymm (inf_le_inf_left T hH₂) (le_inf inf_le_left hTH₂)
  rw [heq]
  have h2 := Subgroup.relIndex_mul_relIndex (T ⊓ H₁) H₂ H₁ hTH₂ hH₂
  rw [h1] at h2
  intro hd
  exact hodd (h2 ▸ Dvd.dvd.mul_right hd _)

theorem not_two_dvd_relIndex_inf_normal {N T₀ H₂ : Subgroup G} (hNH₂ : N ≤ H₂) (hT₀ : T₀ ≤ H₂)
    (hN : ∀ t ∈ T₀, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hodd : ¬ 2 ∣ T₀.relIndex H₂) :
    ¬ 2 ∣ (T₀ ⊓ N).relIndex N := by
  have hnorm : T₀ ≤ Subgroup.normalizer (N : Set G) := fun t ht => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hN t ht x hx, fun hx => ?_⟩
    have := hN t⁻¹ (T₀.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hmul : ∀ h ∈ N ⊔ T₀, ∃ a ∈ N, ∃ b ∈ T₀, h = a * b := by
    intro h hh
    have hc := Subgroup.coe_mul_of_right_le_normalizer_left N T₀ hnorm
    have hh' : h ∈ ((N ⊔ T₀ : Subgroup G) : Set G) := hh
    rw [hc] at hh'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hh'
    exact ⟨a, ha, b, hb, rfl⟩
  have h1 := relIndex_inf_eq_of_forall_mul (H₁ := N) (T := T₀) (H := N ⊔ T₀) le_sup_left hmul
  rw [h1]
  have h2 := Subgroup.relIndex_mul_relIndex T₀ (N ⊔ T₀) H₂ le_sup_right (sup_le hNH₂ hT₀)
  intro hd
  exact hodd (h2 ▸ Dvd.dvd.mul_right hd _)

end Index

end CFSG.Quasithin
