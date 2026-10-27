module

public import CFSG.Timmesfeld.ARS.Defs

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Timmesfeld.ARS

variable {K : Type*} [Group K]

@[expose] def rcsSub (Γ : Subgroup K) (R : Set (Subgroup K)) : Set (Subgroup ↥Γ) :=
  (fun A : Subgroup K => A.subgroupOf Γ) '' R

theorem rcs_subgroupOf_injective {Γ A B : Subgroup K} (hA : A ≤ Γ) (hB : B ≤ Γ)
    (h : A.subgroupOf Γ = B.subgroupOf Γ) : A = B := by
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hA, inf_of_le_left hB] at h
  exact h

theorem rcs_conjSub_subgroupOf {Γ A : Subgroup K} (hA : A ≤ Γ) (g : ↥Γ) :
    conjSub (A.subgroupOf Γ) g = (conjSub A (g : K)).subgroupOf Γ := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a : K), ha, by simp⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨⟨a, hA ha⟩, ha, Subtype.ext ?_⟩
    simpa using hax

theorem rcs_conjSub_le {Γ A : Subgroup K} (hA : A ≤ Γ) (g : ↥Γ) : conjSub A (g : K) ≤ Γ := by
  rintro _ ⟨a, ha, rfl⟩
  exact Γ.mul_mem (Γ.mul_mem g.2 (hA ha)) (Γ.inv_mem g.2)

theorem rcs_commuting_subgroupOf {Γ A B : Subgroup K} (hA : A ≤ Γ) (hB : B ≤ Γ) :
    Commuting (A.subgroupOf Γ) (B.subgroupOf Γ) ↔ Commuting A B := by
  constructor
  · intro h a ha b hb
    exact congrArg Subtype.val (h ⟨a, hA ha⟩ ha ⟨b, hB hb⟩ hb)
  · intro h a ha b hb
    exact Subtype.ext (h a ha b hb)

theorem rcs_opposite_subgroupOf {Γ A B : Subgroup K} (hA : A ≤ Γ) (hB : B ≤ Γ)
    (h : Opposite A B) : Opposite (A.subgroupOf Γ) (B.subgroupOf Γ) := by
  obtain ⟨hne, h1, h2⟩ := h
  refine ⟨fun e => hne (rcs_subgroupOf_injective hA hB e), ?_, ?_⟩
  · intro a ha ha1
    obtain ⟨b, hb, hb1, e⟩ := h1 (a : K) ha (fun h => ha1 (Subtype.ext h))
    refine ⟨⟨b, hB hb⟩, hb, fun h => hb1 (congrArg Subtype.val h), ?_⟩
    rw [rcs_conjSub_subgroupOf hA, rcs_conjSub_subgroupOf hB]
    exact congrArg (fun S => S.subgroupOf Γ) e
  · intro b hb hb1
    obtain ⟨a, ha, ha1, e⟩ := h2 (b : K) hb (fun h => hb1 (Subtype.ext h))
    refine ⟨⟨a, hA ha⟩, ha, fun h => ha1 (congrArg Subtype.val h), ?_⟩
    rw [rcs_conjSub_subgroupOf hA, rcs_conjSub_subgroupOf hB]
    exact congrArg (fun S => S.subgroupOf Γ) e

theorem rcs_commutator_le {Γ A B : Subgroup K} (hA : A ≤ Γ) (hB : B ≤ Γ) : ⁅A, B⁆ ≤ Γ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (hA ha) (hB hb)) (Γ.inv_mem (hA ha)))
    (Γ.inv_mem (hB hb))

theorem rcs_commutator_subgroupOf {Γ A B : Subgroup K} (hA : A ≤ Γ) (hB : B ≤ Γ) :
    ⁅A.subgroupOf Γ, B.subgroupOf Γ⁆ = ⁅A, B⁆.subgroupOf Γ := by
  apply Subgroup.map_injective Γ.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le (rcs_commutator_le hA hB)]

theorem rcs_special_subgroupOf {Γ : Subgroup K} {R₀ : Set (Subgroup K)} {A B : Subgroup K}
    (hA : A ≤ Γ) (hB : B ≤ Γ) (hAB : ⁅A, B⁆ ∈ R₀) (hcA : Commuting ⁅A, B⁆ A)
    (hcB : Commuting ⁅A, B⁆ B) :
    Special (rcsSub Γ R₀) (A.subgroupOf Γ) (B.subgroupOf Γ) := by
  have hle := rcs_commutator_le hA hB
  rw [Special, rcs_commutator_subgroupOf hA hB]
  exact ⟨⟨_, hAB, rfl⟩, (rcs_commuting_subgroupOf hle hA).mpr hcA,
    (rcs_commuting_subgroupOf hle hB).mpr hcB⟩

theorem rcs_hyp_of_subgroup [Finite K] {Γ A₀ : Subgroup K} {R₀ 𝒳 : Set (Subgroup K)}
    (hA₀ : A₀ ≤ Γ) (hne : A₀ ≠ ⊥) (hexp : ∀ a ∈ A₀, a * a = 1)
    (hR₀ : R₀ = Set.range (fun g : ↥Γ => conjSub A₀ (g : K)))
    (hdich : ∀ A ∈ R₀, ∀ B ∈ R₀, A ≠ B → Commuting A B ∨ Opposite A B ∨ Special 𝒳 A B)
    (hclos : ∀ A ∈ R₀, ∀ B ∈ R₀, Special 𝒳 A B → ⁅A, B⁆ ∈ R₀)
    (hgen : ⨆ A ∈ R₀, A = Γ) (hnondeg : ∃ A ∈ R₀, ∃ B ∈ R₀, Special 𝒳 A B)
    (hcenter : Subgroup.center ↥Γ = ⊥)
    (htwoCore : ∀ N : Subgroup ↥Γ, N.Normal → IsPGroup 2 N → N = ⊥) :
    Hyp ↥Γ (rcsSub Γ R₀) := by
  have hle : ∀ A ∈ R₀, A ≤ Γ := by
    rw [hR₀]
    rintro _ ⟨g, rfl⟩
    exact rcs_conjSub_le hA₀ g
  have hne' : ∀ A ∈ R₀, A ≠ ⊥ := by
    rw [hR₀]
    rintro _ ⟨g, rfl⟩ h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective A₀ (MulAut.conj (g : K)).injective).mp h)
  have hexp' : ∀ A ∈ R₀, ∀ a ∈ A, a * a = 1 := by
    rw [hR₀]
    rintro _ ⟨g, rfl⟩ _ ⟨a, ha, rfl⟩
    have := hexp a ha
    calc (MulAut.conj (g : K)).toMonoidHom a * (MulAut.conj (g : K)).toMonoidHom a
        = (MulAut.conj (g : K)).toMonoidHom (a * a) := (map_mul _ _ _).symm
      _ = 1 := by rw [this, map_one]
  have hspecial : ∀ A ∈ R₀, ∀ B ∈ R₀, Special 𝒳 A B →
      Special (rcsSub Γ R₀) (A.subgroupOf Γ) (B.subgroupOf Γ) := fun A hA B hB hS =>
    rcs_special_subgroupOf (hle A hA) (hle B hB) (hclos A hA B hB hS) hS.2.1 hS.2.2
  refine ⟨inferInstance, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hcenter, htwoCore⟩
  ·
    refine ⟨A₀.subgroupOf Γ, ?_⟩
    ext S
    constructor
    · rintro ⟨A, hA, rfl⟩
      rw [hR₀] at hA
      obtain ⟨g, rfl⟩ := hA
      exact ⟨g, (rcs_conjSub_subgroupOf hA₀ g)⟩
    · rintro ⟨g, rfl⟩
      exact ⟨conjSub A₀ (g : K), by rw [hR₀]; exact ⟨g, rfl⟩, (rcs_conjSub_subgroupOf hA₀ g).symm⟩
  ·
    rintro _ ⟨A, hA, rfl⟩ h
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact hne' A hA (le_bot_iff.mp (by simpa [inf_of_le_left (hle A hA)] using h.le_bot))
  ·
    rintro _ ⟨A, hA, rfl⟩ a ha
    exact Subtype.ext (hexp' A hA a ha)
  ·
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
    have hAB' : A ≠ B := fun e => hAB (e ▸ rfl)
    rcases hdich A hA B hB hAB' with h | h | h
    · exact Or.inl ((rcs_commuting_subgroupOf (hle A hA) (hle B hB)).mpr h)
    · exact Or.inr (Or.inl (rcs_opposite_subgroupOf (hle A hA) (hle B hB) h))
    · exact Or.inr (Or.inr (hspecial A hA B hB h))
  ·
    apply Subgroup.map_injective Γ.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun S => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hS => ?_
      obtain ⟨A, hA, rfl⟩ := hS
      rw [Subgroup.map_subgroupOf_eq_of_le (hle A hA)]
      exact hle A hA
    · calc Γ = ⨆ A ∈ R₀, A := hgen.symm
        _ ≤ _ := by
          refine iSup₂_le fun A hA => ?_
          refine le_iSup_of_le (A.subgroupOf Γ) ?_
          rw [Subgroup.map_iSup]
          refine le_iSup_of_le (show A.subgroupOf Γ ∈ rcsSub Γ R₀ from ⟨A, hA, rfl⟩) ?_
          rw [Subgroup.map_subgroupOf_eq_of_le (hle A hA)]
  ·
    obtain ⟨A, hA, B, hB, hS⟩ := hnondeg
    exact ⟨A.subgroupOf Γ, ⟨A, hA, rfl⟩, B.subgroupOf Γ, ⟨B, hB, rfl⟩, hspecial A hA B hB hS⟩

end CFSG.RankThree.PartOne.D4RC
