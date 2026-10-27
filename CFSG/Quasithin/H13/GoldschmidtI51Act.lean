module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.I51

section Three

variable {S X : Type*} [Group S] [MulAction S X]

theorem action_three_aux (x0 a b : X) (hfix : ∀ s : S, s • x0 = x0) (hx0a : x0 ≠ a)
    (hx0b : x0 ≠ b) (hab : a ≠ b) (hall : ∀ x : X, x = x0 ∨ x = a ∨ x = b) (s : S) :
    (s • a = a ∧ s • b = b) ∨ (s • a = b ∧ s • b = a) := by
  have hinj : ∀ x y : X, s • x = s • y → x = y := fun x y h => MulAction.injective s h
  have ha : s • a ≠ x0 := fun h => hx0a (hinj _ _ (h.trans (hfix s).symm)).symm
  have hb : s • b ≠ x0 := fun h => hx0b (hinj _ _ (h.trans (hfix s).symm)).symm
  rcases hall (s • a) with h | h | h
  · exact absurd h ha
  · left
    refine ⟨h, ?_⟩
    rcases hall (s • b) with h' | h' | h'
    · exact absurd h' hb
    · exact absurd (hinj _ _ (h.trans h'.symm)) hab
    · exact h'
  · right
    refine ⟨h, ?_⟩
    rcases hall (s • b) with h' | h' | h'
    · exact absurd h' hb
    · exact h'
    · exact absurd (hinj _ _ (h.trans h'.symm)) hab

theorem action_three (x0 a b : X) (hfix : ∀ s : S, s • x0 = x0) (hx0a : x0 ≠ a)
    (hx0b : x0 ≠ b) (hab : a ≠ b) (hall : ∀ x : X, x = x0 ∨ x = a ∨ x = b) (s₁ s₂ : S) :
    (∀ x : X, s₁ • x = x) ∨ (∀ x : X, s₂ • x = x) ∨ (∀ x : X, (s₁ * s₂⁻¹) • x = x) := by
  have key : ∀ s : S, s • a = a → ∀ x : X, s • x = x := fun s hs x => by
    rcases action_three_aux x0 a b hfix hx0a hx0b hab hall s with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hall x with rfl | rfl | rfl
      · exact hfix s
      · exact h1
      · exact h2
    · exact absurd (hs.symm.trans h1) hab
  by_cases h1 : s₁ • a = a
  · exact Or.inl (key s₁ h1)
  by_cases h2 : s₂ • a = a
  · exact Or.inr (Or.inl (key s₂ h2))
  right; right
  apply key
  rcases action_three_aux x0 a b hfix hx0a hx0b hab hall s₁ with ⟨h, -⟩ | ⟨h1', h1''⟩
  · exact absurd h h1
  rcases action_three_aux x0 a b hfix hx0a hx0b hab hall s₂ with ⟨h, -⟩ | ⟨h2', h2''⟩
  · exact absurd h h2
  rw [mul_smul]
  have : s₂⁻¹ • a = b := by
    rw [inv_smul_eq_iff]; exact h2''.symm
  rw [this]
  exact h1''

end Three

section Core

variable {G : Type*} [Group G] [Finite G]

theorem exists_two_others {X : Type*} [Finite X] (hX : Nat.card X = 3) (x0 : X) :
    ∃ a b : X, x0 ≠ a ∧ x0 ≠ b ∧ a ≠ b ∧ ∀ w : X, w = x0 ∨ w = a ∨ w = b := by
  classical
  have := Fintype.ofFinite X
  have h3 : (Finset.univ : Finset X).card = 3 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hX]
  obtain ⟨x, y, z, hxy, hxz, hyz, hu⟩ := Finset.card_eq_three.1 h3
  have hall : ∀ w : X, w = x ∨ w = y ∨ w = z := fun w => by
    have : w ∈ (Finset.univ : Finset X) := Finset.mem_univ w
    rw [hu] at this
    simpa using this
  rcases hall x0 with rfl | rfl | rfl
  · refine ⟨y, z, hxy, hxz, hyz, fun w => ?_⟩
    rcases hall w with h | h | h <;> simp [h]
  · refine ⟨x, z, hxy.symm, hyz, hxz, fun w => ?_⟩
    rcases hall w with h | h | h <;> simp [h]
  · refine ⟨x, y, hxz.symm, hyz.symm, hxy, fun w => ?_⟩
    rcases hall w with h | h | h <;> simp [h]

theorem core_cases_of_relIndex_three {H P S : Subgroup G} (hPH : P ≤ H) (hSP : S ≤ P)
    (h3 : P.relIndex H = 3) :
    ∀ s₁ ∈ S, ∀ s₂ ∈ S, (∀ h ∈ H, h⁻¹ * s₁ * h ∈ P) ∨ (∀ h ∈ H, h⁻¹ * s₂ * h ∈ P) ∨
      (∀ h ∈ H, h⁻¹ * (s₁ * s₂⁻¹) * h ∈ P) := by
  intro s₁ hs₁ s₂ hs₂
  have hSH : S ≤ H := hSP.trans hPH
  have hX : Nat.card (↥H ⧸ P.subgroupOf H) = 3 := by
    rw [← Subgroup.index_eq_card]; exact h3
  obtain ⟨a, b, hx0a, hx0b, hab, hall⟩ := exists_two_others hX (((1 : ↥H)) : ↥H ⧸ P.subgroupOf H)
  have hsm : ∀ (t g : ↥H),
      (t • (g : ↥H ⧸ P.subgroupOf H) : ↥H ⧸ P.subgroupOf H) =
        ((t * g : ↥H) : ↥H ⧸ P.subgroupOf H) := fun t g => rfl
  have hfix : ∀ s : ↥(S.subgroupOf H),
      s • (((1 : ↥H)) : ↥H ⧸ P.subgroupOf H) = (((1 : ↥H)) : ↥H ⧸ P.subgroupOf H) := by
    intro s
    rw [Subgroup.smul_def, hsm, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
    exact Subgroup.mem_subgroupOf.2 (hSP (Subgroup.mem_subgroupOf.1 s.2))
  have key := fun (t₁ t₂ : ↥(S.subgroupOf H)) =>
    action_three (S := ↥(S.subgroupOf H)) (((1 : ↥H)) : ↥H ⧸ P.subgroupOf H) a b hfix hx0a hx0b
      hab hall t₁ t₂
  let t₁ : ↥(S.subgroupOf H) := ⟨⟨s₁, hSH hs₁⟩, Subgroup.mem_subgroupOf.2 hs₁⟩
  let t₂ : ↥(S.subgroupOf H) := ⟨⟨s₂, hSH hs₂⟩, Subgroup.mem_subgroupOf.2 hs₂⟩
  have conv : ∀ (u : ↥(S.subgroupOf H)), (∀ x : ↥H ⧸ P.subgroupOf H, u • x = x) →
      ∀ h ∈ H, h⁻¹ * ((u : ↥H) : G) * h ∈ P := by
    intro u hu h hh
    have := hu (((⟨h, hh⟩ : ↥H)) : ↥H ⧸ P.subgroupOf H)
    rw [Subgroup.smul_def, hsm, QuotientGroup.eq] at this
    have h2 : (h⁻¹ * (((u : ↥H) : G))⁻¹ * h) ∈ P := by
      have := Subgroup.mem_subgroupOf.1 this
      simpa [mul_assoc] using this
    have h3 := P.inv_mem h2
    have e : (h⁻¹ * (((u : ↥H) : G))⁻¹ * h)⁻¹ = h⁻¹ * ((u : ↥H) : G) * h := by group
    rwa [e] at h3
  rcases key t₁ t₂ with h | h | h
  · exact Or.inl (conv t₁ h)
  · exact Or.inr (Or.inl (conv t₂ h))
  · refine Or.inr (Or.inr ?_)
    intro g hg
    have := conv (t₁ * t₂⁻¹) h g hg
    simpa [t₁, t₂] using this

theorem core_of_fix_point {H P S : Subgroup G} (hPH : P ≤ H) (hSP : S ≤ P)
    (h3 : P.relIndex H = 3) {s : G} (hs : s ∈ H) (hsP : s ∉ P) :
    ∀ q ∈ S, s⁻¹ * q * s ∈ P → ∀ h ∈ H, h⁻¹ * q * h ∈ P := by
  intro q hq hqs
  have hSH : S ≤ H := hSP.trans hPH
  have hX : Nat.card (↥H ⧸ P.subgroupOf H) = 3 := by
    rw [← Subgroup.index_eq_card]; exact h3
  obtain ⟨a, b, hx0a, hx0b, hab, hall⟩ :=
    exists_two_others hX (((1 : ↥H)) : ↥H ⧸ P.subgroupOf H)
  have hsm : ∀ (t g : ↥H),
      (t • (g : ↥H ⧸ P.subgroupOf H) : ↥H ⧸ P.subgroupOf H) =
        ((t * g : ↥H) : ↥H ⧸ P.subgroupOf H) := fun t g => rfl
  have hfix : ∀ u : ↥(S.subgroupOf H),
      u • (((1 : ↥H)) : ↥H ⧸ P.subgroupOf H) = (((1 : ↥H)) : ↥H ⧸ P.subgroupOf H) := by
    intro u
    rw [Subgroup.smul_def, hsm, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
    exact Subgroup.mem_subgroupOf.2 (hSP (Subgroup.mem_subgroupOf.1 u.2))
  let t : ↥(S.subgroupOf H) := ⟨⟨q, hSH hq⟩, Subgroup.mem_subgroupOf.2 hq⟩
  let y : ↥H ⧸ P.subgroupOf H := (((⟨s, hs⟩ : ↥H)) : ↥H ⧸ P.subgroupOf H)
  have hy0 : y ≠ (((1 : ↥H)) : ↥H ⧸ P.subgroupOf H) := by
    intro h
    rw [QuotientGroup.eq] at h
    have h' : (s⁻¹ : G) ∈ P := by simpa [y] using Subgroup.mem_subgroupOf.1 h
    exact hsP (by simpa using P.inv_mem h')
  have hty : t • y = y := by
    show ((⟨q, hSH hq⟩ : ↥H) • y) = y
    rw [hsm, QuotientGroup.eq]
    have h' := P.inv_mem hqs
    have e : (s⁻¹ * q * s)⁻¹ = s⁻¹ * q⁻¹ * s := by group
    rw [e] at h'
    exact Subgroup.mem_subgroupOf.2 (by simpa [mul_assoc] using h')
  have hfixall : ∀ x : ↥H ⧸ P.subgroupOf H, t • x = x := by
    rcases action_three_aux (S := ↥(S.subgroupOf H)) _ a b hfix hx0a hx0b hab hall t with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro x
      rcases hall x with rfl | rfl | rfl
      · exact hfix t
      · exact h1
      · exact h2
    · exfalso
      rcases hall y with h | h | h
      · exact hy0 h
      · rw [h] at hty; exact hab (hty.symm.trans h1)
      · rw [h] at hty; exact hab (hty.symm.trans h2).symm
  intro h hh
  have := hfixall (((⟨h, hh⟩ : ↥H)) : ↥H ⧸ P.subgroupOf H)
  rw [Subgroup.smul_def, hsm, QuotientGroup.eq] at this
  have h2 : (h⁻¹ * (q⁻¹ * h)) ∈ P := by
    have := Subgroup.mem_subgroupOf.1 this
    simpa [mul_assoc] using this
  have h3' := P.inv_mem h2
  have e : (h⁻¹ * (q⁻¹ * h))⁻¹ = h⁻¹ * q * h := by group
  rwa [e] at h3'

end Core

end CFSG.Quasithin.H13.I51
