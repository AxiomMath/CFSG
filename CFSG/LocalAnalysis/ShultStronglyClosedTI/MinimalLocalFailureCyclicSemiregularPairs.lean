module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.GroupTheory.Index

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

theorem act_translate_injective {G Ω : Type*} [Group G] (act : Ω → G → Ω)
    (act_one : ∀ ω, act ω 1 = ω) (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h)) (g : G) :
    Function.Injective (act · g) := fun x y hxy => by
  simpa only [act_mul, mul_inv_cancel, act_one] using congrArg (act · g⁻¹) hxy

theorem exists_act_eq_of_pair_transitive {G Ω : Type*} [Group G] (act : Ω → G → Ω)
    (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h)) (C : Subgroup G) (s : Finset Ω)
    (hgt : 2 < s.card)
    (hpairs : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s, a ≠ b → c ≠ d →
      ∃ g ∈ C, (act a g = c ∧ act b g = d) ∨ (act a g = d ∧ act b g = c)) :
    ∀ x ∈ s, ∀ y ∈ s, ∃ g ∈ C, act x g = y := by
  classical
  intro x hx y hy
  obtain ⟨z, hz, hzxy⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card ((Finset.card_le_two (a := x) (b := y)).trans_lt hgt)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzxy
  obtain ⟨g, hg, ⟨h, -⟩ | ⟨h₁, h₂⟩⟩ :=
    hpairs x hx z hz y hy z hz (Ne.symm hzxy.1) (Ne.symm hzxy.2)
  · exact ⟨g, hg, h⟩
  · exact ⟨g * g, C.mul_mem hg hg, by rw [← act_mul, h₁, h₂]⟩

theorem odd_card_of_invariant_tournament {G Ω : Type*} [Group G] (act : Ω → G → Ω)
    (act_one : ∀ ω, act ω 1 = ω) (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h))
    (C : Subgroup G) (s : Finset Ω) (hs : s.Nonempty) (hpres : ∀ x ∈ s, ∀ g ∈ C, act x g ∈ s)
    (htrans : ∀ x ∈ s, ∀ y ∈ s, ∃ g ∈ C, act x g = y) (r : Ω → Ω → Prop)
    (hr : ∀ x y, ∀ g ∈ C, r x y → r (act x g) (act y g))
    (htot : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y ∨ r y x) (hasymm : ∀ x y, r x y → ¬r y x) :
    Odd s.card := by
  classical
  have hle : ∀ r' : Ω → Ω → Prop, (∀ x y, ∀ g ∈ C, r' x y → r' (act x g) (act y g)) →
      ∀ x ∈ s, ∀ x' ∈ s, (s.filter (r' x)).card ≤ (s.filter (r' x')).card := by
    intro r' hr' x hx x' hx'
    obtain ⟨g, hg, rfl⟩ := htrans x hx x' hx'
    refine Finset.card_le_card_of_injOn (act · g) (fun y hy => ?_)
      (act_translate_injective act act_one act_mul g).injOn
    rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    exact ⟨hpres y hy.1 g hg, hr' x y g hg hy.2⟩
  have hr' : ∀ x y, ∀ g ∈ C, r y x → r (act y g) (act x g) := fun x y g hg => hr y x g hg
  obtain ⟨x₀, hx₀⟩ := hs
  have hmn : s.card * (s.filter (r x₀)).card = s.card * (s.filter (fun y => r y x₀)).card :=
    Finset.card_mul_eq_card_mul r
      (fun x hx => le_antisymm (hle r hr x hx x₀ hx₀) (hle r hr x₀ hx₀ x hx))
      (fun y hy => le_antisymm (hle (fun x y => r y x) hr' y hy x₀ hx₀)
        (hle (fun x y => r y x) hr' x₀ hx₀ y hy))
  have hsum : (s.filter (r x₀)).card + (s.filter (fun y => r y x₀)).card = s.card - 1 := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_filter.2 fun y _ h₁ h₂ => hasymm _ _ h₁ h₂), ← Finset.card_erase_of_mem hx₀]
    congr 1
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hy, h⟩ | ⟨hy, h⟩) <;> refine ⟨?_, hy⟩ <;> rintro rfl <;> exact hasymm _ _ h h
    · rintro ⟨hne, hy⟩
      exact (htot x₀ hx₀ y hy (Ne.symm hne)).imp (fun h => ⟨hy, h⟩) fun h => ⟨hy, h⟩
  have hpos : 0 < s.card := Finset.card_pos.2 ⟨x₀, hx₀⟩
  have heq := Nat.eq_of_mul_eq_mul_left hpos hmn
  exact ⟨(s.filter (r x₀)).card, by omega⟩

theorem two_transitive_of_unordered_pair_transitive {G Ω : Type*} [Group G]
    (act : Ω → G → Ω) (act_one : ∀ ω, act ω 1 = ω)
    (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h))
    (C : Subgroup G) (Δ : Set Ω) (hΔ : Δ.Finite)
    (hpres : ∀ ω ∈ Δ, ∀ c ∈ C, act ω c ∈ Δ)
    (heven : Even (Nat.card Δ)) (hgt : 2 < Nat.card Δ)
    (hpairs : ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
      ∃ g ∈ C, (act a g = c ∧ act b g = d) ∨ (act a g = d ∧ act b g = c)) :
    ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
      ∃ g ∈ C, act a g = c ∧ act b g = d := by
  intro a ha b hb c hc d hd hab hcd
  by_cases hba : ∃ h ∈ C, act a h = b ∧ act b h = a
  · obtain ⟨h, hhC, hha, hhb⟩ := hba
    obtain ⟨g, hgC, hg | hg⟩ := hpairs a ha b hb c hc d hd hab hcd
    · exact ⟨g, hgC, hg⟩
    · exact ⟨h * g, C.mul_mem hhC hgC, by rw [← act_mul, hha, hg.2],
        by rw [← act_mul, hhb, hg.1]⟩
  exfalso
  obtain ⟨s, rfl⟩ := hΔ.exists_finset_coe
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset] at heven hgt
  refine Nat.not_odd_iff_even.2 heven <| odd_card_of_invariant_tournament act act_one act_mul C s
    (Finset.card_pos.1 (by omega)) hpres
    (exists_act_eq_of_pair_transitive act act_mul C s hgt hpairs)
    (fun x y => ∃ g ∈ C, act a g = x ∧ act b g = y) ?_ ?_ ?_
  · rintro x y k hk ⟨g, hg, rfl, rfl⟩
    exact ⟨g * k, C.mul_mem hg hk, (act_mul a g k).symm, (act_mul b g k).symm⟩
  · intro x hx y hy hxy
    obtain ⟨g, hg, h | h⟩ := hpairs a ha b hb x hx y hy hab hxy
    · exact Or.inl ⟨g, hg, h⟩
    · exact Or.inr ⟨g, hg, h⟩
  · rintro x y ⟨g, hg, hgx, hgy⟩ ⟨k, hk, hky, hkx⟩
    refine hba ⟨k * g⁻¹, C.mul_mem hk (C.inv_mem hg), ?_, ?_⟩
    · rw [← act_mul, hky, ← hgy, act_mul, mul_inv_cancel, act_one]
    · rw [← act_mul, hkx, ← hgx, act_mul, mul_inv_cancel, act_one]

theorem card_dvd_card_of_free {G Ω : Type*} [Group G] [Finite G]
    (act : Ω → G → Ω) (act_one : ∀ ω, act ω 1 = ω)
    (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h))
    (X : Subgroup G) (Γ : Set Ω) (hΓ : Γ.Finite)
    (hpres : ∀ ω ∈ Γ, ∀ x ∈ X, act ω x ∈ Γ)
    (hfree : ∀ ω ∈ Γ, ∀ x ∈ X, act ω x = ω → x = 1) :
    Nat.card X ∣ Nat.card Γ := by
  let _ : MulAction X Γ :=
    { smul x ω := ⟨act ω (x⁻¹ : X), hpres _ ω.2 _ (x⁻¹).2⟩
      one_smul ω := Subtype.ext <| by
        change act ω ((1⁻¹ : X) : G) = ω
        rw [inv_one, X.coe_one, act_one]
      mul_smul x y ω := Subtype.ext <| by
        change act ω (((x * y)⁻¹ : X) : G) = act (act ω (y⁻¹ : X)) (x⁻¹ : X)
        rw [act_mul, mul_inv_rev, X.coe_mul] }
  have hstab : ∀ ω : Γ, MulAction.stabilizer X ω = ⊥ := fun ω => by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h := hfree ω ω.2 _ (x⁻¹).2 (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hx))
    exact inv_eq_one.1 (Subtype.ext h)
  have _ := hΓ.to_subtype
  have _ := Fintype.ofFinite (MulAction.orbitRel.Quotient X Γ)
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits X Γ), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, hstab, Subgroup.index_bot]

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
