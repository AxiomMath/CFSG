module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolBase
public import CFSG.Quasithin.EmptyFaithful.SzF53BasA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T3

variable {G : Type} [Group G] [Finite G] {H M : Subgroup G}

omit [Finite G] in
theorem relIndex_stab_le_two {N : Subgroup G} (hN : N ≤ H ⊔ M) {δ₀ δ'' : Geo H M}
    (hne : δ'' ≠ δ₀)
    (horb : ∀ q (hq : q ∈ N), (⟨q, hN hq⟩ : ↥(H ⊔ M)) • δ₀ = δ₀ ∨
      (⟨q, hN hq⟩ : ↥(H ⊔ M)) • δ₀ = δ'') :
    (N ⊓ stab δ₀).relIndex N ≤ 2 := by
  classical
  set D : Subgroup ↥N := (N ⊓ stab δ₀).subgroupOf N with hD
  have hmem : ∀ b : ↥N, b ∈ D ↔ (⟨(b : G), hN b.2⟩ : ↥(H ⊔ M)) • δ₀ = δ₀ := by
    intro b
    rw [hD, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact smul_eq_of_mem_stab h.2
    · intro h
      exact ⟨b.2, mem_stab_of_smul_eq h⟩
  have hact : ∀ a b : ↥N, (⟨((a * b : ↥N) : G), hN (a * b).2⟩ : ↥(H ⊔ M)) • δ₀ =
      (⟨(a : G), hN a.2⟩ : ↥(H ⊔ M)) • ((⟨(b : G), hN b.2⟩ : ↥(H ⊔ M)) • δ₀) := by
    intro a b
    rw [← mul_smul]
    rfl
  show D.index ≤ 2
  by_cases htop : D = ⊤
  · rw [htop, Subgroup.index_top]; omega
  · obtain ⟨a, ha⟩ : ∃ a : ↥N, a ∉ D := by
      by_contra h
      push Not at h
      exact htop (eq_top_iff.mpr fun x _ => h x)
    have haδ : (⟨(a : G), hN a.2⟩ : ↥(H ⊔ M)) • δ₀ = δ'' := by
      rcases horb a a.2 with h | h
      · exact absurd ((hmem a).mpr h) ha
      · exact h
    have : D.index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨a, fun b => ?_⟩
      have hab := hact b a
      rw [haδ] at hab
      by_cases hb : b ∈ D
      · have hb' := (hmem b).mp hb
        have hna : b * a ∉ D := by
          intro h
          have h' := (hmem (b * a)).mp h
          rw [hab] at h'
          exact hne (MulAction.injective (⟨(b : G), hN b.2⟩ : ↥(H ⊔ M)) (h'.trans hb'.symm))
        exact Or.inr ⟨hb, hna⟩
      · have hb' : (⟨(b : G), hN b.2⟩ : ↥(H ⊔ M)) • δ₀ = δ'' := by
          rcases horb b b.2 with h | h
          · exact absurd ((hmem b).mpr h) hb
          · exact h
        have hba : b * a ∈ D := by
          rw [hmem]
          have h2 : (⟨((b * a : ↥N) : G), hN (b * a).2⟩ : ↥(H ⊔ M)) • δ₀ = δ₀ ∨
              (⟨((b * a : ↥N) : G), hN (b * a).2⟩ : ↥(H ⊔ M)) • δ₀ = δ'' :=
            horb _ (b * a).2
          rcases h2 with h | h
          · exact h
          · exfalso
            rw [hab] at h
            exact hne (MulAction.injective (⟨(b : G), hN b.2⟩ : ↥(H ⊔ M)) (h.trans hb'.symm))
        exact Or.inl ⟨hba, hb⟩
    omega

end S35.T3

end F53.Stellmacher

end CFSG.Quasithin
