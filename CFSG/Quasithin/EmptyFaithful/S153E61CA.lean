module

public import CFSG.Quasithin.EmptyFaithful.S153E56E1
public import CFSG.Quasithin.EmptyFaithful.T1531Geom

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace S153E61C

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem fuse_V_of_gens (cx : Ctx15350 T Mc M V₁ V₂ t) {z v : G}
    (hz : Subgroup.zpowers z = quasithinOmegaOneCenter T)
    (hv : Subgroup.zpowers v = ZS153 T M V₁ ⊓ V₁) (hv1 : v ≠ 1) :
    ∀ w ∈ VZ T M, w ≠ 1 → (∃ m ∈ M, m * z * m⁻¹ = w) ∨ (∃ m ∈ M, m * v * m⁻¹ = w) := by
  have hzmem : z ∈ quasithinOmegaOneCenter T := hz ▸ Subgroup.mem_zpowers z
  have hzV : z ∈ VZ T M := cx.c.hyp.Z_le_VZ hzmem
  have hq : qV153 cx.c ⟨z, hzV⟩ = 0 := S153E56e.q_z cx hzmem hzV
  have hz1 : z ≠ 1 := by
    rintro rfl
    have h1 := S153E57.Z_card cx
    rw [← hz, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h1
    omega
  have hz12 : z ∉ V₁ ∧ z ∉ V₂ := by
    have hiff := (qV153_spec cx.c).2.2.2.2 z hzV
    have hn : ¬ ((z ∈ V₁ ∨ z ∈ V₂) ∧ z ≠ 1) := fun h => by
      have h1 := hiff.2 h
      rw [hq] at h1
      exact absurd h1 (by decide)
    exact ⟨fun h => hn ⟨Or.inl h, hz1⟩, fun h => hn ⟨Or.inr h, hz1⟩⟩
  have hvV₁ : v ∈ V₁ := (hv ▸ Subgroup.mem_zpowers v : v ∈ ZS153 T M V₁ ⊓ V₁).2
  intro w hwV hw1
  by_cases hw : w ∈ V₁ ∨ w ∈ V₂
  · obtain ⟨m, hm, e⟩ := exists_conj_nonsingular cx.c.decomp ⟨Or.inl hvV₁, hv1⟩ ⟨hw, hw1⟩
    exact Or.inr ⟨m, hm, e⟩
  · obtain ⟨m, hm, e⟩ := exists_conj_singular cx.c.hyp cx.c.decomp ⟨hzV, hz12.1, hz12.2⟩
      ⟨hwV, fun h => hw (Or.inl h), fun h => hw (Or.inr h)⟩
    exact Or.inl ⟨m, hm, e⟩

end S153E61C

end CFSG.Quasithin
