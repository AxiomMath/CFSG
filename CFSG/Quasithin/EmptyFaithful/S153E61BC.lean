module

public import CFSG.Quasithin.EmptyFaithful.S153E57E
public import CFSG.Quasithin.EmptyFaithful.S153E59E

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E61B

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem rho59_eq_rho57 (cx : Ctx15350 T Mc M V₁ V₂ t) (h : ↥Mc) :
    S153E59.rho cx h = S153E57.rho cx ⟨h, S153E57.Mc_le_NZ cx h.2⟩ := by
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  rw [S153E59.rho_apply_coe, S153E57.rho_apply_coe]
  rfl

theorem exists_a_V_not_U (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁) :
    ∃ a ∈ VZ T M, a ∉ UH153 T M V₁ Mc := by
  by_contra h
  push Not at h
  exact c.h51.one (fun a ha => c.h59.one ▸ h a ha)

theorem rho_a_data (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁)
    {a : G} (ha : a ∈ VZ T M) (haU : a ∉ UH153 T M V₁ Mc) (hN : a ∈ S153E57.NZ T) :
    S153E57.rho cx ⟨a, hN⟩ ≠ 1 ∧ S153E57.rho cx ⟨a, hN⟩ ∈ XStar153 T M V₁ Mc (VZ T M) ∧
      ∀ w ∈ XStar153 T M V₁ Mc (VZ T M), w = 1 ∨ w = S153E57.rho cx ⟨a, hN⟩ := by
  have hMc : a ∈ Mc := S153E59.VZ_le_Mc cx ha
  have hne : S153E57.rho cx ⟨a, hN⟩ ≠ 1 := by
    intro h1
    rw [← rho59_eq_rho57 cx ⟨a, hMc⟩, S153E59.rho_eq_one_iff cx ⟨a, hMc⟩] at h1
    exact haU (c.h59.one ▸ h1)
  have hmem : S153E57.rho cx ⟨a, hN⟩ ∈ XStar153 T M V₁ Mc (VZ T M) :=
    S153E57.rho_mem_XStar cx ⟨a, hN⟩ ha
  refine ⟨hne, hmem, ?_⟩
  obtain ⟨v, -, -, huniq⟩ := S153E57.exists_v c.toChain15356
  intro w hw
  rcases huniq w hw with h | h
  · exact Or.inl h
  · rcases huniq _ hmem with h' | h'
    · exact absurd h' hne
    · exact Or.inr (h.trans h'.symm)

end Basic

end S153E61B

end CFSG.Quasithin
