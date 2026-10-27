module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support

open CFSG.Quasithin

variable {G : Type} [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}

theorem isSumOfNaturalModulesVia_restrict {K V V₁ B : Subgroup G} {ψ : ↥K →* ↥Γ} {dual : Bool}
    {k : ℕ} (h : IsSumOfNaturalModulesVia K V B ψ dual k) (hV₁ : V₁ ≤ V)
    (hKV₁ : K ≤ Subgroup.normalizer (V₁ : Set G)) (hn : V₁ ≤ Subgroup.normalizer (B : Set G))
    (hsup : V₁ ⊔ B = V) :
    IsSumOfNaturalModulesVia K V₁ (V₁ ⊓ B) ψ dual k := by
  obtain ⟨-, hBV, β, hβs, hβk, hβe⟩ := h
  refine ⟨hKV₁, inf_le_left, β.comp (Subgroup.inclusion hV₁), ?_, ?_, ?_⟩
  · intro t
    obtain ⟨v, rfl⟩ := hβs t
    have hv : (v : G) ∈ ((V₁ ⊔ B : Subgroup G) : Set G) := by rw [hsup]; exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V₁ B hn] at hv
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hv
    have hyB : (⟨y, hBV hy⟩ : ↥V) ∈ B.subgroupOf V := hy
    rw [← hβk] at hyB
    refine ⟨⟨x, hx⟩, ?_⟩
    have e : v = Subgroup.inclusion hV₁ ⟨x, hx⟩ * ⟨y, hBV hy⟩ := Subtype.ext hxy.symm
    rw [MonoidHom.comp_apply, e, map_mul, MonoidHom.mem_ker.mp hyB, mul_one]
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp only [Subgroup.coe_inclusion, x.2, true_and]
  · intro a u v huv i
    exact hβe a (Subgroup.inclusion hV₁ u) (Subgroup.inclusion hV₁ v) huv i

end CFSG.Quasithin.EmptyFaithful.Stellmacher.MS93Support
