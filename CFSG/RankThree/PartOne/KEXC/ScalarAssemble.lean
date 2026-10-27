module

public import CFSG.RankThree.PartOne.KF.FratRows

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

theorem exists_scalar_of_weyl_scalar {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (ctx : Fus12Ctx G p A c L E) {n : G}
    (hn : n ∈ cNormalizer c ⊓ torusNormalizer E)
    (H : ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) →
      y ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) →
      ∃ h : G, h ∈ L ∧ h ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ∧
        ∃ k : ℤ, ∀ f ∈ E ⊓ L, y * f * y⁻¹ = h * f ^ k * h⁻¹) :
    ∃ l ∈ L ⊓ torusNormalizer E, ∃ k : ℕ, ∀ f ∈ E ⊓ L, (l * n) * f * (l * n)⁻¹ = f ^ k := by
  have hcore := ctx.table_core
  have hnL : n ∈ Subgroup.normalizer (L : Set G) := ctx.facts.twoB hn
  have hnF := ctx.mem_normalizer_inf hn
  obtain ⟨h, hhL, hhF, k, hk⟩ := H n hnL hnF
  have hlL : h⁻¹ ∈ L := L.inv_mem hhL
  have hlF : h⁻¹ ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
    (Subgroup.normalizer _).inv_mem hhF
  have hp : 0 < p := hcore.prime.pos
  have h0 : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  refine ⟨h⁻¹, ⟨hlL, ctx.mem_torusNormalizer hlL hlF⟩, (k % (p : ℤ)).toNat, fun f hf => ?_⟩
  have hfp : f ^ p = 1 := hcore.F_exp f hf
  calc (h⁻¹ * n) * f * (h⁻¹ * n)⁻¹ = h⁻¹ * (n * f * n⁻¹) * h := by group
    _ = h⁻¹ * (h * f ^ k * h⁻¹) * h := by rw [hk f hf]
    _ = f ^ k := by group
    _ = f ^ (k % (p : ℤ)).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h0]
      exact zpow_eq_zpow_emod' k hfp

end CFSG.RankThree.PartOne.KEXC
