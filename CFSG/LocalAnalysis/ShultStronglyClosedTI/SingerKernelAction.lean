module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerMinimalBlock
public import CFSG.Permutation.BurnsideSchur.Main

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module MulAction

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace MinimalBlock

variable (M : MinimalBlock k F)

theorem smul_mem_Δ_of_mem_K {h : F ≃ₗ[k] F} (hh : h ∈ M.K) {p : ℙ k F} (hp : p ∈ M.Δ) :
    h • p ∈ M.Δ :=
  (M.smul_mem_iff_of_mem_K hh M.Δ_mem_blocks).mpr hp

instance : MulAction M.K M.Δ where
  smul h p := ⟨(h : F ≃ₗ[k] F) • (p : ℙ k F), M.smul_mem_Δ_of_mem_K h.2 p.2⟩
  one_smul p := Subtype.ext (one_smul _ (p : ℙ k F))
  mul_smul h h' p := Subtype.ext (mul_smul (h : F ≃ₗ[k] F) (h' : F ≃ₗ[k] F) (p : ℙ k F))

theorem coe_K_smul (h : M.K) (p : M.Δ) :
    ((h • p : M.Δ) : ℙ k F) = (h : F ≃ₗ[k] F) • (p : ℙ k F) :=
  rfl

@[expose] def BuToK : M.Bu →* M.K :=
  MonoidHom.codRestrict ((scalarHom k F).comp M.Bu.subtype) M.K fun c => M.scalarHom_mem_K c.2

theorem coe_BuToK (c : M.Bu) : (M.BuToK c : F ≃ₗ[k] F) = scalarHom k F c :=
  rfl

@[expose] def permK : Subgroup (Equiv.Perm M.Δ) := (MulAction.toPermHom M.K M.Δ).range

@[expose] def permBu : Subgroup (Equiv.Perm M.Δ) :=
  ((MulAction.toPermHom M.K M.Δ).comp M.BuToK).range

theorem permBu_le : M.permBu ≤ M.permK := by
  rintro _ ⟨c, rfl⟩
  exact ⟨M.BuToK c, rfl⟩

theorem mem_permK {σ : Equiv.Perm M.Δ} :
    σ ∈ M.permK ↔ ∃ h : M.K, ∀ p : M.Δ, σ p = h • p := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, fun _ => rfl⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, Equiv.ext fun p => (hh p).symm⟩

theorem mem_permBu {σ : Equiv.Perm M.Δ} :
    σ ∈ M.permBu ↔ ∃ c ∈ M.Bu, ∀ p : M.Δ, (σ p : ℙ k F) = c • (p : ℙ k F) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, fun p => scalarHom_smul (c : Fˣ) (p : ℙ k F)⟩
  · rintro ⟨c, hc, hσ⟩
    refine ⟨⟨c, hc⟩, Equiv.ext fun p => Subtype.ext ?_⟩
    rw [hσ p]
    exact scalarHom_smul c (p : ℙ k F)

theorem isPretransitive_permBu : IsPretransitive M.permBu M.Δ := by
  refine ⟨fun p q => ?_⟩
  obtain ⟨c, hc, hcq⟩ := M.Bu_transitive M.Δ_mem_blocks p.2 q.2
  refine ⟨⟨_, ⟨⟨c, hc⟩, rfl⟩⟩, Subtype.ext ?_⟩
  rw [← hcq]
  exact scalarHom_smul c (p : ℙ k F)

theorem stabilizer_permBu_eq_bot (p : M.Δ) : stabilizer M.permBu p = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro ⟨σ, hσ⟩ hσp
  obtain ⟨c, hc, hcσ⟩ := M.mem_permBu.mp hσ
  have hfix : c • (p : ℙ k F) = p := by
    rw [← hcσ p]
    exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hσp)
  have hk := units_smul_eq_self_iff.mp hfix
  refine Subtype.ext (Equiv.ext fun q => Subtype.ext ?_)
  change (σ q : ℙ k F) = q
  rw [hcσ q]
  exact units_smul_eq_self_iff.mpr hk

instance isCyclic_permBu [Finite F] : IsCyclic M.permBu :=
  isCyclic_of_surjective ((MulAction.toPermHom M.K M.Δ).comp M.BuToK).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

theorem isBlock_G_of_isBlock_K [Finite F] {Y : Set (ℙ k F)} (hY : Y ⊆ M.Δ)
    (hKY : ∀ h ∈ M.K, h • Y = Y ∨ Disjoint (h • Y) Y) :
    ∀ g ∈ M.G, g • Y = Y ∨ Disjoint (g • Y) Y := by
  have hBuY : ∀ X : Set (ℙ k F), (∀ h ∈ M.K, h • X = X ∨ Disjoint (h • X) X) →
      ∀ c ∈ M.Bu, c • X = X ∨ Disjoint (c • X) X := by
    intro X hX c hc
    rw [← scalarHom_smul_set]
    exact hX _ (M.scalarHom_mem_K hc)
  intro g hg
  rcases M.isBlock g hg with hgΔ | hgΔ
  ·
    have hgY : g • Y ⊆ M.Δ := hgΔ ▸ Set.smul_set_mono hY
    have hKgY : ∀ h ∈ M.K, h • g • Y = g • Y ∨ Disjoint (h • g • Y) (g • Y) := by
      intro h hh
      have hc : g⁻¹ * h * g ∈ M.K := by
        have := M.conj_mem_K (M.G.inv_mem hg) hh
        rwa [inv_inv] at this
      have e : h • g • Y = g • (g⁻¹ * h * g) • Y := by
        rw [← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [e]
      rcases hKY _ hc with h1 | h1
      · exact Or.inl (by rw [h1])
      · exact Or.inr (Set.disjoint_smul_set.mpr h1)
    by_cases hne : (g • Y ∩ Y).Nonempty
    · obtain ⟨z, hz₁, hz₂⟩ := hne
      exact Or.inl (M.eq_of_Bu_blocks hgY hY (hBuY _ hKgY) (hBuY _ hKY)
        (Set.ncard_smul_set g Y) hz₁ hz₂)
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hne))
  · exact Or.inr (Set.disjoint_of_subset (Set.smul_set_mono hY) hY hgΔ)

theorem isPreprimitive_K [Finite F] : IsPreprimitive M.K M.Δ where
  exists_smul_eq p q := by
    obtain ⟨c, hc, hcq⟩ := M.Bu_transitive M.Δ_mem_blocks p.2 q.2
    exact ⟨M.BuToK ⟨c, hc⟩, Subtype.ext (by rw [coe_K_smul, coe_BuToK, scalarHom_smul]; exact hcq)⟩
  isTrivialBlock_of_isBlock {X} hX := by
    set Y : Set (ℙ k F) := Subtype.val '' X with hYdef
    have hY : Y ⊆ M.Δ := by
      rintro _ ⟨p, -, rfl⟩
      exact p.2
    have himage : ∀ h : M.K, Subtype.val '' (h • X) = (h : F ≃ₗ[k] F) • Y := by
      intro h
      ext q
      simp only [Set.mem_image, Set.mem_smul_set, hYdef]
      constructor
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨h • p, ⟨p, hp, rfl⟩, rfl⟩
    have hKY : ∀ h ∈ M.K, h • Y = Y ∨ Disjoint (h • Y) Y := by
      intro h hh
      rcases hX.smul_eq_or_disjoint ⟨h, hh⟩ with h1 | h1
      · left
        rw [← himage ⟨h, hh⟩, h1]
      · right
        rw [← himage ⟨h, hh⟩]
        exact (Set.disjoint_image_iff Subtype.val_injective).mpr h1
    have hGY := M.isBlock_G_of_isBlock_K hY hKY
    by_cases h1 : 1 < Y.ncard
    · right
      have hle := M.minimal Y hGY h1
      have hYΔ : Y = M.Δ := Set.eq_of_subset_of_ncard_le hY hle
      rw [Set.eq_univ_iff_forall]
      intro p
      have : (p : ℙ k F) ∈ Y := by rw [hYΔ]; exact p.2
      obtain ⟨q, hq, hqp⟩ := this
      rwa [← Subtype.ext hqp]
    · left
      have hsub : Y.Subsingleton := Set.ncard_le_one_iff_subsingleton.mp (by omega)
      intro a ha b hb
      exact Subtype.ext (hsub ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)

instance isPreprimitive_permK [Finite F] : IsPreprimitive M.permK M.Δ := by
  have := M.isPreprimitive_K
  let f : M.Δ →ₑ[(MulAction.toPermHom M.K M.Δ).rangeRestrict] M.Δ :=
    { toFun := id
      map_smul' := fun _ _ => rfl }
  exact IsPreprimitive.of_surjective (f := f) Function.surjective_id

theorem burnside_schur_K [Finite F] :
    IsMultiplyPretransitive M.permK M.Δ 2 ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card M.Δ = p ∧ ∃ e : M.Δ ≃ ZMod p,
        e.permCongr '' (M.permBu : Set (Equiv.Perm M.Δ)) = {t | ∃ b, ∀ x, t x = x + b} ∧
        (∀ g ∈ M.permK, ∃ a ≠ 0, ∃ b, ∀ x, e (g x) = a * e x + b) := by
  have := M.isPretransitive_permBu
  have hΩ : 2 ≤ Nat.card M.Δ := by
    rw [Nat.card_coe_set_eq]
    exact M.one_lt_ncard
  rcases CFSG.burnside_schur M.permK M.permBu hΩ M.permBu_le M.stabilizer_permBu_eq_bot with
    h | ⟨p, hp, hcard, e, he, haff, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, hp, hcard, e, he, haff⟩

end MinimalBlock

end CFSG.ShultStronglyClosedTI.Singer
