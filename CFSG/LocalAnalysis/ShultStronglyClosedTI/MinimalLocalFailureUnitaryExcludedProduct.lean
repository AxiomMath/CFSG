module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedCosetHull

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
  {t u : G} {A P : Subgroup G} {d : ExclusionSetup H z beta t u A P}

theorem ExclusionSetup.mem_baseOrbit_pairHull (d : ExclusionSetup H z beta t u A P)
    {γ : rightCosetSpace H} (h₁ : γ ∈ baseOrbit H (uHull z u))
    (h₂ : γ ∈ baseOrbit H (aHull z A)) :
    γ ∈ baseOrbit H (minimalLocalFailureProperPairHull H z beta t) := by
  obtain ⟨l₁, hl₁, rfl⟩ := h₁
  obtain ⟨l₂, hl₂, h₁₂⟩ := h₂
  have hh : l₁ * l₂⁻¹ ∈ H := (rightCosetMk_eq_iff H l₂ l₁).mp h₁₂
  have hzQ : z ∈ minimalLocalFailurePairActionPointHull H z :=
    Subgroup.subset_closure ⟨1, by simp⟩
  have hQLu := point_le_pairHull d.Fu
  have hrLu : l₁⁻¹ * z * l₁ ∈ uHull z u :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hl₁)
      (pairHull_le d.Fu (hQLu hzQ))) hl₁
  have hhz : (l₁ * l₂⁻¹)⁻¹ * z * (l₁ * l₂⁻¹) ∈ minimalLocalFailurePairActionPointHull H z :=
    point_subgroup_normalized d.point_class _ hh z hzQ
  have hrLA : l₁⁻¹ * z * l₁ ∈ aHull z A := by
    have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hl₂)
      (pairHull_le d.FA (point_le_pairHull d.FA hhz))) hl₂
    rwa [show l₂⁻¹ * ((l₁ * l₂⁻¹)⁻¹ * z * (l₁ * l₂⁻¹)) * l₂ = l₁⁻¹ * z * l₁ by group] at h
  have hrD : l₁⁻¹ * z * l₁ ∈ involutionPointClass z := ⟨l₁, rfl⟩
  have hrK : l₁⁻¹ * z * l₁ ∈ conjugacyWithin (minimalLocalFailureProperPairHull H z beta t) z := by
    rw [← d.pairHull_class, ← d.overlap]
    exact ⟨⟨hrD, hrLu⟩, hrLA⟩
  obtain ⟨k, hk⟩ := hrK
  have hfix₁ : rightCosetTranslate H (rightCosetMk H l₁) (l₁⁻¹ * z * l₁) = rightCosetMk H l₁ := by
    rw [translate_mk_fixed_iff, show l₁ * (l₁⁻¹ * z * l₁) * l₁⁻¹ = z by group]
    exact d.datum.distinguished_mem
  have hfix₂ : rightCosetTranslate H (rightCosetMk H (k : G)) (l₁⁻¹ * z * l₁) =
      rightCosetMk H k := by
    rw [translate_mk_fixed_iff, ← hk, show (k : G) * ((k : G)⁻¹ * z * k) * (k : G)⁻¹ = z by group]
    exact d.datum.distinguished_mem
  exact ⟨k, k.2, (class_fixed_unique d.datum hrD hfix₁ hfix₂).symm⟩

omit [Finite G] in
theorem ExclusionSetup.card_root (d : ExclusionSetup H z beta t u A P) :
    Nat.card d.Fu.root = Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 :=
  (root_structure d.Fu.J d.Fu.rootEquiv (2 ^ d.Fu.f) d.Fu.hcard d.Fu.hfixed).1.trans
    (congrArg (· ^ 3) d.Fu.hq.symm)

namespace BarCoordinates

variable (b : BarCoordinates d)

theorem U_le_normalizer_root : b.U ≤ Subgroup.normalizer (d.Fu.root : Set G) := fun _ hx =>
  d.mem_normalizer_root (b.U_le_normalizer hx) (b.U_le_centralizer_A hx)

theorem W_le_normalizer_root : b.W ≤ Subgroup.normalizer (d.Fu.root : Set G) :=
  sup_le b.U_le_normalizer_root (Subgroup.zpowers_le.mpr
    (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ hx =>
      d.root_commute_u hx)))

omit [Finite G] in
theorem pow_four_of_mem_U {x : G} (hx : x ∈ b.U) : x ^ 2 ^ 2 = 1 :=
  pow_four_eq_one_of_mem_hull Subtype.val_injective d.u_sq b.bar_field (b.U_le_W hx)

theorem commutator_mem {x τ : G} (hx : x ∈ b.U) (hτ : τ ∈ d.Fu.root) :
    x * τ * x⁻¹ * τ⁻¹ ∈ minimalLocalFailurePairActionPointHull H z :=
  d.commutator_mem_point (b.U_le_normalizer hx) (b.U_le_centralizer_A hx)
    (b.U_le_centralizer_point hx) (b.pow_four_of_mem_U hx) hτ

theorem root_le_normalizer_W : d.Fu.root ≤ Subgroup.normalizer (b.W : Set G) := by
  intro τ hτ
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨w, hw, rfl⟩
  change τ * w * τ⁻¹ ∈ b.W
  obtain ⟨x, hx, h | h⟩ := (b.mem_W_iff w).mp hw <;> rw [h]
  · have hc := b.U_le_W (b.point_le_U (b.commutator_mem hx hτ))
    rw [show τ * x * τ⁻¹ = (x * τ * x⁻¹ * τ⁻¹)⁻¹ * x by group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) (b.U_le_W hx)
  · have hc := b.U_le_W (b.point_le_U (b.commutator_mem hx hτ))
    rw [show τ * (u * x) * τ⁻¹ = τ * u * x * τ⁻¹ by group, d.root_commute_u hτ,
      show u * τ * x * τ⁻¹ = u * ((x * τ * x⁻¹ * τ⁻¹)⁻¹ * x) by group]
    exact Subgroup.mul_mem _ b.u_mem_W (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) (b.U_le_W hx))

theorem root_inf_W : d.Fu.root ⊓ b.W = minimalLocalFailurePairActionPointHull H z := by
  refine le_antisymm ?_ (le_inf (le_root d.Fu) (b.point_le_U.trans b.U_le_W))
  rintro g ⟨hgT, hgW⟩
  obtain ⟨x, hx, rfl | rfl⟩ := (b.mem_W_iff g).mp hgW
  · exact d.mem_point_of_mem_root_of_commute hgT (b.U_le_centralizer_A hx)
  · exfalso
    have hcomm := d.root_commute_u hgT
    have hxu : u * x * u⁻¹ = x := by
      have h : u * (x * u) = u * (u * x) := by rw [← mul_assoc, hcomm]
      rw [← mul_left_cancel h, mul_inv_cancel_right]
    have hx2 : x * x = 1 := by
      have h := b.conj_U hx
      rw [hxu] at h
      calc x * x = x * x⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel x
    have hxT : x ∈ d.Fu.root := le_root d.Fu (b.mem_point_of_mul_self hx hx2)
    have huT : u ∈ d.Fu.root := by
      have h := Subgroup.mul_mem _ hgT (Subgroup.inv_mem _ hxT)
      rwa [mul_inv_cancel_right] at h
    exact d.u_not_mem_hull d.Fu (d.Fu.root_le huT)

omit [Finite G] in
theorem card_W' : Nat.card b.W = 2 * Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 :=
  b.card_W.trans (congrArg (fun n => 2 * n ^ 2) d.FA.hq.symm)

theorem card_S : Nat.card (d.Fu.root ⊔ b.W : Subgroup G) =
    2 * Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 4 := by
  have h := card_sup_mul_card_inf b.W_le_normalizer_root
  rw [b.root_inf_W, d.card_root, b.card_W'] at h
  have hq : 0 < Nat.card (minimalLocalFailurePairActionPointHull H z) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [h]
  ring

theorem S_isPGroup : IsPGroup 2 (d.Fu.root ⊔ b.W : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' (ExclusionSetup.root_isPGroup d.Fu) b.W_isPGroup
    b.W_le_normalizer_root

theorem S_le_normalizer_W : d.Fu.root ⊔ b.W ≤ Subgroup.normalizer (b.W : Set G) :=
  sup_le b.root_le_normalizer_W Subgroup.le_normalizer

omit [Finite G] in
theorem S_le_normalizer_coset : d.Fu.root ⊔ b.W ≤
    Subgroup.normalizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)) :=
  sup_le (d.root_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)) b.W_le_normalizer

theorem eq_one_of_fixes {τ x : G} (hτ : τ ∈ d.Fu.root) (hx : x ∈ b.U)
    (hfix : rightCosetTranslate H beta (τ * x) = beta) : τ * x = 1 := by
  have hγ : rightCosetTranslate H beta τ = rightCosetTranslate H beta x⁻¹ := by
    conv_rhs => rw [← hfix]
    rw [rightCosetTranslate_mul, mul_inv_cancel_right]
  have hβ : beta = rightCosetMk H t := d.flip_coset
  have htLu := flip_mem d.Fu
  have htLA := flip_mem d.FA
  have hxLA := d.FA.root_le (b.U_le_root hx)
  have h₁ : rightCosetTranslate H beta τ ∈ baseOrbit H (uHull z u) :=
    ⟨t * τ, Subgroup.mul_mem _ htLu (d.Fu.root_le hτ), by rw [hβ, rightCosetTranslate_mk]⟩
  have h₂ : rightCosetTranslate H beta τ ∈ baseOrbit H (aHull z A) :=
    ⟨t * x⁻¹, Subgroup.mul_mem _ htLA (Subgroup.inv_mem _ hxLA),
      by rw [hγ, hβ, rightCosetTranslate_mk]⟩
  have hK := d.mem_baseOrbit_pairHull h₁ h₂
  obtain ⟨w₁, rfl⟩ := hτ
  have hτQ := (rootHom_mem_iff d.Fu w₁).mpr
    (fst_eq_zero_of_translate_mem_baseOrbit d.Fu d.flip_coset d.flip_sq hK)
  obtain ⟨w₂, hw₂⟩ := Subgroup.inv_mem _ (b.U_le_root hx)
  rw [hγ, ← hw₂] at hK
  have hxQ := (rootHom_mem_iff d.FA w₂).mpr
    (fst_eq_zero_of_translate_mem_baseOrbit d.FA d.flip_coset d.flip_sq hK)
  rw [hw₂] at hxQ
  have hmem : d.Fu.rootHom w₁ * x ∈ minimalLocalFailurePairActionPointHull H z := by
    have h := Subgroup.mul_mem _ hτQ (Subgroup.inv_mem _ hxQ)
    rwa [inv_inv] at h
  exact eq_one_of_mem_root_of_fixes d.Fu d.flip_coset d.beta_ne (le_root d.Fu hmem) hfix

theorem eq_one_or_eq_u {s : G} (hsS : s ∈ d.Fu.root ⊔ b.W)
    (hsB : s ∈ pairPointStabilizer H beta) : s = 1 ∨ s = u := by
  have hfix : rightCosetTranslate H beta s = beta := (mem_rightCosetStabilizer_iff H _ s).mp hsB.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    b.W_le_normalizer_root] at hsS
  obtain ⟨τ, hτ, w, hw, rfl⟩ := hsS
  dsimp only at hfix ⊢
  obtain ⟨x, hx, rfl | rfl⟩ := (b.mem_W_iff w).mp hw
  · exact Or.inl (b.eq_one_of_fixes hτ hx hfix)
  · right
    have hτu := d.root_commute_u hτ
    have hs : τ * (u * x) = u * (τ * x) := by rw [← mul_assoc, hτu, mul_assoc]
    have hfix' : rightCosetTranslate H beta (τ * x) = beta := by
      rw [hs, ← rightCosetTranslate_mul, d.u_fixes_beta] at hfix
      exact hfix
    rw [hs, b.eq_one_of_fixes hτ hx hfix', mul_one]

end BarCoordinates

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
