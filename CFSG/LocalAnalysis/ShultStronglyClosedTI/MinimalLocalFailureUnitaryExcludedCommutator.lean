module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedNormalize
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismAut

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

variable {G : Type} [Group G]

theorem isPGroup_zpowers {P : Type*} [Group P] {y : P} {k : ℕ} (hk : y ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers y) := by
  rintro ⟨_, n, rfl⟩
  refine ⟨k, Subtype.ext ?_⟩
  change (y ^ n) ^ 2 ^ k = 1
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk,
    _root_.one_zpow]

theorem coe_mem_of_mem_zpowers {N S : Subgroup G} {y n : N} (hy : (y : G) ∈ S)
    (hn : n ∈ Subgroup.zpowers y) : (n : G) ∈ S := by
  obtain ⟨m, rfl⟩ := hn
  change ((y ^ m : N) : G) ∈ S
  rw [Subgroup.coe_zpow]
  exact zpow_mem hy m

variable [Finite G] {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t u : G}
  {A P : Subgroup G} (d : ExclusionSetup H z beta t u A P)

namespace ExclusionSetup

theorem commutator_mem_point {v : G}
    (hvΔ : v ∈ Subgroup.normalizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)))
    (hvA : v ∈ Subgroup.centralizer (A : Set G))
    (hvQ : v ∈ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G))
    {k : ℕ} (hvk : v ^ 2 ^ k = 1) {τ : G} (hτ : τ ∈ d.Fu.root) :
    v * τ * v⁻¹ * τ⁻¹ ∈ minimalLocalFailurePairActionPointHull H z := by
  have hvN := d.mem_normalizer_root hvΔ hvA
  obtain ⟨c, hc, hcA⟩ := d.exists_torus_noncentral
  have haN := hullTorus_le_normalizer d.Fu (torusElt_mem d.Fu c)
  set Ψ := d.Fu.root.normalizerMonoidHom
  set φ := d.Fu.rootEquiv
  set θa := Ψ ⟨torusElt d.Fu c, haN⟩
  set μ := ((c : d.Fu.kˣ) : d.Fu.k) ^ 3
  have hμ : μ * d.Fu.J.conj μ = 1 := by
    have h := c.2
    change ((c : d.Fu.kˣ) : d.Fu.k) * d.Fu.J.conj ((c : d.Fu.kˣ) : d.Fu.k) = 1 at h
    rw [map_pow, ← mul_pow, h, one_pow]
  have hθ : ∀ x : d.Fu.root, (φ.symm (θa x)).1.1 = μ * (φ.symm x).1.1 := by
    intro x
    obtain ⟨w, rfl⟩ := φ.surjective x
    have hx : θa (φ w) = φ (torusCoord c w) := Subtype.ext (by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, d.Fu.coe_rootEquiv, d.Fu.coe_rootEquiv]
      exact torusElt_conj d.Fu c w)
    rw [hx, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    rfl
  have hvk' : (⟨v, hvN⟩ : Subgroup.normalizer (d.Fu.root : Set G)) ^ 2 ^ k = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hvk)
  set Pv : Subgroup (MulAut d.Fu.root) := (Subgroup.zpowers ⟨v, hvN⟩).map Ψ
  have hP : IsPGroup 2 Pv := (isPGroup_zpowers hvk').map Ψ
  have hPE : ∀ ψ ∈ Pv, ∀ x ∈ rootCenter d.Fu.J φ, ψ x = x := by
    rintro _ ⟨n, hn, rfl⟩ x hx
    obtain ⟨w, rfl⟩ := φ.surjective x
    rw [mem_rootCenter, MulEquiv.symm_apply_apply] at hx
    have hxQ : (φ w : G) ∈ minimalLocalFailurePairActionPointHull H z := by
      rw [d.Fu.coe_rootEquiv]
      exact (rootHom_mem_iff d.Fu w).mpr hx
    have hnQ := coe_mem_of_mem_zpowers (y := ⟨v, hvN⟩) hvQ hn
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
      ← Subgroup.mem_centralizer_iff.mp hnQ _ hxQ, mul_inv_cancel_right]
  have hPθ : ∀ ψ ∈ Pv, ψ * θa = θa * ψ := by
    rintro _ ⟨n, hn, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hnA := coe_mem_of_mem_zpowers (y := ⟨v, hvN⟩) hvA hn
    exact (Subgroup.mem_centralizer_iff.mp hnA _ hcA).symm
  have hψ : Ψ ⟨v, hvN⟩ ∈ Pv := ⟨⟨v, hvN⟩, Subgroup.mem_zpowers _, rfl⟩
  have key := root_two_subgroup_fst_eq d.Fu.J φ (2 ^ d.Fu.f) d.Fu.hcard d.Fu.hfixed θa hμ hc hθ
    Pv hP hPE hPθ _ hψ ⟨τ, hτ⟩
  set w₁ := φ.symm (Ψ ⟨v, hvN⟩ ⟨τ, hτ⟩)
  set w₂ := φ.symm ⟨τ, hτ⟩
  have h1 : v * τ * v⁻¹ = d.Fu.rootHom w₁ := by
    rw [← d.Fu.coe_rootEquiv, MulEquiv.apply_symm_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
  have h2 : τ = d.Fu.rootHom w₂ := by
    rw [← d.Fu.coe_rootEquiv, MulEquiv.apply_symm_apply]
  have h3 : v * τ * v⁻¹ * τ⁻¹ = d.Fu.rootHom (w₁ * w₂⁻¹) := by
    rw [map_mul, map_inv, ← h1, ← h2]
  rw [h3, rootHom_mem_iff, fst_mul, fst_inv, key, add_neg_cancel]

end ExclusionSetup

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
