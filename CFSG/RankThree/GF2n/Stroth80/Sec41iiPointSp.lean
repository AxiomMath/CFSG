module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorNat
public import CFSG.ClassicalGroups.Alternating.PointRadicalStabilizer
public import CFSG.ClassicalGroups.Alternating.PointRadicalCard
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

private theorem pointSp_card_Lsp {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) :
    Nat.card (CFSG.ClassicalGroups.Alternating.Lsp
      (CFSG.ClassicalGroups.Symplectic.spForm m K)
      (CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := m) (K := K)) u) =
      Nat.card K ^ (2 * m - 1) := by
  have hle := CFSG.ClassicalGroups.Alternating.pointRadical_le_bilinIsometryGroup
    (CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := m) (K := K)) u
  have h1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [CFSG.ClassicalGroups.Alternating.card_pointRadical
    (CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := m) (K := K))
    (CFSG.ClassicalGroups.Symplectic.spForm_nondegenerate (m := m) (K := K)) hu,
    CFSG.ClassicalGroups.Symplectic.finrank_spSpace] at h1
  exact h1

private theorem pointSp_card_le_isometry {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    (Q : Subgroup (CFSG.ClassicalGroups.Alternating.Gsp
      (CFSG.ClassicalGroups.Symplectic.spForm m K)))
    (hQS : Q ≤ CFSG.ClassicalGroups.Alternating.pointStabilizer
      (CFSG.ClassicalGroups.Symplectic.spForm m K) u)
    (hQn : ∀ x ∈ CFSG.ClassicalGroups.Alternating.pointStabilizer
      (CFSG.ClassicalGroups.Symplectic.spForm m K) u, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    (hQsq : ∀ y ∈ Q, y * y = 1) :
    Nat.card Q ≤ Nat.card K ^ (2 * m - 1) := by
  haveI : Finite (Module.End K (Fin m ⊕ Fin m → K)) :=
    Finite.of_injective _
      (DFunLike.coe_injective (F := (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)))
  haveI : Finite (LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :=
    Finite.of_injective _ Units.val_injective
  have hQp : IsPGroup 2 Q := by
    intro y
    exact ⟨1, Subtype.ext (by simpa [pow_two] using hQsq y.1 y.2)⟩
  have hQL : Q ≤ CFSG.ClassicalGroups.Alternating.Lsp
      (CFSG.ClassicalGroups.Symplectic.spForm m K)
      (CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := m) (K := K)) u := by
    rw [CFSG.ClassicalGroups.Alternating.Lsp_eq_pCoreOf_pointStabilizer
      (CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := m) (K := K))
      (CFSG.ClassicalGroups.Symplectic.spForm_nondegenerate (m := m) (K := K)) hu]
    exact CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hQS hQn hQp
  have hcard := Subgroup.card_le_of_le hQL
  rw [pointSp_card_Lsp hu] at hcard
  exact hcard

private theorem pointSp_card_le_fixed {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K))
    (hP : P ≤ CFSG.Open.StatedSp m K) (hP2 : ∀ p ∈ P, p * p = 1)
    (hPfix : ∀ p ∈ P, (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u)
    (hPnorm : ∀ g ∈ CFSG.Open.StatedSp m K,
      (∃ c : K, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ p ∈ P, g * p * g⁻¹ ∈ P) :
    Nat.card P ≤ Nat.card K ^ (2 * m - 1) := by
  have hcardP : Nat.card ↥((P.subgroupOf (CFSG.Open.StatedSp m K)).map
      (CFSG.ClassicalGroups.Symplectic.spEquiv (m := m) (K := K)).toMonoidHom) = Nat.card P :=
    (Subgroup.card_map_of_injective
      (f := (CFSG.ClassicalGroups.Symplectic.spEquiv (m := m) (K := K)).toMonoidHom)
      (CFSG.ClassicalGroups.Symplectic.spEquiv (m := m) (K := K)).injective).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv)
  rw [← hcardP]
  refine pointSp_card_le_isometry hu _ ?_ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    refine CFSG.ClassicalGroups.Alternating.mem_pointStabilizer.mpr ⟨1, ?_⟩
    rw [one_smul]
    exact (CFSG.ClassicalGroups.Symplectic.spEquiv_app s u).trans
      (hPfix _ (Subgroup.mem_subgroupOf.mp hs))
  · intro x hx y hy
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Alternating.mem_pointStabilizer.mp hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨g, rfl⟩ := (CFSG.ClassicalGroups.Symplectic.spEquiv (m := m) (K := K)).surjective x
    have hcg : ((g : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u :=
      (CFSG.ClassicalGroups.Symplectic.spEquiv_app g u).symm.trans hc
    have hmem := hPnorm (g : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K) g.2 ⟨c, hcg⟩
      (s : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K) (Subgroup.mem_subgroupOf.mp hs)
    refine Subgroup.mem_map.mpr ⟨g * s * g⁻¹, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    simp [map_mul, map_inv]
  · rintro _ ⟨s, hs, rfl⟩
    have hss : s * s = 1 := Subtype.ext (hP2 _ (Subgroup.mem_subgroupOf.mp hs))
    rw [← map_mul (CFSG.ClassicalGroups.Symplectic.spEquiv (m := m) (K := K)).toMonoidHom, hss,
      map_one]

theorem classicalPointSp : ClassicalPointSpStatement := by
  intro K instField instFinite instChar _hK m _hm u hu P hPX hP2 hPfix hPnorm
  have hcardV : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨?_, ?_⟩
  · rw [hcardV]
    exact pointSp_card_le_fixed hu P hPX hP2 hPfix hPnorm
  · intro h3
    exfalso
    rw [hcardV] at h3
    omega

end CFSG.RankThree.GF2n.Stroth80
