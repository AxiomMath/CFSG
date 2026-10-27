module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerBlock
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.SectionRank.OddCover CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
  CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n d : ℕ}

theorem mk_mem_ggFix_of_mem_cenSU {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {s : ↥(unitarySU 2 n K d)} (hs : s ∈ cenSU (n := n) D) :
    LargeEvenProjMk (unitarySU 2 n K d) s ∈
      ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩) := by
  rw [mem_ggFix, projConj_mk_coe]
  congr 1
  apply Subtype.ext
  show D * (s : GL (Fin d) K) * D⁻¹ = s
  rw [mem_cenSU] at hs
  rw [← hs, mul_inv_cancel_right]

theorem exists_conj_eq_scalar_mul {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {s : ↥(unitarySU 2 n K d)}
    (hs : LargeEvenProjMk (unitarySU 2 n K d) s ∈
      ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩)) :
    ∃ c : Kˣ, D * (s : GL (Fin d) K) * D⁻¹ = GeneralLinearGroup.scalar (Fin d) c * s := by
  rw [mem_ggFix, projConj_mk_coe] at hs
  obtain ⟨c, hc⟩ := exists_scalar_of_mk_eq hs
  refine ⟨c⁻¹, ?_⟩
  have hc' : (s : GL (Fin d) K) = (D * s * D⁻¹) * GeneralLinearGroup.scalar (Fin d) c := by
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv]
    show (s : GL (Fin d) K) = (D * s * D⁻¹) * ((D * s * D⁻¹)⁻¹ * s)
    group
  calc D * (s : GL (Fin d) K) * D⁻¹ =
      (D * s * D⁻¹) * GeneralLinearGroup.scalar (Fin d) c *
        (GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by group
    _ = (s : GL (Fin d) K) * (GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by rw [← hc']
    _ = GeneralLinearGroup.scalar (Fin d) c⁻¹ * s := by
        rw [← map_inv]
        exact (commute_scalar c⁻¹ (s : GL (Fin d) K)).eq

theorem conj_mem_cenSU {D : GL (Fin d) K} {s t : ↥(unitarySU 2 n K d)} {c : Kˣ}
    (hs : D * (s : GL (Fin d) K) * D⁻¹ = GeneralLinearGroup.scalar (Fin d) c * s)
    (ht : t ∈ cenSU (n := n) D) : s * t * s⁻¹ ∈ cenSU (n := n) D := by
  rw [mem_cenSU] at ht ⊢
  have hz : ∀ g : GL (Fin d) K, g * GeneralLinearGroup.scalar (Fin d) c =
      GeneralLinearGroup.scalar (Fin d) c * g := fun g => (commute_scalar c g).eq
  have ht' : D * (t : GL (Fin d) K) * D⁻¹ = t := by rw [← ht, mul_inv_cancel_right]
  have e : D * ((s * t * s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * D⁻¹ =
      (D * (s : GL (Fin d) K) * D⁻¹) * (D * (t : GL (Fin d) K) * D⁻¹) *
        (D * (s : GL (Fin d) K) * D⁻¹)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hs, ht'] at e
  have e2 : GeneralLinearGroup.scalar (Fin d) c * (s : GL (Fin d) K) * (t : GL (Fin d) K) *
      (GeneralLinearGroup.scalar (Fin d) c * (s : GL (Fin d) K))⁻¹ =
      ((s * t * s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) := by
    have h1 := hz ((s : GL (Fin d) K) * t * (s : GL (Fin d) K)⁻¹)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc GeneralLinearGroup.scalar (Fin d) c * (s : GL (Fin d) K) * (t : GL (Fin d) K) *
          (GeneralLinearGroup.scalar (Fin d) c * (s : GL (Fin d) K))⁻¹ =
        GeneralLinearGroup.scalar (Fin d) c * ((s : GL (Fin d) K) * t * (s : GL (Fin d) K)⁻¹) *
          (GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by group
      _ = ((s : GL (Fin d) K) * t * (s : GL (Fin d) K)⁻¹) *
          GeneralLinearGroup.scalar (Fin d) c * (GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
          rw [← h1]
      _ = (s : GL (Fin d) K) * t * (s : GL (Fin d) K)⁻¹ := by group
  rw [e2] at e
  set X : GL (Fin d) K := ((s * t * s⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) with hX
  calc X * D = (D * X * D⁻¹) * D := by rw [e]
    _ = D * X := by group

variable (hKd : UnitaryFieldData 2 n K)

include hKd in
theorem isComponentOf_map_blockSU_of_level (hn : 2 ≤ n) {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {τ : Fin d → Kˣ} (hDτ : D = diagHom d τ) {v : Kˣ} {S : Finset (Fin d)}
    (hS : ∀ i, i ∈ S ↔ τ i = v) (hS2 : 2 ≤ S.card) :
    IsComponentOf ((blockSU (n := n) S).map (LargeEvenProjMk (unitarySU 2 n K d)))
      (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩)) := by
  classical
  subst hDτ
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  set C := ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩) with hC
  have hτS : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j := fun i hi j hj => by
    rw [(hS i).mp hi, (hS j).mp hj]
  have hNC : (blockSU (n := n) S).map π ≤ (cenSU (n := n) (diagHom d τ)).map π :=
    Subgroup.map_mono (blockSU_le_cenSU hτS)
  have hCC : (cenSU (n := n) (diagHom d τ)).map π ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    exact mk_mem_ggFix_of_mem_cenSU hD hs
  have hN : (((blockSU (n := n) S).map π).subgroupOf
      ((cenSU (n := n) (diagHom d τ)).map π)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨s, hs, hsg⟩ := g.2
    refine ⟨s * t * s⁻¹, conj_mem_blockSU_of_commute hS (mem_cenSU.mp hs) ht, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hsg, htx]
  have hC' : ((cenSU (n := n) (diagHom d τ)).map π).subgroupOf C |>.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨s, hsg⟩ := QuotientGroup.mk_surjective (g : LargeEvenProj (unitarySU 2 n K d))
    have hgC : (g : LargeEvenProj (unitarySU 2 n K d)) ∈ C := g.2
    rw [← hsg] at hgC
    obtain ⟨c, hs⟩ := exists_conj_eq_scalar_mul hD hgC
    have hπs : π s = (g : LargeEvenProj (unitarySU 2 n K d)) := hsg
    refine ⟨s * t * s⁻¹, conj_mem_cenSU hs ht, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hπs, htx]
  refine ⟨hNC.trans hCC, ?_, ?_⟩
  · exact IsSubnormal.step hNC hN (IsSubnormal.step hCC hC' (IsSubnormal.refl C))
  · exact SURepair.isQuasisimple_map_blockSU_of_two_le hKd hn ker_projMk_le_center hS2

include hKd in
theorem not_isComponentOf_layer_ggFix_diag (hn : 2 ≤ n) {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {τ : Fin d → Kˣ} (hDτ : D = diagHom d τ) {v₁ v₂ : Kˣ} (hv : v₁ ≠ v₂)
    {S₁ S₂ : Finset (Fin d)} (hS₁ : ∀ i, i ∈ S₁ ↔ τ i = v₁) (hS₂ : ∀ i, i ∈ S₂ ↔ τ i = v₂)
    (h₁ : 2 ≤ S₁.card) (h₂ : 2 ≤ S₂.card) :
    ¬ IsComponentOf (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩)) := by
  refine not_isComponentOf_layer_of_commuting
    (isComponentOf_map_blockSU_of_level hKd hn hD hDτ hS₁ h₁)
    (isComponentOf_map_blockSU_of_level hKd hn hD hDτ hS₂ h₂) ?_
  rintro _ ⟨t₁, ht₁, rfl⟩ _ ⟨t₂, ht₂, rfl⟩
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact hv (((hS₁ i).mp hi1).symm.trans ((hS₂ i).mp hi2))
  rw [← map_mul, ← map_mul, blockSU_commute_of_disjoint hdisj ht₁ ht₂]

end CFSG.StandardType.Line63.H5

end
