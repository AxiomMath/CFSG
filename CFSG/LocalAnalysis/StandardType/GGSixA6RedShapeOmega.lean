module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeOrthMat
public import CFSG.LieType.BorelTits.OrthogonalForm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBBlock

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

open scoped Matrix

private theorem conj_mem_statedOmega_of_mem_orthGroup {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Q : (ι → F) → F) {u : GL ι F} (hu : u ∈ orthGroup Q)
    {s : GL ι F} (hs : s ∈ StatedOmega Q) : u * s * u⁻¹ ∈ StatedOmega Q := by
  have hnorm : orthGroup Q ≤ Subgroup.normalizer (StatedOmega Q : Set (GL ι F)) := by
    rw [Subgroup.closure_le]
    intro Y hY
    change Y ∈ Subgroup.normalizer (StatedOmega Q : Set (GL ι F))
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact CFSG.ComponentClassification.HarrisLit.T1.P54.DB.conj_mem_statedOmega
        (CFSG.ComponentClassification.HarrisLit.T1.P54.DB.mem_isoGroup.mpr hY) hh
    · intro hh
      have hY' : ∀ w : ι → F, Q (((Y⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ w) = Q w := by
        intro w
        have h1 := hY (((Y⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ w)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec] at h1
        exact h1.symm
      have h2 := CFSG.ComponentClassification.HarrisLit.T1.P54.DB.conj_mem_statedOmega
        (CFSG.ComponentClassification.HarrisLit.T1.P54.DB.mem_isoGroup.mpr hY') hh
      have h3 : Y⁻¹ * (Y * h * Y⁻¹) * (Y⁻¹)⁻¹ = h := by group
      rwa [h3] at h2
  have hN := hnorm hu
  exact (Subgroup.mem_normalizer_iff.mp hN s).mp hs

theorem ggA6_shape_Omega {F : Type} [Field F] [Finite F] [CharP F 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Φ : QuadForm F (ι → F))
    (P : Subgroup (GL ι F)) (hPO : P ≤ orthGroup Φ.Q) (hP : Odd (Nat.card P))
    (hPn : Group.IsNilpotent ↥P) (J : Subgroup (GL ι F))
    (hJ : IsComponentOf J (CFSG.Open.StatedOmega Φ.Q ⊓
      Subgroup.centralizer (P : Set (GL ι F)))) : GGA6CharTwoLie J := by
  obtain ⟨hJle, hJsub, hJq⟩ := hJ
  have hle : CFSG.Open.StatedOmega Φ.Q ⊓ Subgroup.centralizer (P : Set (GL ι F)) ≤
      orthGroup Φ.Q ⊓ Subgroup.centralizer (P : Set (GL ι F)) :=
    inf_le_inf (statedOmega_le_orthGroup Φ.Q) le_rfl
  have hnormal : IsSubnormal (CFSG.Open.StatedOmega Φ.Q ⊓
      Subgroup.centralizer (P : Set (GL ι F)))
      (orthGroup Φ.Q ⊓ Subgroup.centralizer (P : Set (GL ι F))) := by
    refine CFSG.StandardType.LayerCores.ggSubnormal_of_normal hle ?_
    intro u hu s hs
    obtain ⟨huO, huC⟩ := Subgroup.mem_inf.mp hu
    obtain ⟨hsΩ, hsC⟩ := Subgroup.mem_inf.mp hs
    refine Subgroup.mem_inf.mpr ⟨conj_mem_statedOmega_of_mem_orthGroup Φ.Q huO hsΩ, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at huC hsC ⊢
    intro p hp
    have hu'inv : p * u⁻¹ = u⁻¹ * p :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ huC) p hp
    calc p * (u * s * u⁻¹) = (p * u) * s * u⁻¹ := by group
      _ = (u * p) * s * u⁻¹ := by rw [huC p hp]
      _ = u * (p * s) * u⁻¹ := by group
      _ = u * (s * p) * u⁻¹ := by rw [hsC p hp]
      _ = u * s * (p * u⁻¹) := by group
      _ = u * s * (u⁻¹ * p) := by rw [hu'inv]
      _ = (u * s * u⁻¹) * p := by group
  exact ggA6_shape_orthCentralizer Φ P hPO hP hPn J hJq (hJsub.trans hnormal)

end CFSG.StandardType.A6Red
