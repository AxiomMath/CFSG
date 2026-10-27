module

public import CFSG.Sporadic.SuzRecog.LevelTwoCoverDefs
public import CFSG.Sporadic.SuzRecog.LevelTwoGroups
public import CFSG.Sporadic.SuzRecog.GluingProof2
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Monster.Code.Weights
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwoCover

open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Sporadic.SuzRecog.TitsTwo

variable {Γ : SimpleGraph (Fin 8991)} {T : Set (Fin 8991) → Prop} {ι κ : Type*}

section Base


theorem projX_mem_Xp {x : F} (hx : x • pt = pt) : projX x ∈ LevelTwo.Xp := by
  rw [mem_Xp, ← pr_pt, ← pr_smul, hx]

theorem projX_mem_Xq {x : F} (hx : x • qt = qt) : projX x ∈ LevelTwo.Xq := by
  rw [mem_Xq, ← pr_qt, ← pr_smul, hx]

theorem projX_mem_Xe {x : F}
    (hx : (x • pt = pt ∧ x • pt1 = pt1) ∨ (x • pt = pt1 ∧ x • pt1 = pt)) :
    projX x ∈ LevelTwo.Xe := by
  rw [mem_Xe, ← pr_pt, ← pr_pt1, ← pr_smul, ← pr_smul]
  rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨by rw [h0], by rw [h1]⟩
  · exact Or.inr ⟨by rw [h0], by rw [h1]⟩

end Base

section InvE


theorem proj_mem_invE (D : TitsDataTwo Γ T F ι κ) (hp : D.p = pt) :
    ∀ x ∈ D.Xp, ((proj x : Model.Crho1) : Equiv.Perm (Fin 1782)) ∈ invE 1 := by
  intro x hx
  have h := (D.hXp x).1 hx
  rw [hp] at h
  exact (mem_Xp_iff _).1 (projX_mem_Xp h)

theorem exists_proj_eq_of_mem_invE (D : TitsDataTwo Γ T F ι κ) (hp : D.p = pt) :
    ∀ y (hy : y ∈ Model.Crho1), y ∈ invE 1 → ∃ x ∈ D.Xp, proj x = ⟨y, hy⟩ := by
  intro y hy h1
  obtain ⟨h, hh, rfl⟩ := exists_mem_Xp hy h1
  have hfix : h • pr pt = pr pt := by
    rw [pr_pt]
    exact (mem_Xp h).1 hh
  obtain ⟨x, hx, hxp⟩ := exists_lift h hfix
  refine ⟨x, (D.hXp x).2 (by rw [hp]; exact hxp), Subtype.ext ?_⟩
  rw [coe_proj, ← coe_projX, hx]

theorem mem_B0Plus_of_mem_B0 {g : Equiv.Perm (Fin 1782)} (hg : g ∈ Model.B0)
    (hc : Commute g Model.rho1) : g ∈ B0Plus := by
  refine ⟨hg, ?_⟩
  have hN := (mem_normalizer_R0_iff g).1 (Subgroup.mem_inf.1 hg).2
  have hw : g * Model.w0 * g⁻¹ ∈ rhoTrip Model.w0 := by
    rw [← hN]
    exact ⟨Model.w0, Set.mem_insert _ _, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g * Model.w0 * g⁻¹ =
      Model.rho1 ^ k * Model.w0 * (Model.rho1 ^ k)⁻¹ := by
    simp only [rhoTrip, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with h | h | h
    · exact ⟨0, by rw [h]; group⟩
    · exact ⟨1, by rw [h]; group⟩
    · exact ⟨2, by rw [h, pow_two]; group⟩
  set h := (Model.rho1 ^ k)⁻¹ * g with hh
  have hρ : Commute h Model.rho1 := ((Commute.pow_left (Commute.refl _) k).inv_left).mul_left hc
  have hw0 : h * Model.w0 * h⁻¹ = Model.w0 := by
    calc h * Model.w0 * h⁻¹ = (Model.rho1 ^ k)⁻¹ * (g * Model.w0 * g⁻¹) * Model.rho1 ^ k := by
          rw [hh]; group
      _ = Model.w0 := by rw [hk]; group
  have hw1 : Commute h Model.w0 := by
    show h * Model.w0 = Model.w0 * h
    rw [← mul_inv_eq_iff_eq_mul, hw0]
  have hC : h ∈ Subgroup.centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) := by
    rw [Model.R0, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro s (rfl | rfl)
    · exact hw1.eq.symm
    · exact ((hρ.mul_right hw1).mul_right hρ.inv_right).eq.symm
  have e : g = h * Model.rho1 ^ k := by
    rw [hh, mul_assoc, (Commute.pow_right hc k).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e]
  exact Subgroup.mul_mem_sup hC (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)

theorem proj_mem_B0Plus (D : TitsDataTwo Γ T F ι κ) (hp : D.p = pt) (hq : D.q = qt) :
    ∀ x ∈ D.Xp, x ∈ D.Xq → ((proj x : Model.Crho1) : Equiv.Perm (Fin 1782)) ∈ B0Plus := by
  intro x hxp hxq
  have h1 := (D.hXp x).1 hxp
  have h2 := (D.hXq x).1 hxq
  rw [hp] at h1
  rw [hq] at h2
  have hB := (mem_Xp_inf_Xq_iff (projX x)).1 ⟨projX_mem_Xp h1, projX_mem_Xq h2⟩
  have hc : Commute ((projX x : xGroup) : Equiv.Perm (Fin 1782)) Model.rho1 :=
    Subgroup.mem_centralizer_singleton_iff.1 (xGroup_le_centralizer (projX x).2)
  exact mem_B0Plus_of_mem_B0 hB hc

end InvE

section NR0


theorem proj_mem_NR0 (D : TitsDataTwo Γ T F ι κ) (hq : D.q = qt) :
    ∀ x ∈ D.Xq, ((proj x : Model.Crho1) : Equiv.Perm (Fin 1782)) ∈ Model.NR0 := by
  intro x hx
  have h := (D.hXq x).1 hx
  rw [hq] at h
  exact (mem_Xq_iff _).1 (projX_mem_Xq h)

theorem exists_proj_eq_of_mem_NR0 (D : TitsDataTwo Γ T F ι κ) (hq : D.q = qt) :
    ∀ y (hy : y ∈ Model.Crho1), y ∈ Model.NR0 → ∃ x ∈ D.Xq, proj x = ⟨y, hy⟩ := by
  intro y hy hN
  obtain ⟨h, hh, rfl⟩ := exists_mem_Xq hy hN
  have hfix : h • pr qt = pr qt := by
    rw [pr_qt]
    exact (mem_Xq h).1 hh
  obtain ⟨x, hx, hxq⟩ := exists_lift h hfix
  refine ⟨x, (D.hXq x).2 (by rw [hq]; exact hxq), Subtype.ext ?_⟩
  rw [coe_proj, ← coe_projX, hx]

end NR0

section Edge


theorem proj_mem_centM (D : TitsDataTwo Γ T F ι κ) (hp : D.p = pt) (hp1 : D.p₁ = pt1) :
    ∀ x ∈ D.Xe, ((proj x : Model.Crho1) : Equiv.Perm (Fin 1782)) ∈ centM (suzInv 1 * aP p1) := by
  intro x hx
  have h := (D.hXe x).1 hx
  rw [hp, hp1] at h
  exact mem_centM_of_mem_Xe (projX_mem_Xe h)

end Edge

end CFSG.Sporadic.SuzRecog.LevelTwoCover
