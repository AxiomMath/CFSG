module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatCentMove.Transport
public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.SpecialLinear.Transitive
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatCentMove

open CFSG.Open Matrix

variable {K : Type} [Field K]

open CFSG.ClassicalGroups.SpecialLinear CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.Alternating

theorem exists_dotProduct_eq_zero_eq_one {ι : Type} [Fintype ι] {e u : ι → K} (he : e ≠ 0)
    (hu : ∀ c : K, u ≠ c • e) :
    ∃ φ : ι → K, φ ⬝ᵥ u = 0 ∧ φ ⬝ᵥ e = 1 := by
  classical
  have hmem : e ∉ Submodule.span K ({u} : Set (ι → K)) := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_smul] at hc
      exact he hc.symm
    · refine hu c⁻¹ ?_
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨f, hfe, hfu⟩ := Submodule.exists_le_ker_of_notMem hmem
  have hfu' : f u = 0 := by
    simpa using hfu (Submodule.subset_span (Set.mem_singleton u))
  refine ⟨(f e)⁻¹ • (dotProductEquiv K ι).symm f, ?_, ?_⟩
  · rw [smul_dotProduct, ← dotProductEquiv_apply_apply K ι ((dotProductEquiv K ι).symm f) u,
      LinearEquiv.apply_symm_apply, hfu', smul_zero]
  · rw [smul_dotProduct, ← dotProductEquiv_apply_apply K ι ((dotProductEquiv K ι).symm f) e,
      LinearEquiv.apply_symm_apply, smul_eq_mul, inv_mul_cancel₀ hfe]

theorem centMove_statedSL {d : ℕ} {e : Fin d → K} (he : e ≠ 0) : CentMove (StatedSL d K) e := by
  classical
  intro u hu
  obtain ⟨φ, hφu, hφe⟩ := exists_dotProduct_eq_zero_eq_one he hu
  let f : Module.Dual K (Fin d → K) :=
    { toFun := fun z => φ ⬝ᵥ z
      map_add' := fun a b => dotProduct_add φ a b
      map_smul' := fun c a => dotProduct_smul c φ a }
  have hfu : f u = 0 := hφu
  obtain ⟨A, hA, hAz⟩ := exists_statedSL_mulVec_eq_transvection (v := u) f hfu
  refine ⟨A, hA, ?_, ?_⟩
  · rw [hAz, hfu, zero_smul, add_zero]
  · intro c hc
    have heu : (A : Matrix (Fin d) (Fin d) K) *ᵥ e = e + u := by
      rw [hAz]
      change e + (φ ⬝ᵥ e) • u = e + u
      rw [hφe, one_smul]
    rw [heu] at hc
    have h1 : u = c • e - e := by
      rw [← hc]
      abel
    have h2 : c • e - e = (c - 1) • e := by
      rw [sub_smul c 1, one_smul]
    exact hu (c - 1) (h1.trans h2)

theorem centMove_statedSp (m : ℕ) {e : Fin m ⊕ Fin m → K} (he : e ≠ 0) :
    CentMove (StatedSp m K) e := by
  classical
  intro u hu
  obtain ⟨φ, hφu, hφe⟩ := exists_dotProduct_eq_zero_eq_one he hu
  let a : Fin m ⊕ Fin m → K := -(spJ m K *ᵥ φ)
  have hspJa : spJ m K *ᵥ a = φ := by
    change spJ m K *ᵥ (-(spJ m K *ᵥ φ)) = φ
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, spJ_mul_spJ, Matrix.neg_mulVec,
      Matrix.one_mulVec, neg_neg]
  have hφa : ∀ x : Fin m ⊕ Fin m → K, spForm m K x a = φ ⬝ᵥ x := by
    intro x
    rw [spForm_apply, hspJa, dotProduct_comm]
  have hBu : spForm m K u a = 0 := by rw [hφa, hφu]
  have hBe : spForm m K e a = 1 := by rw [hφa, hφe]
  let T : Gsp (spForm m K) := Tsp spForm_isAlt a 1
  let A : StatedSp m K := (spEquiv (m := m) (K := K)).symm T
  have hA : spEquiv A = T := MulEquiv.apply_symm_apply _ _
  have hAu : ((A : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u := by
    have h := spEquiv_app A u
    rw [hA, Tsp_app, hBu, mul_zero, zero_smul, add_zero] at h
    exact h.symm
  have hAe : ((A : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e = e + a := by
    have h := spEquiv_app A e
    rw [hA, Tsp_app, hBe, mul_one, one_smul] at h
    exact h.symm
  refine ⟨A, A.2, hAu, ?_⟩
  intro c hc
  rw [hAe] at hc
  have ha : a = (c - 1) • e := by
    have h1 : a = c • e - e := by
      rw [← hc]
      abel
    have h2 : c • e - e = (c - 1) • e := by
      rw [sub_smul c 1, one_smul]
    exact h1.trans h2
  have h0 : spForm m K e a = 0 := by
    rw [ha, LinearMap.BilinForm.smul_right, spForm_self, mul_zero]
  rw [hBe] at h0
  exact one_ne_zero h0

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatCentMove
