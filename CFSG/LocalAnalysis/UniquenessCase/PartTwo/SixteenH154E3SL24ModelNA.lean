module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Model
public import CFSG.Quasithin.Background.HStandard
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix
open scoped CFSG.Decide.Bounded

@[expose] def s16h_orth3ActM (A : Matrix (Fin 2) (Fin 2) GF4) (v : GF4 × GF4 × GF4) :
    GF4 × GF4 × GF4 :=
  (A 0 0 * v.1 + A 0 1 * v.2.1, A 1 0 * v.1 + A 1 1 * v.2.1,
   v.2.2 + (A 0 0 * A 1 0) ^ 2 * v.1 + (A 0 1 * A 1 1) ^ 2 * v.2.1)

def s16h_sl2Set : Finset (Matrix (Fin 2) (Fin 2) GF4) :=
  Finset.univ.filter (fun A => A.det = 1)

theorem s16h_mem_sl2Set {A : Matrix (Fin 2) (Fin 2) GF4} :
    A ∈ s16h_sl2Set ↔ A.det = 1 := by
  simp [s16h_sl2Set]

theorem s16h_orth3Act_eq (γ : Matrix.GeneralLinearGroup (Fin 2) GF4)
    (v : GF4 × GF4 × GF4) :
    orth3Act γ v = s16h_orth3ActM (γ : Matrix (Fin 2) (Fin 2) GF4) v := rfl

theorem s16h_orth3ActM_one (v : GF4 × GF4 × GF4) :
    s16h_orth3ActM 1 v = v := by
  ext <;> simp [s16h_orth3ActM]

theorem s16h_orth3ActM_add (A : Matrix (Fin 2) (Fin 2) GF4) (v w : GF4 × GF4 × GF4) :
    s16h_orth3ActM A (v + w) = s16h_orth3ActM A v + s16h_orth3ActM A w := by
  haveI : CharP GF4 2 := CharTwo.of_one_ne_zero_of_two_eq_zero (by decide) (by decide)
  ext <;> simp only [s16h_orth3ActM, Prod.fst_add, Prod.snd_add] <;> ring_nf

theorem s16h_orth3ActM_smul (A : Matrix (Fin 2) (Fin 2) GF4) (c : GF4)
    (v : GF4 × GF4 × GF4) :
    s16h_orth3ActM A (c • v) = c • s16h_orth3ActM A v := by
  ext <;> simp only [s16h_orth3ActM, Prod.smul_fst, Prod.smul_snd] <;> ring

theorem s16h_orth3ActM_mul_basis : ∀ A ∈ s16h_sl2Set, ∀ B ∈ s16h_sl2Set,
    s16h_orth3ActM (A * B) (1, 0, 0) = s16h_orth3ActM A (s16h_orth3ActM B (1, 0, 0)) ∧
    s16h_orth3ActM (A * B) (0, 1, 0) = s16h_orth3ActM A (s16h_orth3ActM B (0, 1, 0)) ∧
    s16h_orth3ActM (A * B) (0, 0, 1) = s16h_orth3ActM A (s16h_orth3ActM B (0, 0, 1)) := by
  decide +kernel

theorem s16h_orth3ActM_mul (A B : Matrix (Fin 2) (Fin 2) GF4) (hA : A ∈ s16h_sl2Set)
    (hB : B ∈ s16h_sl2Set) (v : GF4 × GF4 × GF4) :
    s16h_orth3ActM (A * B) v = s16h_orth3ActM A (s16h_orth3ActM B v) := by
  obtain ⟨h1, h2, h3⟩ := s16h_orth3ActM_mul_basis A hA B hB
  have hdecomp : ∀ u : GF4 × GF4 × GF4,
      u = u.1 • ((1, 0, 0) : GF4 × GF4 × GF4) +
        u.2.1 • ((0, 1, 0) : GF4 × GF4 × GF4) +
        u.2.2 • ((0, 0, 1) : GF4 × GF4 × GF4) := fun u => by ext <;> simp
  have hBv : s16h_orth3ActM B v =
      v.1 • s16h_orth3ActM B (1, 0, 0) + v.2.1 • s16h_orth3ActM B (0, 1, 0) +
        v.2.2 • s16h_orth3ActM B (0, 0, 1) := by
    conv_lhs => rw [hdecomp v]
    rw [s16h_orth3ActM_add, s16h_orth3ActM_add, s16h_orth3ActM_smul, s16h_orth3ActM_smul,
      s16h_orth3ActM_smul]
  rw [hBv]
  conv_lhs => rw [hdecomp v]
  rw [s16h_orth3ActM_add, s16h_orth3ActM_add, s16h_orth3ActM_smul, s16h_orth3ActM_smul,
    s16h_orth3ActM_smul]
  rw [s16h_orth3ActM_add, s16h_orth3ActM_add, s16h_orth3ActM_smul, s16h_orth3ActM_smul,
    s16h_orth3ActM_smul, h1, h2, h3]

theorem s16h_orth3ActM_fix (A : Matrix (Fin 2) (Fin 2) GF4) (v : GF4 × GF4 × GF4)
    (h1 : v.1 = 0) (h2 : v.2.1 = 0) : s16h_orth3ActM A v = v := by
  ext <;> simp [s16h_orth3ActM, h1, h2]

theorem s16h_det_mem_statedSL (γ : ↥(StatedSL 2 GF4)) :
    (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL γ.2

@[expose] def s16h_orth3Aut (γ : ↥(StatedSL 2 GF4)) : MulAut Orth3 where
  toFun v := Multiplicative.ofAdd (s16h_orth3ActM
    ((γ : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4)
    (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (s16h_orth3ActM
    (((γ⁻¹ : ↥(StatedSL 2 GF4)) : Matrix.GeneralLinearGroup (Fin 2) GF4) :
      Matrix (Fin 2) (Fin 2) GF4) (Multiplicative.toAdd v))
  left_inv v := by
    have hmul := s16h_orth3ActM_mul
      (((γ⁻¹ : ↥(StatedSL 2 GF4)) : Matrix.GeneralLinearGroup (Fin 2) GF4) :
        Matrix (Fin 2) (Fin 2) GF4)
      (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4)
      (s16h_mem_sl2Set.mpr (s16h_det_mem_statedSL γ⁻¹))
      (s16h_mem_sl2Set.mpr (s16h_det_mem_statedSL γ)) (Multiplicative.toAdd v)
    show Multiplicative.ofAdd (s16h_orth3ActM _
        (s16h_orth3ActM _ (Multiplicative.toAdd v))) = v
    rw [← hmul]
    have hcoe : ((((γ⁻¹ : ↥(StatedSL 2 GF4)) : Matrix.GeneralLinearGroup (Fin 2) GF4)) :
        Matrix (Fin 2) (Fin 2) GF4) * (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) :
        Matrix (Fin 2) (Fin 2) GF4) = 1 := by
      have h := congrArg (fun δ : ↥(StatedSL 2 GF4) =>
        ((δ : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4))
        (inv_mul_cancel γ)
      simpa using h
    rw [hcoe, s16h_orth3ActM_one]
    exact ofAdd_toAdd v
  right_inv v := by
    have hmul := s16h_orth3ActM_mul
      (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4)
      (((γ⁻¹ : ↥(StatedSL 2 GF4)) : Matrix.GeneralLinearGroup (Fin 2) GF4) :
        Matrix (Fin 2) (Fin 2) GF4)
      (s16h_mem_sl2Set.mpr (s16h_det_mem_statedSL γ))
      (s16h_mem_sl2Set.mpr (s16h_det_mem_statedSL γ⁻¹)) (Multiplicative.toAdd v)
    show Multiplicative.ofAdd (s16h_orth3ActM _
        (s16h_orth3ActM _ (Multiplicative.toAdd v))) = v
    rw [← hmul]
    have hcoe : (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) :
        Matrix (Fin 2) (Fin 2) GF4) * ((((γ⁻¹ : ↥(StatedSL 2 GF4)) :
        Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4) = 1 := by
      have h := congrArg (fun δ : ↥(StatedSL 2 GF4) =>
        ((δ : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4))
        (mul_inv_cancel γ)
      simpa using h
    rw [hcoe, s16h_orth3ActM_one]
    exact ofAdd_toAdd v
  map_mul' a b := by
    show Multiplicative.ofAdd (s16h_orth3ActM _ (Multiplicative.toAdd (a * b))) =
      Multiplicative.ofAdd (s16h_orth3ActM _ (Multiplicative.toAdd a)) *
        Multiplicative.ofAdd (s16h_orth3ActM _ (Multiplicative.toAdd b))
    rw [toAdd_mul, s16h_orth3ActM_add, ofAdd_add]

theorem s16h_orth3Aut_eq_orth3Act (γ : ↥(StatedSL 2 GF4)) (v : Orth3) :
    s16h_orth3Aut γ v = Multiplicative.ofAdd
      (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (Multiplicative.toAdd v)) := by
  show Multiplicative.ofAdd (s16h_orth3ActM _ _) = _
  rw [← s16h_orth3Act_eq]

theorem s16h_orth3Aut_mul (γ δ : ↥(StatedSL 2 GF4)) :
    s16h_orth3Aut (γ * δ) = s16h_orth3Aut γ * s16h_orth3Aut δ := by
  apply MulEquiv.ext
  intro v
  have hmul := s16h_orth3ActM_mul
    (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4)
    (((δ : Matrix.GeneralLinearGroup (Fin 2) GF4)) : Matrix (Fin 2) (Fin 2) GF4)
    (s16h_mem_sl2Set.mpr (s16h_det_mem_statedSL γ))
    (s16h_mem_sl2Set.mpr (s16h_det_mem_statedSL δ)) (Multiplicative.toAdd v)
  show Multiplicative.ofAdd (s16h_orth3ActM
      (((γ * δ : ↥(StatedSL 2 GF4)) : Matrix.GeneralLinearGroup (Fin 2) GF4) :
        Matrix (Fin 2) (Fin 2) GF4) (Multiplicative.toAdd v)) =
    Multiplicative.ofAdd (s16h_orth3ActM _
      (s16h_orth3ActM _ (Multiplicative.toAdd v)))
  rw [← hmul]
  congr 1

theorem s16h_orth3Aut_fix_Z (γ : ↥(StatedSL 2 GF4)) {z : Orth3} (hz : z ∈ orth3Z) :
    s16h_orth3Aut γ z = z := by
  obtain ⟨h1, h2⟩ := hz
  show Multiplicative.ofAdd (s16h_orth3ActM _ (Multiplicative.toAdd z)) = z
  rw [s16h_orth3ActM_fix _ _ h1 h2, ofAdd_toAdd]

theorem s16h_orth3Scal_comm (μ : GF4) (hμ : μ ≠ 0) (γ : ↥(StatedSL 2 GF4)) :
    orth3Scal μ hμ * s16h_orth3Aut γ = s16h_orth3Aut γ * orth3Scal μ hμ := by
  apply MulEquiv.ext
  intro v
  show orth3Scal μ hμ (s16h_orth3Aut γ v) = s16h_orth3Aut γ (orth3Scal μ hμ v)
  rw [s16h_orth3Aut_eq_orth3Act, s16h_orth3Act_eq]
  conv_rhs => rw [s16h_orth3Aut_eq_orth3Act, s16h_orth3Act_eq]
  rw [show orth3Scal μ hμ (Multiplicative.ofAdd
      (s16h_orth3ActM _ (Multiplicative.toAdd v))) =
      Multiplicative.ofAdd (μ • s16h_orth3ActM _ (Multiplicative.toAdd v)) from rfl]
  rw [show orth3Scal μ hμ v = Multiplicative.ofAdd (μ • Multiplicative.toAdd v) from rfl]
  rw [toAdd_ofAdd, s16h_orth3ActM_smul]

@[expose] def s16h_orth3AutHom : ↥(StatedSL 2 GF4) →* MulAut Orth3 where
  toFun := s16h_orth3Aut
  map_one' := by
    apply MulEquiv.ext
    intro v
    show Multiplicative.ofAdd (s16h_orth3ActM
      (((1 : ↥(StatedSL 2 GF4)) : Matrix.GeneralLinearGroup (Fin 2) GF4) :
        Matrix (Fin 2) (Fin 2) GF4) (Multiplicative.toAdd v)) = v
    rw [show (((1 : ↥(StatedSL 2 GF4)) : Matrix.GeneralLinearGroup (Fin 2) GF4) :
      Matrix (Fin 2) (Fin 2) GF4) = 1 from rfl, s16h_orth3ActM_one, ofAdd_toAdd]
  map_mul' := s16h_orth3Aut_mul

theorem s16h_orth3AutHom_apply (γ : ↥(StatedSL 2 GF4)) (v : Orth3) :
    s16h_orth3AutHom γ v = Multiplicative.ofAdd
      (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (Multiplicative.toAdd v)) := by
  show s16h_orth3Aut γ v = _
  rw [s16h_orth3Aut_eq_orth3Act]

theorem s16h_orth3L_eq_range : orth3L = s16h_orth3AutHom.range := by
  rw [orth3L]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro σ ⟨γ, hγ, hσ⟩
    refine ⟨⟨γ, hγ⟩, ?_⟩
    apply MulEquiv.ext
    intro v
    rw [s16h_orth3AutHom_apply, hσ]
  · rintro x ⟨γ, rfl⟩
    exact Subgroup.subset_closure
      ⟨(γ : Matrix.GeneralLinearGroup (Fin 2) GF4), γ.2, fun v => by
        rw [s16h_orth3AutHom_apply]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
