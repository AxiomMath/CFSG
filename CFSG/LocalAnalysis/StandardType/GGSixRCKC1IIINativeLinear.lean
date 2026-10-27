module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryRecognition
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSL
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSL
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.RCKRP CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieAdmissible StatedLieTag)


theorem false_of_row_III_of_native_linear_model
    {X : Type} [Group X] [Finite X] {p m f : ℕ} {K J : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdp : d ^ p = 1) (hf : 1 ≤ f)
    (φ : (ggU .PSL (m + 1) f).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSL (m + 1) f).K)
    (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hdID : GGPsiInnerDiag (ggU .PSL (m + 1) f).D φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, -, hsodd, e, he, J', hJe, hJmap⟩ :=
    rckF1_PSL hp hp2 hdp hf φ hφr hφk hdN hdID hJ
  have hrow' : GGSixRCKJRow .III (J'.map φ) := by rw [hJmap]; exact hrow
  let S : Set (GL (Fin (m + 1)) (GaloisField 2 f)) := {s}
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    have ha' : a = s := ha
    have hb' : b = s := hb
    rw [ha', hb']
  have hodd : ∀ a ∈ S, Odd (orderOf a) := by
    intro a ha
    have ha' : a = s := ha
    simpa only [ha'] using hsodd
  have hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2 := by
    by_contra hdeg
    have hFE := ggSixLSevenFieldExtCase_PSL m f hf φ hφk S hS hodd he hJe (by omega)
    exact not_fieldExtCase_of_row_III hrow' hf hFE
  obtain ⟨k, ι, -, -, -, -, -, -, hcent, hιrange, -⟩ :=
    exists_blockModel_PSL_rank m f S hS he hdeg hJe
  let ν : (ggU .PSL (k + 1) f).K →* X := φ.comp ι
  have hνr : ν.range = J'.map φ := by
    dsimp only [ν]
    rw [MonoidHom.range_comp, hιrange]
  have hνk : ν.ker ≤ Subgroup.center (ggU .PSL (k + 1) f).K := by
    intro y hy
    exact hcent y (hφk hy)
  let j : (ggU .PSL (k + 1) f).K →* GL (Fin (k + 1)) (GaloisField 2 f) :=
    SpecialLinearGroup.toGL
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun a : GL (Fin (k + 1)) (GaloisField 2 f) =>
      (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 f))) hxy)
  have : Finite (ggU .PSL (k + 1) f).K :=
    inferInstanceAs (Finite (SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)))
  have hk3 : 3 ≤ k + 1 := three_le_of_row_III_of_matrix_range j hj ν
    (by rw [hνr]) hrow'
  have hadm : StatedLieAdmissible .PSL (k + 1) 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_, ?_⟩
    all_goals intro hbad; have := (Prod.mk.inj hbad).1; omega
  have hmodel := irg_lieModel_quot (ht := Or.inl rfl) hadm ν hνr hνk
  rcases (lieModel_parameters_of_row_III hrow' hmodel).2 with ⟨hbad, -⟩ | ⟨hbad, -⟩ <;>
    cases hbad

theorem false_of_row_III_of_linear_modelID
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ b ∈ B, b ^ p = 1)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hdB : d ∈ B)
    (hmodel : RCKClassicalModelIDAt .PSL K B)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) : False := by
  obtain ⟨n, f, φ, hf, hφr, hφk, hdiag⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJr : J ≤ φ.range := by rw [hφr]; exact hJ.1.trans inf_le_left
  rcases n with _ | m
  · let j : (ggU .PSL 0 f).K →* GL (Fin 1) (ZMod 2) := SpecialLinearGroup.toGL
    have hj : Function.Injective j := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun a : GL (Fin 1) (ZMod 2) =>
        (a : Matrix (Fin 1) (Fin 1) (ZMod 2))) hxy)
    have : Finite (ggU .PSL 0 f).K :=
      inferInstanceAs (Finite (SpecialLinearGroup (Fin 1) (ZMod 2)))
    have hn : 3 ≤ 1 := three_le_of_row_III_of_matrix_range j hj φ hJr hrow
    omega
  · exact false_of_row_III_of_native_linear_model hp hp2 (hpow d hdB) hf
      φ hφr hφk (hBK hdB) (hdiag d hdB) hJ hrow

theorem ne_PSL_of_row_III_of_modelID
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B : Subgroup X} {t : StatedLieTag}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ b ∈ B, b ^ p = 1)
    (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hJd : ∃ d ∈ B, IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hmodel : RCKClassicalModelIDAt t K B) : t ≠ .PSL := by
  intro ht
  subst t
  obtain ⟨d, hdB, hJ⟩ := hJd
  exact false_of_row_III_of_linear_modelID hp hp2 hpow hBK hdB hmodel hJ hrow

end CFSG.StandardType.RCKC1
