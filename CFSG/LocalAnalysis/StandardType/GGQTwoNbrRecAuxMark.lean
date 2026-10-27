module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeA
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G]

theorem qTwoNbrRec_hasLabel_of_lieModel {R : Type} [Group R] {d : ℕ} (hd : 5 ≤ d)
    (hR : LieModel R .PSU d 2 1) : GGHasLabel (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) R := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨K, hf, hfin, hcard, ⟨e⟩⟩ := qTwoLMPrimeA_marking (m := d' + 1) (by omega) hR
  exact ⟨K, hf, hfin, hcard, ⟨e⟩⟩

private theorem qTwoNbrRec_mark_label_eq {lab : LargeEvenLabel} {d : ℕ} (hd : 5 ≤ d)
    (hrow : ggRowP_ESU 3 lab) (hiso : GGLabelIso lab (⟨.twA, d - 1, 1⟩ : LargeEvenLabel)) :
    lab = ⟨.twA, d - 1, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h <;> simp_all

theorem qTwoNbrRec_marking
    {Bs K : Subgroup G} {d : ℕ} (hd : 5 ≤ d) (hmark : GGInnerDiagOnLabel ggRowP_ESU 3 Bs K)
    (hK : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU d 2 1) :
    GGInnerDiagOnLabel (fun _ lab' => lab' = (⟨.twA, d - 1, 1⟩ : LargeEvenLabel)) 3 Bs K := by
  refine GGInnerDiagOnLabel.mono_label_of_hasLabel (T := fun _ lab' =>
    lab' = (⟨.twA, d - 1, 1⟩ : LargeEvenLabel)) ?_ hmark
  intro lab hlab hhas hrow
  have hlab' : LargeEvenInLambda2 (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) := by
    refine ⟨by norm_num, ?_⟩
    dsimp only
    exact ⟨by omega, by intro h; omega⟩
  have hhas' : GGHasLabel (⟨.twA, d - 1, 1⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K) := qTwoNbrRec_hasLabel_of_lieModel hd hK
  exact qTwoNbrRec_mark_label_eq hd hrow
    (ggLabelRigidInput_holds lab ⟨.twA, d - 1, 1⟩ (↥K ⧸ Subgroup.center ↥K)
      hlab hlab' hhas hhas')

theorem qTwoNbrRec_unpack {Bs K : Subgroup G} {d : ℕ} (hd : 5 ≤ d)
    (h : GGInnerDiagOnLabel (fun _ lab' => lab' = (⟨.twA, d - 1, 1⟩ : LargeEvenLabel)) 3 Bs K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ 1))),
      Nat.card F = (2 ^ 1) ^ 2 ∧ commutator ↥K = ⊤ ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ 1)))
          (LargeEvenGUSet (Fin d) F (2 ^ 1)),
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  have h3 : GGInnerDiagOnLabel
      (fun p lab' => lab' = (⟨.twA, d - 1, 1⟩ : LargeEvenLabel) ∧ p = 3) 3 Bs K :=
    GGInnerDiagOnLabel.mono_label
      (S := fun _ lab' => lab' = (⟨.twA, d - 1, 1⟩ : LargeEvenLabel))
      (fun _ h => ⟨h, rfl⟩) h
  obtain ⟨F, hf, hfin, lab, m, θ, hKcard, h4m, hmrank, hPlab, hpdiv, hperf, hlabΛ, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore h3 (fun p lab hP => by
      obtain ⟨rfl, rfl⟩ := hP
      refine ⟨Or.inl ⟨rfl, ?_⟩, by norm_num⟩
      dsimp only
      omega)
  obtain ⟨rfl, -⟩ := hPlab
  have hmrank' : m = d := by
    have h : m = (d - 1) + 1 := by simpa using hmrank
    rw [h]
    omega
  clear hmrank
  subst m
  exact ⟨F, hf, hfin, θ, hKcard, hperf, hBsN, hbs⟩

end CFSG.StandardType.QTwo

end
