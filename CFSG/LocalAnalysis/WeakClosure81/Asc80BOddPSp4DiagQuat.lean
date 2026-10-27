module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpOuter
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpDiagInv
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpDiag

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm spEnd spEnd_apply)

@[expose] def SeitzFourSp4DiagQuat : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 →
    ∀ E : Subgroup (MulAut (StatedProj (StatedSp 2 F))), IsElemAbelian 2 E → Nat.card E = 4 →
    (∀ W : Submodule F (Fin 2 ⊕ Fin 2 → F), (∀ x ∈ W, ∀ y ∈ W, spForm 2 F x y = 0) →
      (∀ A : gsp 2 F, conjAut 2 F A ∈ E →
        ∀ w ∈ W, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W) →
      W = ⊥) →
    ∀ (a : StatedSp 2 F) (B : gsp 2 F) (ν : F),
      MulAut.conj (proj 2 F a) ∈ E → MulAut.conj (proj 2 F a) ≠ 1 → conjAut 2 F B ∈ E →
      MulAut.conj (proj 2 F a) ≠ conjAut 2 F B →
      ((a : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((a : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1 →
      ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F *
        ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
          ν • formJ 2 F →
      ¬ IsSquare ν →
      ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (-ν) • 1 →
      ((a : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
          -(((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
            ((a : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) →
      PlaneGen E

theorem seitzFourSp4DiagAniso_of_quat (hQ : SeitzFourSp4DiagQuat) : SeitzFourSp4DiagAniso := by
  intro F _ _ hF E hE h4 hlin hout hnoW
  classical
  obtain ⟨a, B, ε, ν, β, lam, haE, ha1, hBE, hB1, hab, hA2, hεpm, hBform, hν, hB2, hβpm,
    hAB, hlampm⟩ :=
    exists_lifts_of_spLinear_of_not_inner (F := F) (r := 2) (by norm_num) hE h4 hlin hout
  set MA : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((a : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hMA
  set MB : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hMB
  have hA2' : MA * MA = ε • 1 := by rw [hMA]; exact hA2
  have hBform' : MBᵀ * formJ 2 F * MB = ν • formJ 2 F := by rw [hMB]; exact hBform
  have hB2' : MB * MB = β • 1 := by rw [hMB]; exact hB2
  have hAB' : MA * MB = lam • (MB * MA) := by rw [hMA, hMB]; exact hAB
  rcases hεpm with hε1 | hεm1
  ·
    have haa : spEnd a * spEnd a = 1 := by
      refine LinearMap.ext fun v => ?_
      rw [Module.End.mul_apply, spEnd_apply, spEnd_apply, Matrix.mulVec_mulVec, hA2', hε1,
        one_smul, Matrix.one_mulVec]
      rfl
    exact planeGen_of_involutory_lift (F := F) (r := 2) (by norm_num) hF hE h4 a haE ha1 haa
      B hBE hB1 hab
  ·
    have hA2m : MA * MA = -1 := by rw [hεm1] at hA2'; simpa using hA2'
    have hAform : MAᵀ * formJ 2 F * MA = formJ 2 F := by
      have h := SymplecticTorusWeyl.mem_statedSp_iff.mp a.2
      simpa [hMA] using h
    rcases hlampm with hl1 | hlm1
    ·
      have hABc : MA * MB = MB * MA := by rw [hAB', hl1, one_smul]
      obtain ⟨W, hW0, hWiso, hWA, hWB⟩ :=
        exists_isotropic_of_commute_of_neg (F := F) (r := 2) (A := MA) (B := MB)
          (ν := ν) (β := β) hF (by norm_num) hAform hA2m hBform' hν hB2' hABc
      have hst : ∀ A : gsp 2 F, conjAut 2 F A ∈ E →
          ∀ w ∈ W, ((A : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W :=
        lift_mulVec_mem_of_stable (F := F) (r := 2) (by norm_num) hE h4 haE ha1 hBE hB1 hab
          hWA hWB
      exfalso
      exact hW0 (hnoW W hWiso hst)
    · rcases hβpm with hβν | hβmν
      ·
        have hABa : MA * MB = -(MB * MA) := by rw [hAB', hlm1, neg_one_smul]
        have hB2ν : MB * MB = ν • 1 := by rw [hβν] at hB2'; simpa using hB2'
        obtain ⟨W, hW0, hWiso, hWA, hWB⟩ :=
          exists_isotropic_of_anticommute_of_eq (F := F) (r := 2) (A := MA) (B := MB)
            (ν := ν) hF (by norm_num) hAform hA2m hBform' hν hB2ν hABa
        have hst : ∀ A : gsp 2 F, conjAut 2 F A ∈ E →
            ∀ w ∈ W, ((A : GL (Fin 2 ⊕ Fin 2) F) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W :=
          lift_mulVec_mem_of_stable (F := F) (r := 2) (by norm_num) hE h4 haE ha1 hBE hB1 hab
            hWA hWB
        exfalso
        exact hW0 (hnoW W hWiso hst)
      ·
        have hABa : MA * MB = -(MB * MA) := by rw [hAB', hlm1, neg_one_smul]
        have hB2neg : MB * MB = (-ν) • 1 := by rw [hβmν] at hB2'; simpa using hB2'
        exact hQ F hF E hE h4 hnoW a B ν haE ha1 hBE hab hA2m hBform' hν hB2neg hABa

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
