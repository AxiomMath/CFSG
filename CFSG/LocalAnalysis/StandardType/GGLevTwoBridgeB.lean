module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4bAux1
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4bAux2
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4bAux3
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4bIndep

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem LevTwoType

section Bridge

variable {G : Type} [Group G] [Finite G]

@[expose] def levTwoPhiOf (T : LevTwoType) {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} (ρ : Wg T.rootFT ≃* ↥A)
    (AL : Subgroup (MulAut ↥Bs)) : Set (Fin T.n → ℤ) :=
  {β | IsRt T.rootFT β ∧ ((ρ (rRefl T.rootFT β) : ↥A) : MulAut ↥Bs) ∈ AL}

theorem levTwoPhiData (T : LevTwoType) (hT : T.Valid) (p : ℕ) (Bs : Subgroup G)
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (A : Subgroup (MulAut ↥Bs)) (hA : A ≤ ggInduced ⊤ Bs) (ρ : Wg T.rootFT ≃* ↥A)
    (hdict : ∀ a : MulAut ↥Bs, (a ∈ A ∧ GGIsReflection p a) ↔
      ∃ g ∈ Refl T.rootFT, ((ρ g : ↥A) : MulAut ↥Bs) = a)
    (AL : Subgroup (MulAut ↥Bs)) (ιL : Type) [Fintype ιL] (ML : CoxeterMatrix ιL)
    (hAL : AL ≤ A) (hML : GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) (hW : GGWeylOfType p ML AL) :
    PhiStruct T.rootFT (levTwoPhiOf T ρ AL) ∧
      (∃ s : Finset (Fin T.n → ℤ), (s : Set (Fin T.n → ℤ)) ⊆ levTwoPhiOf T ρ AL ∧
        LinearIndependent ℚ (fun v : s => toRat (v : Fin T.n → ℤ)) ∧ s.card = Fintype.card ιL) ∧
      3 ≤ Fintype.card ιL ∧
      (Wsub T.rootFT (levTwoPhiOf T ρ AL)).map (A.subtype.comp ρ.toMonoidHom) = AL := by
  have _ := hT
  classical
  let c : levTwoS4b_Ctx G :=
    { T := T, hT := hT, p := p, Bs := Bs, hp := hp, hp2 := hp2, hEl := hEl, hNT := hNT,
      A := A, hA := hA, ρ := ρ, hdict := hdict, AL := AL, ιL := ιL,
      fintype := inferInstance, decEq := Classical.decEq ιL, ML := ML,
      hAL := hAL, hML := hML, hW := hW }
  have hphi : levTwoS4b_Phi c = levTwoPhiOf T ρ AL := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := levTwoS4b_phiStruct_basic c
    rwa [hphi] at h
  · obtain ⟨s, hs, hli, hcard⟩ := levTwoS4b_indep c
    exact ⟨s, by rwa [hphi] at hs, hli, hcard⟩
  · exact levTwoS4b_card c
  · have h := levTwoS4b_wsub c
    rwa [hphi] at h

end Bridge

end CFSG.StandardType.LevTwo
