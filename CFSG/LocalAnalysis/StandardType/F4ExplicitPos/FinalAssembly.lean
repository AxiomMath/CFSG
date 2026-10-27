module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedPairAmbientPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart3
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NeighbourFinalPart2

@[expose] public section

public noncomputable section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieKnownR2.F4
  CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.ActualSetup

open CFSG.StandardType.F4ExplicitPos.LiteralSetup

open CFSG.StandardType.F4ExplicitPos.SelectedPair

open CFSG.StandardType.F4ExplicitPos.SelectedPairAmbient

open CFSG.StandardType.F4ExplicitPos.ComponentAttach

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.RationalA2Finish

open CFSG.StandardType.F4ExplicitPos.NeighbourFinal

open CFSG.StandardType.LieCore

open scoped Matrix

namespace CFSG.StandardType.F4ExplicitPos.FinalAssembly

theorem f4_sp6_position :
    ∀ (X : Type) [Group X] [Finite X] (n f : ℕ)
      (ψ : (ggU .F4 n f).K →* X) (p : ℕ)
      (G₀ B₁ D J L : Subgroup X) (x : X),
      GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x →
      ∃ R Rm : Subgroup X,
        R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .F4 n f p ψ R Rm ∧ 1 ≤ f ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) →
            J ≤ K → K ≠ J → Odd (Nat.card (Subgroup.center ↥K)) →
            K = G₀ ∨
              ∃ β : Fin (ggU .PSp 3 f).D.rank → ℤ,
                β ∈ (ggU .PSp 3 f).D.roots ∧
                  GGRootVia (ggU .PSp 3 f) K R β := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hH
  let : Algebra (ZMod 2) (F4Omega f) := ZMod.algebra (F4Omega f) 2
  let : Algebra.IsAlgebraic (ZMod 2) (F4Omega f) :=
    CFSG.LieType.Chevalley.algebraicClosure_isAlgebraic_zmod 2 (GaloisField 2 f)
  set FD := F4PosData.ofHyp hH with hFD
  obtain ⟨w, g0, hg0C, hg0, hFrob, hFin, htor, hstep, hTheker, d, hdD, coord,
    hd1, hdCL, hgen, hcoord, hexp, hcd, hattach, hsel⟩ :=
    CFSG.StandardType.F4ExplicitPos.SelectedLiteral.f4_literal_selected_pair hH
  obtain ⟨iJ, hle, hSelPair⟩ := hsel
  set Δ : LangDatum Tag.F4 (F4Omega f) :=
    langDatumF4 (K := GaloisField 2 f) (L := F4Omega f) (iterateFrobenius (F4Omega f) 2 f)
      (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w hg0C hg0 with hΔ
  have hpOdd : Odd p := FD.hp.odd_of_ne_two FD.hp2
  have hpa : ∀ i, coord ⟨x, FD.h17⟩ i ^ p = 1 := fun i => hexp ⟨x, FD.h17⟩ i
  have hpd : ∀ i, coord ⟨d, hdD⟩ i ^ p = 1 := fun i => hexp ⟨d, hdD⟩ i
  have hTorAll : ∀ d0 : D, rootDiagUnit Tag.F4 (coord d0) ∈ Δ.torus := by
    intro d0
    apply CFSG.StandardType.F4ExplicitPos.SelectedLiteral.rootDiagUnit_mem_torus_of_step_fixed Δ
    rw [← hcoord d0]
    exact hstep (Subgroup.inclusion FD.hDB d0)
  have hJorbit : ((J.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
        (center_adjointGroup_F4_galoisField f) g0)) ≤
      rootSpan .F4 (F4Omega f)
        (ratOrbit (fun u => (MulAction.toPerm w) u)
          (componentRoots (jointChar (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩)) iJ)) := by
    rw [CFSG.StandardType.F4ExplicitPos.OddKernelActual.f4_joint_ratOrbit_eq_of_coord
      (D := Δ) (ρ := MulAction.toPerm w) hFrob
      (coord ⟨x, FD.h17⟩) (coord ⟨d, hdD⟩) (hTorAll ⟨x, FD.h17⟩) (hTorAll ⟨d, hdD⟩)
      hpOdd hpa hpd iJ]
    exact hle
  obtain ⟨alpha, wD, eps, epsm, R, Rm, hAlpha, hwD, hRJ, hRmJ, hReta, hRmeta, hAmbient⟩ :=
    CFSG.StandardType.F4ExplicitPos.SelectedPairAmbient.f4_selected_pair_ambient
      (Ω := F4Omega f) n f p FD.hf ψ G₀ FD.hG0 FD.hker
      (center_adjointGroup_F4_galoisField f)
      (Fr := iterateFrobenius (F4Omega f) 2 f)
      (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) rfl w hg0C hg0
      J (FD.h15.1.trans inf_le_left) hSelPair
  have hRcard : Nat.card ((R.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
        (center_adjointGroup_F4_galoisField f) g0)) = Nat.card (GaloisField 2 f) := by
    rw [hReta]
    exact conjugatedRootRange_card wD alpha eps
  have hRcurve : ((R.subgroupOf G₀).map (etaF4 (L := F4Omega f) ψ G₀ FD.hG0 FD.hker
        (center_adjointGroup_F4_galoisField f) g0)) ≤
      (rootSubgroup Tag.F4 (F4Omega f) alpha).map (MulAut.conj wD).toMonoidHom := by
    rw [hReta]
    exact SelectedPairAmbient.conjugatedRootRange_le_conj_rootSubgroup
      (k := GaloisField 2 f) wD alpha eps
  refine ⟨R, Rm, hRJ, hRmJ, hAmbient, FD.hf, ?_⟩
  intro e he hene K hKG hKcomp hJK hKne hKodd
  exact CFSG.StandardType.F4ExplicitPos.NeighbourFinal.f4_neighbour_actual
    (X := X) (n := n) (f := f) (p := p) (ψ := ψ)
    (G₀ := G₀) (B₁ := B₁) (D := D) (J := J) (L := L) (x := x)
    hH (iterateFrobenius (F4Omega f) 2 f)
    (iterateFrobenius_card_F4 (L := F4Omega f) f FD.hf) w g0 hg0C hg0
    (MulAction.toPerm w) hFrob hdD hgen coord hcoord hexp hTorAll hstep
    hattach hJorbit hAlpha hwD hRJ hRcard hRcurve he hene hKG hKcomp hJK hKne hKodd

theorem f4PosExplicit :
    GGSixF4PosExplicit :=
  CFSG.StandardType.LieKnownR2.F4.f4PosExplicit_of_sp6_position f4_sp6_position

end CFSG.StandardType.F4ExplicitPos.FinalAssembly

end

end
