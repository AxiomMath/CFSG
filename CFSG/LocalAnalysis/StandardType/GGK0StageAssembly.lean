module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
import CFSG.LocalAnalysis.StandardType.GGK0CentralTorusLeaf
import CFSG.LocalAnalysis.StandardType.GGK0LEModel

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]

theorem rationalAt_of_stages
    {lab : LargeEvenLabel} {p : ℕ}
    (hA : LargeEvenLabelAll lab (fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
      Nonempty (K0LangMark Omega lab p R I phi)))
    (hP : ∀ {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
      (A : K0LangMark Omega lab p R I phi), Nonempty (K0Positions A))
    (hqs : ∀ {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
      (A : K0LangMark Omega lab p R I phi) (P : K0Positions A) (j : Fin A.row.D.orbits.length),
      A.row.D.orbits[j].qs = true →
        CFSG.IsQuasisimple (rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (hlabel : ∀ {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
      (A : K0LangMark Omega lab p R I phi) (P : K0Positions A) (j : Fin A.row.D.orbits.length),
      A.row.D.orbits[j].qs = true → LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
        GGHasLabel A.row.D.orbits[j].lab
          ((coreFactor A.setup A.iota A.a (P.repr j)) ⧸
            Subgroup.center (coreFactor A.setup A.iota A.a (P.repr j))))
    (hsolv : ∀ {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
      (A : K0LangMark Omega lab p R I phi) (P : K0Positions A) (j : Fin A.row.D.orbits.length),
      A.row.D.orbits[j].qs = false →
        Group.IsSolvable (rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (ha12 : ∀ {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
      (A : K0LangMark Omega lab p R I phi) (P : K0Positions A) (j : Fin A.row.D.orbits.length),
      A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩ → A.row.D.orbits[j].qs = false →
        Nonempty ((fullFactor A.setup A.iota A.a (P.repr j)) ≃* Equiv.Perm (Fin 3)))
    (hinv : ∀ {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
      (A : K0LangMark Omega lab p R I phi) (P : K0Positions A) (j : Fin A.row.D.orbits.length),
      A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩ → A.row.D.orbits[j].qs = false →
        ∀ u : MulAut R, Commute u phi →
          (fullFactor A.setup A.iota A.a (P.repr j)).map u.toMonoidHom =
            fullFactor A.setup A.iota A.a (P.repr j))
    (hcentred : ∀ {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
      (A : K0LangMark Omega lab p R I phi), GGKacCentred lab p →
        adjointGroup A.tau Omega ⊓ Subgroup.centralizer {rootDiagUnit A.tau A.a} ≤
          Subgroup.closure (Set.range (fun b : Fin A.tau.rank → Omegaˣ =>
            rootDiagUnit A.tau b)) ⊔
            rootSpan A.tau Omega (kernelRoots (rootCharHom A.a))) :
    LargeEvenLabelAll lab (fun R _ I _ => ∀ phi : MulAut R, phi ∈ I → orderOf phi = p →
      Nonempty (MarkedRationalKacRealization Omega lab p R I phi)) := by
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ (hA Q hQ)
  rintro R _ I F ⟨hq, h⟩
  refine ⟨hq, fun phi hphi hord => ?_⟩
  obtain ⟨A⟩ := h phi hphi hord
  obtain ⟨P⟩ := hP A
  obtain ⟨T⟩ := k0CentralTorus_nonempty A
  exact ⟨A.toRealization P T (hqs A P) (hlabel A P) (hsolv A P) (ha12 A P)
    (k0_fullFactor_map_modelAction A P) (hinv A P) (hcentred A)⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
