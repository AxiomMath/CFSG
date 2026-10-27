module

public import CFSG.LocalAnalysis.StandardType.GGLangE8RecogBase

public section

namespace CFSG.StandardType

section Recognition

open CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem recoga_class_exists
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (hτ : B.τ = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    {b : Bs} (hb : b ≠ 1) {Jm : Subgroup (GGAutU .E8 n' f)}
    (hJm : CFSG.Assembly.IsComponentOf Jm ((ggPsiU .E8 n' f).range ⊓
      Subgroup.centralizer ({(b : GGAutU .E8 n' f)} : Set (GGAutU .E8 n' f))))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJ : GGHasLabel labJ (↥Jm ⧸ Subgroup.center ↥Jm)) :
    ∃ i : KernelComponent (rootCharHom (B.a b)),
      CFSG.IsQuasisimple ↥(recogaR B b i) ∧
        Jm = ((recogaR B b i).comap B.ι).map (ggPsiBar .E8 n' f) ∧
        GGHasLabel labJ (↥(recogaR B b i) ⧸ Subgroup.center ↥(recogaR B b i)) := by
  obtain ⟨i, hq, hEq⟩ := ggLang_exists_rationalComponent_of_isComponentOf B hp hp2 hb hJm
  refine ⟨i, hq, hEq, ?_⟩
  have hR : recogaR B b i ≤ B.setup.Γ := (Subgroup.commutator_le_self _).trans inf_le_right
  obtain ⟨e⟩ := ggPsiImage_mulEquiv B hR
  rw [← hEq] at e
  exact ggHasLabel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hJ

end Recognition

end CFSG.StandardType

end
