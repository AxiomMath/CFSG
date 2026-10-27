module

public import CFSG.LocalAnalysis.StandardType.GGK0LEModel
public import CFSG.LocalAnalysis.StandardType.GGK0LEA12E7
public import CFSG.Sporadic.ThSchreier.GlobalData

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.AlgebraicGroups

theorem k0_fullFactor_a12_invariant_of_twE6
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hAlg : ∀ c : Omega, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (hqs : ∀ j, A.row.D.orbits[j].qs = true →
      CFSG.IsQuasisimple (rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (hsolv : ∀ j, A.row.D.orbits[j].qs = false →
      Group.IsSolvable (rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)))
    (hn : 1 ≤ lab.n) (hp : p.Prime) (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hjqs : A.row.D.orbits[j].qs = false)
    (htw : lab.tag = .twE6 → ∀ u : MulAut R, Commute u phi →
      (fullFactor A.setup A.iota A.a (P.repr j)).map u.toMonoidHom =
        fullFactor A.setup A.iota A.a (P.repr j))
    (u : MulAut R) (hu : Commute u phi) :
    (fullFactor A.setup A.iota A.a (P.repr j)).map u.toMonoidHom =
      fullFactor A.setup A.iota A.a (P.repr j) := by
  obtain ⟨hn1, -, htag⟩ := ggKacValid_a12_tag hn hp hd A.row.valid j ⟨hj, hjqs⟩
  rcases htag with htag | htag
  · have hT : A.row.T = .E7 := by
      have h : some (GGKacType.E7, false) = some (A.row.T, A.row.tw) := by
        rw [← A.row.type_eq]
        simp [ggKacTypeOfLabel, htag]
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    obtain ⟨g, rfl⟩ := k0_exists_modelAction_eq_E7 hAlg A hT hn1 u
    exact k0_fullFactor_a12_map_modelAction A P hqs hsolv hn hp hd j hj hjqs g hu
  · exact htw htag u hu

end CFSG.StandardType.GGK0MarkedKacIface1587
