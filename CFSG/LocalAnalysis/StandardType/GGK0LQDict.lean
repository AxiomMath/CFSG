module

public import CFSG.LocalAnalysis.StandardType.GGK0LQRoots
public import CFSG.LocalAnalysis.StandardType.GGK0LQTwist
public import CFSG.Sporadic.ThSchreier.GlobalData

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

theorem lq_K4 (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A) (j : Fin A.row.D.orbits.length)
    (hj : A.row.D.orbits[j].lab = ⟨.A, 1, 1⟩) (hqs : A.row.D.orbits[j].qs = false) :
    twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner ∧
      A.setup.D.q ^ componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j))
        = 2 ∧ ∀ α ∈ componentRoots (rootCharHom A.a) (P.repr j),
          ∀ δ ∈ componentRoots (rootCharHom A.a) (P.repr j), δ = α ∨ δ = -α := by
  obtain ⟨hfam, hcase, hn⟩ := (lq_qs_false_iff A P j).1 hqs
  have hq : A.setup.D.q ^ componentOrbitLength A.setup.ρ
      (componentRoots (rootCharHom A.a) (P.repr j)) = 2 := by
    rw [lq_qpow A P j, hn]; norm_num
  rcases hcase with ⟨-, hr1⟩ | ⟨htw, hr2⟩
  · have hlen : (lqNodes A P j).length = 1 := by rw [← lq_compType_A_rank _ _ hfam]; exact hr1
    exact ⟨lq_kind_of_rankOne A P j hlen, hq, (lq_rankOne_iff A P j).2 hlen⟩
  · exfalso
    have h := lq_descriptor_eq A P j
    have hl : (k0LabelOf (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1
        (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).2 (lqTw A P j)
        ((P.orbitNodes j).length * lab.n)).lab = ⟨.A, 1, 1⟩ := by
      rw [← h]
      exact hj
    rw [hfam] at hl
    unfold k0LabelOf at hl
    split_ifs at hl <;> simp_all

end CFSG.StandardType.GGK0LQ

end
