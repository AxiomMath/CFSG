module

public import CFSG.LocalAnalysis.StandardType.GGK0LQNodes
public import CFSG.LocalAnalysis.StandardType.GGK0LQPairTable

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private lemma lk0xlqpair_span_nodes (A : K0LangMark Omega lab p R I phi)
    (x y : ℕ) (hx : x < A.row.diagram.marks.length) (hy : y < A.row.diagram.marks.length) :
    ({w : Fin A.tau.rank → ℤ | ∃ i : Fin A.row.diagram.marks.length,
        i.val ∈ [x, y] ∧ w = A.nodeMap (Pi.single i 1)} : Set (Fin A.tau.rank → ℤ)) =
      ({lqExtRoot A.tau A.row.T x, lqExtRoot A.tau A.row.T y} : Set (Fin A.tau.rank → ℤ)) := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨i, hix | hiy, rfl⟩
    · left
      rw [show i = ⟨x, hx⟩ from Fin.ext hix, lq_nodeMap_eq A ⟨x, hx⟩]
    · right
      rw [show i = ⟨y, hy⟩ from Fin.ext hiy, lq_nodeMap_eq A ⟨y, hy⟩]
  · rintro (rfl | rfl)
    · exact ⟨⟨x, hx⟩, Or.inl rfl, (lq_nodeMap_eq A ⟨x, hx⟩).symm⟩
    · exact ⟨⟨y, hy⟩, Or.inr rfl, (lq_nodeMap_eq A ⟨y, hy⟩).symm⟩

theorem lq_pair_ncard (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h : (lqNodes A P j).length = 2) :
    (componentRoots (rootCharHom A.a) (P.repr j)).ncard =
      if (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .A then 6 else 8 := by
  obtain ⟨x, y, hc, hxy, hy, hadj⟩ := lq_pair_adj A P j h
  have hx : x < A.row.diagram.marks.length := lt_trans hxy hy
  rw [P.repr_roots j, show (P.orbitNodes j).headD [] = [x, y] from hc]
  rw [lk0xlqpair_span_nodes A x y hx hy]
  rw [hc]
  exact lq_pair_ncard_table A.tau A.row.T A.tau_eq x y hxy hy hadj

end CFSG.StandardType.GGK0LQ

end
