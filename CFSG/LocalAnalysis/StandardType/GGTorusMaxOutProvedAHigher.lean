module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_A_higher (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : d.1 = .A n q) (hn : 2 ≤ n)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  subst hd
  obtain ⟨e⟩ := e
  have hmodel : CFSG.Models.LieModel J .PSL (n + 1) q.p q.exponent :=
    CFSG.Models.lieModel_A n q hv e
  have hT : CFSG.Open.StatedClassicalModel J .PSL (n + 1) q.p q.exponent :=
    CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) hmodel
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ∣
      2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent - 1) := by
    simpa only [CFSG.RankThree.OuterOrder.determinantParameter] using
      (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
        (Or.inl rfl) (by omega) q.prime_p q.exponent_pos hT).1
  have haut : Nat.card (MulAut J) ∣ Nat.card J *
      (2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent - 1)) :=
    CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd hout
  have htm : tmLieOut (.A n q) =
      2 * q.exponent * Nat.gcd (n + 1) (q.p ^ q.exponent - 1) := by
    simp only [tmLieOut, TauCeti.PrimePower.card_def]
    rw [if_neg (by omega : ¬ n = 1)]
    ring
  rw [htm]
  exact haut

end CFSG.StandardType.FrameRoute

end
