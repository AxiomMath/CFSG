module

public import CFSG.Quasithin.Background.Harris.L2.Cases
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusNat
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusSelfDual
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusEnd

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
  CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

theorem case7_holds : Case7Input := by
  intro V _ _ _ Γ A L m a hs ha φ hma hD hdim
  classical
  let F := GaloisField 2 (2 * a)
  let _ : Fintype F := Fintype.ofFinite _
  have hF : Fintype.card F = 2 ^ (2 * a) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * a) (by omega)]
  have : Fact (repOf L φ).IsIrreducible := ⟨repOf_isIrreducible φ hs.L_irr⟩
  have hnt : Nontrivial SL(2, F) := by
    refine ⟨⟨1, ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩⟩
    have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp at this
  obtain ⟨j, β, hβ⟩ := orth_iso (s := a) ha hF (repOf L φ) (repOf_nontrivial L φ) hD hdim
  obtain ⟨b, c, hbc, Θ, ψ, hψ, hQ⟩ := natural_omega_of_orth ha φ hF β j hβ
  have hdimF : Module.finrank (ZMod 2) V = a * 4 := by
    rw [finrank_eq_mul_of_card hD, hdim]
  have hbound := hs.bound
  refine ⟨a, ⟨ha, by omega, by omega, hma,
    ⟨φ.trans (specialLinearGroupEquivStatedSL 2 F)⟩, b, c, hbc, Θ, ψ, hψ⟩,
    endIsField_of_card hs.L_irr φ ha hD,
    selfDual_of_omegaNatural hbc ψ (fun l => ((Θ l : GL QIdx (GaloisField 2 a)) :
      Matrix QIdx QIdx (GaloisField 2 a))) hψ hQ⟩

end CFSG.Quasithin.G11.Harris.L2
