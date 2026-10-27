module

public import CFSG.Quasithin.Background.Harris.L2.Cases
public import CFSG.Quasithin.Background.Harris.L2.NaturalAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesNatural

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem endIsField_of_natCard [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) {n : ℕ}
    (hcard : Nat.card (endCommutant L) = 2 ^ n) : EndIsField L n := by
  classical
  have := CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_nontrivial hL
  have := CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_noZeroDivisors hL
  have : IsDomain (endCommutant L) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant L) := Subtype.finite
  let alg : Algebra (ZMod 2) (endCommutant L) := inferInstance
  let _ : Field (endCommutant L) := (Finite.isDomain_to_isField (endCommutant L)).toField
  let _ : Algebra (ZMod 2) (endCommutant L) := alg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨GaloisField.algEquivGaloisField 2 n hcard⟩

theorem nontrivial_sl2 (F : Type*) [Field F] : Nontrivial SL(2, F) := by
  refine ⟨⟨1, ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩⟩
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp at this

theorem case6_holds : Case6Input := by
  intro V _ _ _ Γ A L m n hs hn φ hmn hD hdim
  classical
  have hn0 : n ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 n hn0
  have : Fact (repOf L φ).IsIrreducible := ⟨repOf_isIrreducible φ hs.L_irr⟩
  have := nontrivial_sl2 (GaloisField 2 n)
  have hdimV : Module.finrank (ZMod 2) V = n * 2 := by
    rw [finrank_eq_mul_of_card hD, hdim]
  have hb := hs.bound
  obtain ⟨θ, hθ⟩ := exists_natural_iso (by omega) hF (repOf L φ) (repOf_nontrivial L φ) hD hdim
  let ψ : V ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 n) :=
    LinearEquiv.mk (AddMonoidHom.toZModLinearMap 2 θ.toAddMonoidHom) θ.symm θ.left_inv θ.right_inv
  have hψ : ∀ (h : ↥L) (v : V), ψ ((h : GLV V) v) =
      ((φ h : SL(2, GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
        (ψ v) := fun h v => by
    have := hθ (φ h) v
    rw [repOf_apply, MulEquiv.symm_apply_apply] at this
    exact this
  refine ⟨n, ⟨by omega, by omega, by omega, hmn, ?_⟩, ?_, selfDual_of_natural φ ψ hψ⟩
  · refine ⟨φ.trans (specialLinearGroupEquivStatedSL 2 (GaloisField 2 n)), ψ, fun h v => ?_⟩
    rw [hψ]
    rfl
  · refine endIsField_of_natCard hs.L_irr ?_
    rw [natCard_endCommutant_eq L φ, hD]

end CFSG.Quasithin.G11.Harris.L2
