module

public import CFSG.Quasithin.Background.SmithB42Sp4Excl
import CFSG.Quasithin.Background.SmithB42Sp4Ident
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Sub

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin.B42Sp4 CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {f : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem finrank_endRing_subquotient_eq_four_of_sp4_displacement_lt_three_mul
    (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (ρ : Representation (ZMod 2) (antiSp F) W)
    (A : Subrepresentation ρ) (B : Subrepresentation A.toRepresentation)
    [Finite (A.toSubmodule ⧸ B.toSubmodule)] [Fact B.quotient.IsIrreducible]
    (hnt : ∃ g, B.quotient g ≠ 1)
    (z : antiSp F) (hz : z * z = 1) (hz1 : z ≠ 1)
    (hsmall : Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * f) :
    Module.finrank (EndRing B.quotient) (A.toSubmodule ⧸ B.toSubmodule) = 4 := by
  let π : antiSp F →* ((A.toSubmodule ⧸ B.toSubmodule) ≃ₗ[ZMod 2]
      (A.toSubmodule ⧸ B.toSubmodule)) :=
    { toFun := repLinEquiv B.quotient
      map_one' := repLinEquiv_one B.quotient
      map_mul' := repLinEquiv_mul B.quotient }
  have hπ : repOf π = B.quotient := by
    ext g w
    rw [repOf_apply]
    rfl
  have : Fact (repOf π).IsIrreducible := ⟨by rw [hπ]; exact Fact.out⟩
  have hnt' : ∃ g, repOf π g ≠ 1 := by rwa [hπ]
  have hbound : dispRank (π z) < 3 * f :=
    lt_of_le_of_lt
      ((CFSG.QuasithinUnique.Setup.X7.finrank_range_quotient_le B z).trans
        (CFSG.QuasithinUnique.Setup.X7.finrank_range_toRepresentation_le A z)) hsmall
  by_contra hdim
  have hdim' : Module.finrank (EndRing (repOf π))
      (A.toSubmodule ⧸ B.toSubmodule) ≠ 4 := by rw [hπ]; exact hdim
  exact (not_lt_of_ge (displacement_ge hF hf π hnt' hdim' hz hz1).1) hbound

theorem natural_subquotient_of_sp4_displacement_lt_three_mul
    (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (ρ : Representation (ZMod 2) (antiSp F) W)
    (A : Subrepresentation ρ) (B : Subrepresentation A.toRepresentation)
    (hirr : B.quotient.IsIrreducible) (hnt : ∃ g, B.quotient g ≠ 1)
    (z : antiSp F) (hz : z * z = 1) (hz1 : z ≠ 1)
    (hsmall : Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * f) :
    ∃ (i : ℕ) (φ : (A.toSubmodule ⧸ B.toSubmodule) ≃+ (Fin 4 → F)),
      ∀ g w, φ (B.quotient g w) =
        (glMat (((minorAut F ^ i) g : antiSp F) : GL (Fin 4) F)).mulVec (φ w) := by
  have : Fact B.quotient.IsIrreducible := ⟨hirr⟩
  have : Finite (A.toSubmodule ⧸ B.toSubmodule) :=
    Finite.of_surjective Submodule.Quotient.mk (Submodule.Quotient.mk_surjective B.toSubmodule)
  let π : antiSp F →* ((A.toSubmodule ⧸ B.toSubmodule) ≃ₗ[ZMod 2]
      (A.toSubmodule ⧸ B.toSubmodule)) :=
    { toFun := repLinEquiv B.quotient
      map_one' := repLinEquiv_one B.quotient
      map_mul' := repLinEquiv_mul B.quotient }
  have hπ : repOf π = B.quotient := by
    ext g w
    rw [repOf_apply]
    rfl
  have : Fact (repOf π).IsIrreducible := ⟨by rw [hπ]; exact hirr⟩
  have hnt' : ∃ g, repOf π g ≠ 1 := by rwa [hπ]
  have hdim : Module.finrank (EndRing (repOf π))
      (A.toSubmodule ⧸ B.toSubmodule) = 4 := by
    rw [hπ]
    exact finrank_endRing_subquotient_eq_four_of_sp4_displacement_lt_three_mul
      hF hf ρ A B hnt z hz hz1 hsmall
  exact exists_natural_of_four hF hf π hnt' hdim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
