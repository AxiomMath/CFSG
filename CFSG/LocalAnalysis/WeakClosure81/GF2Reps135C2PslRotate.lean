module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Label
public import CFSG.LieType.SpecialLinear.TypeLabel.Rotation
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.EndField
import CFSG.LieType.SpecialLinear.TypeLabel.StagePeriod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module Finset
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open scoped TensorProduct

theorem w135c2_rotate_of_hasTwistedLabel {m f : ℕ} {K : Type} [Field K] [Fintype K]
    [CharP K 2] (hK : Fintype.card K = 2 ^ f)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {ε : Fin f → Finset (Fin (m + 1))} (hε : HasTwistedLabel ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K))
      ρ.asModule) = 2 ^ s) :
    ∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (SpecialLinearGroup (Fin (m + 1)) K)) ρ.asModule
  obtain ⟨k, _, _, _, _, y, χ, J, h0, ht, hχ, _, _, _⟩ := hε
  haveI : Fintype E := Fintype.ofFinite E
  have hsimp := isSimpleRep_extendScalars_endFieldRep ρ k
  have hval : ∀ g ∈ (curtisDatum m K 2).H, ∃ c : E, χ g = algebraMap E k c :=
    chi_mem_range_of_isCoverType_extendScalars (m := m) (F := K) (E := E) (k := k)
      (X := ρ.asModule) (CFSG.endFieldRep ρ) hsimp ht
  have hEcard : Fintype.card E = 2 ^ s := by
    rw [← Nat.card_eq_fintype_card]
    exact hE
  intro r
  exact rotate_eq_of_chi_mem_range (F := K) (E := E) (k := k) hK hEcard ε h0 hχ hval r

end CFSG.LocalAnalysis.WeakClosure81
