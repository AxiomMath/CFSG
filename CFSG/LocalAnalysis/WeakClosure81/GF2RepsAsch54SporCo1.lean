module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.Sporadic.Co1.Asch54Pair
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co2Schreier.FullAut

import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
import CFSG.Sporadic.Schreier.PairOuter
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Co1Sub

theorem isSylowIn_T₀_co1 :
    IsSylowIn 2 T₀ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, IsPGroup.of_card card_T₀, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index T₀
  rw [card_T₀, Sporadic.Bridge.Co1.card_J] at h
  omega

theorem isLPair_A₀_B₀_co1 :
    IsLPair IsCalL0 T₀ A₀ B₀ where
  le_left := T₀_le_A₀
  le_right := T₀_le_B₀
  ne_top_left h := by
    have h1 := congrArg (fun H : Subgroup (J co1D) => Nat.card H) h
    simp only [Subgroup.card_top, Sporadic.Bridge.Co1.card_J, card_A₀] at h1
    omega
  ne_top_right h := by
    have h1 := congrArg (fun H : Subgroup (J co1D) => Nat.card H) h
    simp only [Subgroup.card_top, Sporadic.Bridge.Co1.card_J, card_B₀] at h1
    omega
  not_left := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 21) (N := 3 * 2 ^ 21)
    (by decide +kernel) (dvd_of_eq card_A₀)
  not_right := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 21) (N := 405 * 2 ^ 21)
    (by decide +kernel) (dvd_of_eq card_B₀)
  sup_eq_top := sup_A₀_B₀

theorem card_outer_J_co1D :
    Nat.card (Outer ↥(J co1D)) = 1 := by
  have hin : ∀ α : MulAut Blueprint.NativeSporadic.Co1, ∃ g : Blueprint.NativeSporadic.Co1,
      α = MulAut.conj g :=
    Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner
  have h1 : Nat.card (Outer Blueprint.NativeSporadic.Co1) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨Sporadic.Co1Schreier.subsingleton_outer_of_inner hin, ⟨1⟩⟩
  have h2 : Nat.card (Outer ↥(J co1D)) ≤ 1 :=
    Sporadic.Schreier.outer_card_le_of_equiv h1.le
      (seedEquiv Sporadic.Co1.co1Facts.toBaseFacts).symm
  have h3 : Nat.card (Outer Blueprint.NativeSporadic.Co1) ≤ Nat.card (Outer ↥(J co1D)) :=
    Sporadic.Schreier.outer_card_le_of_equiv le_rfl (seedEquiv Sporadic.Co1.co1Facts.toBaseFacts)
  rw [h1] at h3
  omega

theorem asch54SporGenAt_co1 :
    Asch54SporGenAt .Co1 :=
  asch54SporGenAt_of_isLPair_of_card_outer_eq_one
    (Sporadic.Bridge.Co1.nonempty_mulEquiv.map fun e =>
      e.symm.trans Sporadic.Bridge.Co1.nativeEquiv)
    card_outer_J_co1D isSylowIn_T₀_co1 isLPair_A₀_B₀_co1

end CFSG.LocalAnalysis.WeakClosure81

end
