module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem w135c2_psl_adjoint {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {K : Type} [Field K] [Fintype K] [CharP K 2] (hK : Fintype.card K = 2)
    (φ : SpecialLinearGroup (Fin 3) K →* ↥L) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K))
    (hW : Nat.card W = 2 ^ 8) : Chev2Item3 W L := by
  classical
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin 3) K) = ⊥ :=
    center_specialLinear_eq_bot_of_card_two hK
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hcenter ▸ hker)
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  let e : SpecialLinearGroup (Fin 3) K ≃* ↥L := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  have hunits : Fintype.card Kˣ = 1 := by rw [Fintype.card_units, hK]
  haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp hunits.le
  have hScal : CFSG.Open.StatedScalars (Fin 3) K = ⊥ := by
    rw [CFSG.Open.StatedScalars, MonoidHom.range_eq_bot_iff]
    ext x
    rw [Subsingleton.elim x 1, map_one]
    rfl
  have hScalSub : (CFSG.Open.StatedScalars (Fin 3) K).subgroupOf
      (CFSG.Open.StatedSL 3 K) = ⊥ := by
    rw [hScal, Subgroup.bot_subgroupOf]
  have ebot : CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) ≃*
      ↥(CFSG.Open.StatedSL 3 K) :=
    (QuotientGroup.quotientMulEquivOfEq hScalSub).trans QuotientGroup.quotientBot
  have hiso : ↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) :=
    (e.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)).trans
      ebot.symm
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega, by decide, by decide⟩
  have hcard : Nat.card K = 2 ^ 1 := by rw [Nat.card_eq_fintype_card, hK, pow_one]
  have hsc : CFSG.Open.StatedClassicalModel ↥L .PSL 3 2 1 :=
    ⟨hadm, K, inferInstance, inferInstance, hcard, ⟨hiso⟩⟩
  have hlie : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3 ↥L 1 := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3, CFSG.Blueprint.LieModel]
    exact Or.inl ⟨by decide, hsc⟩
  exact Or.inr (Or.inr (Or.inr ⟨hlie, hW⟩))

end CFSG.LocalAnalysis.WeakClosure81
