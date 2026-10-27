module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFLModel
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLLift
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLSp6
public import CFSG.RankThree.PartTwo.Sec21.HeringFFNormal
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr)

theorem exists_e9_normalizing_two_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : ∃ E V : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
      E ≤ Subgroup.normalizer (V : Set Y)) :
    ∃ E V : Subgroup Y', IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ V ≠ ⊥ ∧ IsPGroup 2 V ∧
      E ≤ Subgroup.normalizer (V : Set Y') := by
  obtain ⟨E, V, hE, hE9, hV, hV2, hEV⟩ := h
  refine ⟨E.map e.toMonoidHom, V.map e.toMonoidHom, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_,
    hV2.map _, (Subgroup.map_mono hEV).trans (Subgroup.le_normalizer_map _)⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    apply Subtype.ext
    have hc : (a' : Y) * b' = b' * a' :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul, ← map_mul, hc]
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, hE.2 y hy, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hE9
  · intro hbot
    exact hV ((Subgroup.map_eq_bot_iff_of_injective V e.injective).mp hbot)

theorem nonempty_mulEquiv_H6_of_stated {K : Type} [Group K]
    (hm : StatedClassicalModel K .PSp 3 2 1) : Nonempty (K ≃* H6) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : F ≃+* ZMod 2 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 1 one_pos hcard).trans
      (GaloisField.equivZmodP 2).toRingEquiv
  exact ⟨e.trans ((statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 3) (glCongr_statedScalars φ)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        CFSG.RankThree.PartTwo.Census.statedScalars_subgroupOf_sp6).trans
          QuotientGroup.quotientBot))⟩

theorem fFKE9_holds : FFKE9 := by
  intro X _ _ _ h3 hmod
  refine exists_e9_normalizing_two_of_quotient (Subgroup.center X) le_rfl h3 ?_
  rcases hmod with h4 | h5 | h6
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one h4
    exact exists_e9_normalizing_two_of_mulEquiv e.symm
      (Hering214.exists_e9_normalizing_two_projectiveSL hK (Or.inl rfl))
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Hering214.exists_mulEquiv_projectiveSL_of_psl_two_one h5
    exact exists_e9_normalizing_two_of_mulEquiv e.symm
      (Hering214.exists_e9_normalizing_two_projectiveSL hK (Or.inr rfl))
  · obtain ⟨e⟩ := nonempty_mulEquiv_H6_of_stated h6
    exact exists_e9_normalizing_two_of_mulEquiv e.symm
      CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.exists_e9_normalizing_two_H6

end CFSG.RankThree.PartTwo.Sec21
