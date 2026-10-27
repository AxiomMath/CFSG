module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeCornerOp
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeCornerOrder
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumDef
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4

theorem false_of_fixedDatumZ_su32 {K₀ : Type} [Field K₀] (hK₀ : PiField false 2 1 K₀)
    {F : Type} [Group F] (e : F ≃* slPi false 3 (2 ^ 1) K₀) (h : FixedDatumZ F) : False := by
  obtain ⟨R, P, hPR, hP2, hPnc, hRs, hRn, hZR, h9⟩ := h
  haveI := hK₀.finite
  have hq : ModThree false (2 ^ 1) := by
    change 2 ^ 1 % 3 = 2
    norm_num
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K₀ := hK₀.unitary
  have hC : Nat.card (slPi false 3 (2 ^ 1) K₀) = 216 :=
    CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
  have hZ : Nat.card (Subgroup.center (slPi false 3 (2 ^ 1) K₀)) = 3 :=
    KFacts.card_center_slPi hK₀ hq
  have hO2 : ∀ N : Subgroup (slPi false 3 (2 ^ 1) K₀), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hN h2 => eq_bot_of_normal_isPGroup hK₀ hq N h2
  let eP : P ≃* P.map e.toMonoidHom := Subgroup.equivMapOfInjective P e.toMonoidHom e.injective
  have hP' : P.map e.toMonoidHom = ⊥ := by
    refine eq_bot_of_datum_order_216 hC hZ hO2 (Subgroup.map_mono hPR) ?_ ?_ ?_
      (IsPGroup.of_surjective hP2 eP.toMonoidHom eP.surjective)
    · intro c r' hr'
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hr'
      refine Subgroup.mem_map.mpr ⟨e.symm c * r * (e.symm c)⁻¹, hRn _ r hr, ?_⟩
      simp
    · intro z hz
      have hz' : e.symm z ∈ Subgroup.center F := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro g
        apply e.injective
        simpa using hz (e g)
      exact Subgroup.mem_map.mpr ⟨e.symm z, hZR hz', by simp⟩
    · rw [Subgroup.card_map_of_injective e.injective]
      exact h9
  have hPb : P = ⊥ := (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) P e.injective).mp hP'
  apply hPnc
  rw [hPb]
  infer_instance

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
