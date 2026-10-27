module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUDvd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusNoLine_of_noInvariantLineSCr {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGNoInvariantLineSCr p r R I) : GGTorusNoLine p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  obtain ⟨W, hW1, hW2⟩ := h L' ψ hψ hker hperf A hA hAI hr h3 hsc
  refine ⟨W, hW1, fun _ a₀ ha₀ ha₁ => ?_⟩
  have := Fact.mk hp
  have hz : Subgroup.zpowers a₀ ≤ A := Subgroup.zpowers_le.mpr ha₀
  have hord : orderOf a₀ = p := orderOf_eq_prime (hA.2 a₀ ha₀) ha₁
  have hcard : Nat.card (Subgroup.zpowers a₀) = p := by rw [Nat.card_zpowers, hord]
  obtain ⟨n, hn, e, he, hne⟩ := hW2 _ hz hcard
  refine ⟨n, hn, fun hmem => hne ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hmem k

section Main

theorem largeEvenLabelAll_torusLift_noLine_unitDvd {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvdLabelNo63 p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNoLine p r R I :=
  (largeEvenLabelAll_unitDvd_line LineU.unitaryUniversalCover hp hlab h).mono
    fun _ _ _ _ ⟨r, hl, hT⟩ => ⟨r, hl, ggTorusNoLine_of_noInvariantLineSCr hp hT⟩

theorem ggNbrInnerWeylOn_unitDvd : GGNbrInnerWeylOn GGNbrWeylUnitDvdLabel :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨hpow, ht, h3, hpq, hpd, h63⟩ =>
    largeEvenLabelAll_weylInnerKLevel_of_noLine
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      (largeEvenLabelAll_torusLift_noLine_unitDvd hp hlab ⟨⟨ht, h3, hpq, hpd⟩, h63⟩)

end Main

end CFSG.StandardType

end
