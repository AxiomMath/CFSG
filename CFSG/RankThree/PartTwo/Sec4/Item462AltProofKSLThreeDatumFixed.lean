module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumDef
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFixed

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

theorem fixedDatum_of_noncyclicDatum {S : Type} [Group S] {β' : MulAut S}
    (h : NoncyclicDatum β') : FixedDatum (fixedSub β') := by
  obtain ⟨R, P, hPR, hP2, hPnc, hRs, hfix, hnorm, -, -⟩ := h
  have hRF : R ≤ fixedSub β' := fun r hr => hfix r hr
  have hPF : P ≤ fixedSub β' := hPR.trans hRF
  let eP : P.subgroupOf (fixedSub β') ≃* P := Subgroup.subgroupOfEquivOfLe hPF
  let eR : R.subgroupOf (fixedSub β') ≃* R := Subgroup.subgroupOfEquivOfLe hRF
  refine ⟨R.subgroupOf (fixedSub β'), P.subgroupOf (fixedSub β'), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hPR hx
  · exact IsPGroup.of_surjective hP2 eP.symm.toMonoidHom eP.symm.surjective
  · exact fun hc => hPnc (eP.isCyclic.mp hc)
  · exact Group.isSolvable_of_isSolvable_injective (f := eR.toMonoidHom) eR.injective
  · intro c r hr
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    exact hnorm _ c.2 _ hr

theorem fixedDatumZ_of_noncyclicDatum {S : Type} [Group S] [Finite S]
    (hZS : Nat.card (Subgroup.center S) = 3) {β' : MulAut S} (hβ' : β' ^ 3 = 1)
    (hZF : Nat.card (Subgroup.center (fixedSub β')) = 3) (h : NoncyclicDatum β') :
    FixedDatumZ (fixedSub β') := by
  obtain ⟨R, P, hPR, hP2, hPnc, hRs, hfix, hnorm, hZR, h9⟩ := h
  have hRF : R ≤ fixedSub β' := fun r hr => hfix r hr
  have hZc : ∀ z ∈ Subgroup.center S, β' z = z := fixed_center_of_cube hZS hβ'
  have hZF' : Subgroup.center S ≤ fixedSub β' := fun z hz => hZc z hz
  haveI : Finite (Subgroup.center (fixedSub β')) :=
    Nat.finite_of_card_ne_zero (by rw [hZF]; norm_num)
  have hle : (Subgroup.center S).subgroupOf (fixedSub β') ≤ Subgroup.center (fixedSub β') := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz c)
  have hcardZ : Nat.card ((Subgroup.center S).subgroupOf (fixedSub β')) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZF').toEquiv, hZS]
  have heq : (Subgroup.center S).subgroupOf (fixedSub β') = Subgroup.center (fixedSub β') :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZF, hcardZ])
  refine ⟨R.subgroupOf (fixedSub β'), P.subgroupOf (fixedSub β'), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hPR hx
  · exact IsPGroup.of_surjective hP2 (Subgroup.subgroupOfEquivOfLe (hPR.trans hRF)).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (hPR.trans hRF)).symm.surjective
  · exact fun hc => hPnc ((Subgroup.subgroupOfEquivOfLe (hPR.trans hRF)).isCyclic.mp hc)
  · exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRF).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRF).injective
  · intro c r hr
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    exact hnorm _ c.2 _ hr
  · intro z hz
    rw [← heq, Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_subgroupOf]
    exact hZR hz
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv]
    exact h9

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
