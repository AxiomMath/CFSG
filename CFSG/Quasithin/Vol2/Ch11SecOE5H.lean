module

public import CFSG.Quasithin.Vol2.Ch11SecOE5E
public import CFSG.Quasithin.Vol2.Ch11SecOE5G
public import CFSG.Quasithin.Vol2.Ch11SecO11G
public import CFSG.Quasithin.Vol2.Ch11SecO11D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.HNB CFSG.Assembly.LowTwoRank

theorem OE5.l24Unique_PS0 : O11.L24Unique (OE5.S0.map (unitaryProj OE5.hF25 3)) :=
  OE5.l24Unique_of_data OE5.isSylowTwoOf_PS0 OE5.card_PS0 OE5.card_psu35
    (fun _ hx => OE5.projInvT_central hx) (fun _ hy hc => OE5.eq_of_central_PS0 hy hc)
    (OE5.card_centralizer_projInvT_le OE5.hF25)

theorem OE5.l24Unique_psu {Q : Type} [Group Q] [Finite Q] (hQ : IsPSU 3 5 1 Q) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : O11.L24Unique S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hQ
  have := Fintype.ofFinite K
  have eKF : K ≃+* F25 :=
    FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK,
      ← Nat.card_eq_fintype_card, F25.card]; norm_num)
  have φ : Q ≃* unitaryPSU OE5.hF25 3 :=
    e.trans ((OE5.statedProjSUEquiv eKF 3 (5 ^ 1)).trans
      (unitaryPSUEquiv OE5.hF25 (by norm_num)).symm)
  exact O11.l24Unique_of_equiv OE5.isSylowTwoOf_PS0 OE5.l24Unique_PS0 ⟨φ⟩ hS

theorem OE5.l24Unique_su {Q : Type} [Group Q] [Finite Q] (hQ : IsSU3 5 Q) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : O11.L24Unique S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hQ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = (5 ^ 1) ^ 2 := by rw [hK]; norm_num
  have : CharP K 5 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  have hU : UnitaryFieldData 5 1 K := ⟨Nat.prime_five, le_rfl, by rw [hK]⟩
  have hZ : Subgroup.center ↥(StatedSU 3 5 K) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 5 K) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 5) (f := 1)
      hK' le_rfl (by norm_num)).2
  let e₂ : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSU 3 5 K) :=
    QuotientGroup.congr _ _ e (by rw [Subgroup.map_center_eq e, hZ])
  have hZ3 : Nat.card (Subgroup.center Q) = 3 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center Q)
      (e : Q →* ↥(StatedSU 3 5 K)) e.injective).toEquiv, Subgroup.map_center_eq e, hZ]
    show Nat.card ↥((StatedScalars (Fin 3) K).subgroupOf (unitarySU 5 1 K 3)) = 3
    rw [← unitaryScalars_eq hU (by norm_num : 1 ≤ 3), card_unitaryScalars hU (by norm_num)]
    decide
  have hQZ : IsPSU 3 5 1 (Q ⧸ Subgroup.center Q) :=
    ⟨⟨Nat.prime_five, le_rfl, le_rfl, by decide⟩, K, inferInstance, inferInstance, hK', ⟨e₂⟩⟩
  refine O11.l24Unique_of_quot_center (by rw [hZ3]; decide) ?_
  exact OE5.l24Unique_psu hQZ
    (isSylowTwoOf_top_map_of_surjective hS _ (QuotientGroup.mk'_surjective _))

theorem factU35UniqueL24_holds : FactU35UniqueL24 := by
  intro Q _ _ hQ S hS B₁ B₂ h₁ h₂
  rcases hQ with hQ | hQ
  · exact OE5.l24Unique_su hQ hS B₁ B₂ h₁ h₂
  · exact OE5.l24Unique_psu hQ hS B₁ B₂ h₁ h₂

end CFSG.Quasithin.Vol2.Ch11.SecS
