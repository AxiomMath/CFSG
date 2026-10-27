module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitExcAux
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitExcAux3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover TableB TableBSymp NbrInnerRest

theorem ggWTSX_recipeChevalleyF4_weylTypeW
    {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false Q) :
    LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4,
    TableBF4.ggTorusLift_F4 hp hp2 (by rw [hK]; exact hpn), ggWTEx1_weylTypeW_F4_four hp hp2 K⟩

theorem ggWTSX_largeEvenLabelAll_weylTypeW_F4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTableBF4Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  exact ggWTSX_recipeChevalleyF4_weylTypeW hlab.1 hp hpn hQ

theorem ggWTSX_largeEvenLabelAll_weylTypeW_G2
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .G2)
    (hsp : GGNbrSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  have hX := TableBExc.largeEvenLabelAll_card_lt_G2 hp hlab ht (Or.inl ⟨hsp.1, hsp.2.2⟩)
  have hpn := hsp.2.2
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hpn
  subst ht
  intro Q hQ
  have hQ' := hX Q hQ
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq', hcard⟩ := hQ'
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, i1, i2, hK, hq', _,
    TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .G2 K)
      (TableBExc.ggTorusLift_adjoint (τ := .G2) (by decide) hp hp2 hpq
        (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_G2 (Nat.coprime_one_left p))),
    ggWTSX_weylTypeW_of_card_lt hcard⟩

theorem ggWTSX_recipeChevalleyExc_weylTypeW
    {τ : Tag} {n p : ℕ}
    (hτ : (τ = .E6 ∧ p ≠ 3) ∨ τ = .E7 ∨ τ = .E8) (hn : 1 ≤ n) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley τ.cartan (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  rcases hτ with ⟨rfl, hp3⟩ | rfl | rfl
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 6, TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq,
      ggWTSX_weylTypeW_E6 hp hp2 hp3 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 7, TableBExc.ggTorusLift_E7 hp hp2 hpq,
      ggWTSX_weylTypeW_E7 hp hp2 hpq⟩
  · exact ⟨K, inferInstance, inferInstance, hK, hQ, 8, TableBExc.ggTorusLift_E8 hp hp2 hpq,
      ggWTSX_weylTypeW_E8 hp hp2 hpq⟩

theorem ggWTSX_largeEvenLabelAll_weylTypeW_excSplit
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTableBNbrInnerExcSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with ⟨ht, hp3⟩ | ht | ht <;> dsimp only at ht hpn <;> subst ht
  · exact ggWTSX_recipeChevalleyExc_weylTypeW (Or.inl ⟨rfl, hp3⟩) hn hp hpn hQ
  · exact ggWTSX_recipeChevalleyExc_weylTypeW (Or.inr (Or.inl rfl)) hn hp hpn hQ
  · exact ggWTSX_recipeChevalleyExc_weylTypeW (Or.inr (Or.inr rfl)) hn hp hpn hQ

end CFSG.StandardType

end
