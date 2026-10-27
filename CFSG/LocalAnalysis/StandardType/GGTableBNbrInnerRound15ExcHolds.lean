module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRound15Label
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSCr
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerClassicalModel
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlus
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusHolds
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerIrredF4
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerIrredE7
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerIrredE8
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerIrredTwE6Dvd
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOfIrredSCr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Round15Exc

private def RowF4 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n + 1

private def RowE78 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ∣ 2 ^ lab.n + 1

private def RowTwE6Dvd (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n - 1

private def RowTwE6Add (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n + 1

private theorem two_ne_of_dvd_two_pow_add_one {p n : ℕ} (hn : 1 ≤ n) (h : p ∣ 2 ^ n + 1) :
    p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  omega

private theorem two_ne_of_dvd_two_pow_sub_one {p n : ℕ} (hn : 1 ≤ n) (h : p ∣ 2 ^ n - 1) :
    p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

private theorem round15_rows {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTableBNbrInnerRound15ExcLabel p lab) :
    RowF4 p lab ∨ RowE78 p lab ∨ RowTwE6Dvd p lab ∨ RowTwE6Add p lab := by
  obtain ⟨⟨⟨_, hrow⟩, hno⟩, hE6, hT6⟩ := h
  rcases hrow with ⟨hF, hd⟩ | ⟨ht, hp3, hd⟩ | ⟨ht, hd⟩ | hU
  · rcases hF with hF | hF | hF
    · exact Or.inl ⟨hF, fun hp3 => hno (Or.inl ⟨hF, hp3, hd⟩), hd⟩
    · exact Or.inr (Or.inl ⟨Or.inl hF,
        fun hp3 => hno (Or.inr (Or.inl ⟨Or.inl hF, Or.inl hp3, hd⟩)),
        fun hp5 => hno (Or.inr (Or.inl ⟨Or.inl hF, Or.inr hp5, hd⟩)), hd⟩)
    · exact Or.inr (Or.inl ⟨Or.inr hF,
        fun hp3 => hno (Or.inr (Or.inl ⟨Or.inr hF, Or.inl hp3, hd⟩)),
        fun hp5 => hno (Or.inr (Or.inl ⟨Or.inr hF, Or.inr hp5, hd⟩)), hd⟩)
  · exact absurd ⟨ht, hp3, hd⟩ hE6
  · rcases hd with hd | hd
    · exact Or.inr (Or.inr (Or.inl ⟨ht,
        fun hp3 => hno (Or.inr (Or.inr (Or.inl ⟨ht, hp3, hd⟩))), hd⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ht, fun hp3 => hT6 ⟨ht, hp3, hp3 ▸ hd⟩, hd⟩))
  · exact absurd hU (fun hU => hno (Or.inr (Or.inr (Or.inr hU))))

private theorem round15_of_rows (h1 : GGTableBNbrInnerInputOn RowF4)
    (h2 : GGTableBNbrInnerInputOn RowE78) (h3 : GGTableBNbrInnerInputOn RowTwE6Dvd)
    (h4 : GGTableBNbrInnerInputOn RowTwE6Add) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound15ExcLabel :=
  GGTableBNbrInnerInputOn.mono (fun _ _ h => round15_rows h) (h1.or (h2.or (h3.or h4)))

private theorem rowF4_input :
    GGTableBNbrInnerInputOn RowF4 := by
  refine ggTableBNbrInnerInputOn_of_labelsSCr fun p lab hp hlab hrow => ?_
  obtain ⟨htag, hp3, hpn⟩ := hrow
  have hp2 : p ≠ 2 := two_ne_of_dvd_two_pow_add_one hlab.1 hpn
  have hlift := largeEvenLabelAll_torusLift_excPlus hp hp2 (lab := lab)
    ⟨Or.inr (Or.inr htag), hpn⟩
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hlift
  subst htag
  have hnbr : LargeEvenLabelAll ⟨.F4, l, n⟩ fun R _ I _ => GGTorusNbrSCr p 3 R I := by
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusNbrSCr_of_scWeylIrred hp
      (TableBF4.center_recipeGroup_eq_bot K) (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ)
      (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2) (ggSCWeylIrred_F4Plus_largePrime hp hp3 hpq)⟩
  exact (largeEvenLabelAll_and hlift hnbr).mono fun _ _ _ _ ⟨hl, hn⟩ => ⟨3, hl, hn⟩

private theorem rowE78_input :
    GGTableBNbrInnerInputOn RowE78 := by
  refine ggTableBNbrInnerInputOn_of_labelsSCr fun p lab hp hlab hrow => ?_
  obtain ⟨htag, hp3, hp5, hpn⟩ := hrow
  have hp2 : p ≠ 2 := two_ne_of_dvd_two_pow_add_one hlab.1 hpn
  have hlift := largeEvenLabelAll_torusLift_excPlus hp hp2 (lab := lab)
    ⟨htag.elim Or.inl fun h => Or.inr (Or.inl h), hpn⟩
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hlift
  rcases htag with rfl | rfl
  · have hnbr : LargeEvenLabelAll ⟨.E7, l, n⟩ fun R _ I _ => GGTorusNbrSCr p 6 R I := by
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card hK
      have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
      exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusNbrSCr_of_scWeylIrred hp
        (TableBExc.center_recipeGroup_eq_bot .E7 K)
        (fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
        (ExcSplitL.ggCenterPrime_recipe_E7 (f := n) hlab.1 hK hp hp2)
        (ggSCWeylIrred_E7Plus_largePrime hp hp3 hp5 hpq)⟩
    exact (largeEvenLabelAll_and hlift hnbr).mono fun _ _ _ _ ⟨hl, hn⟩ => ⟨6, hl, hn⟩
  · have hnbr : LargeEvenLabelAll ⟨.E8, l, n⟩ fun R _ I _ => GGTorusNbrSCr p 7 R I := by
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card hK
      have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
      exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusNbrSCr_of_scWeylIrred hp
        (TableBExc.center_recipeGroup_eq_bot .E8 K)
        (fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
        (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2)
        (ggSCWeylIrred_E8Plus_largePrime hp hp3 hp5 hpq)⟩
    exact (largeEvenLabelAll_and hlift hnbr).mono fun _ _ _ _ ⟨hl, hn⟩ => ⟨7, hl, hn⟩

private theorem rowTwE6Dvd_input :
    GGTableBNbrInnerInputOn RowTwE6Dvd := by
  refine ggTableBNbrInnerInputOn_of_labelsSCr fun p lab hp hlab hrow => ?_
  obtain ⟨ht, hp3, hpn⟩ := hrow
  have hp2 : p ≠ 2 := two_ne_of_dvd_two_pow_sub_one hlab.1 hpn
  have hlift := largeEvenLabelAll_torusLift_twE6Dvd hp hp2 hlab ⟨ht, hpn⟩
  have hnbr : LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSCr p 4 R I :=
    TwE6Delta.labelAll ht fun K _ _ hK =>
      ggTorusNbrSCr_of_scWeylIrred hp (TwE6Delta.center_recipeR_eq_bot hlab.1 hK)
        (fun φ hφ hφp => TwE6Delta.ggOutdiagPrime_twE6 hlab.1 hK hp hp3 φ hφ hφp)
        (TwE6Delta.ggCenterPrime_twE6 hlab.1 hK hp hp2 hp3)
        (ggSCWeylIrred_twE6Dvd_largePrime hlab.1 hK hp hp3 hpn)
  exact (largeEvenLabelAll_and hlift hnbr).mono fun _ _ _ _ ⟨hl, hn⟩ => ⟨4, hl, hn⟩

private theorem rowTwE6Add_input :
    GGTableBNbrInnerInputOn RowTwE6Add := by
  refine ggTableBNbrInnerInputOn_of_labelsSCr fun p lab hp hlab hrow => ?_
  obtain ⟨ht, hp3, hpn⟩ := hrow
  have hp2 : p ≠ 2 := two_ne_of_dvd_two_pow_add_one hlab.1 hpn
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := fun h => by subst h; exact absurd hp (by norm_num)
    omega
  have hr : TwE6Delta.liftRank p = 5 := if_neg hp3
  have hlift := largeEvenLabelAll_torusLift_twE6Add hp hlab ⟨ht, hpn⟩
  rw [hr] at hlift
  have hnbr : LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSCr p 5 R I :=
    TwE6Delta.labelAll ht fun K _ _ hK =>
      haveI := Fact.mk hp
      ggTorusNbrSCr_of_ggTorusIrredSCr hp (TwE6TB.ggTorusIrredSCr_of_modelSCr hp5
        (ggTwE6TorusModelInput_holds K lab.n p hlab.1 hK hp hpn hp5))
  exact (largeEvenLabelAll_and hlift hnbr).mono fun _ _ _ _ ⟨hl, hn⟩ => ⟨5, hl, hn⟩

theorem ggTableBNbrInnerInputOn_round15Exc_holds :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound15ExcLabel :=
  round15_of_rows rowF4_input rowE78_input rowTwE6Dvd_input rowTwE6Add_input

end Round15Exc

end CFSG.StandardType

end
