module

public import CFSG.Quasithin.Background.F918N3
public import CFSG.Quasithin.Background.F918N5
public import CFSG.Quasithin.Background.F918N6
public import CFSG.Quasithin.Background.F918N8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Final

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

theorem z35_final (hB42 : AsB42) (hA21 : AsA21SQTKSection) (i3 : D35InspUniq) (i4 : D35InspB42)
    (h : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {A : Subgroup (MulAut X)}
    (hAQ : A ∈ QhatStar (Mb ⊔ Tb)) (hAT : A ≤ Tb) (hAV : A ≤ stabSub Vb)
    (hfaith : ∀ a ∈ A, (∀ w ∈ Vb, a w = w) → a = 1)
    (hr : Nat.card ↥Vb ≤ Nat.card A * Nat.card ↥(Vb ⊓ fixV A)) : Z35Concl Mb Tb Lb Vb := by
  obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hAQ
  obtain ⟨A', hA'A, -, hb42⟩ := z35_b42 hB42 hA21 h hML hAT hAV hA2.2.2 hA2.2.1 hfaith hr
  have hA'T : A' ≤ Tb ⊓ stabSub Vb := le_inf (hA'A.trans hAT) (hA'A.trans hAV)
  obtain ⟨hidx, hb⟩ := i4 X Mb Tb Lb Vb A' h hML hA'T hb42
  have hnot := z35_not_le_stab h
  have h4 := z35_four h hidx
  refine ⟨hML, h4.1, h4.2, ?_⟩
  rcases hb hnot with h5 | h8 | h11
  · exact h5
  · exact (z35_elim i3 h hML hAQ hAT hAV hidx (z35_faithful_orbit h hAT hA2.2.2)
      ⟨A', Or.inl h8⟩).elim
  · exact (z35_elim i3 h hML hAQ hAT hAV hidx (z35_faithful_orbit h hAT hA2.2.2)
      ⟨A', Or.inr h11⟩).elim

end Final

theorem z35Main_of_inputs (hB42 : AsB42) (hB51 : AsB51) (hB56 : AsB56) (hA21 : AsA21SQTKSection)
    (i1 : D35InspTwo) (i2 : D35InspSum) (i3 : D35InspUniq) (i4 : D35InspB42) : Z35Main := by
  intro X _ _ Mb Tb Lb Vb h
  obtain ⟨A, hAQ, hAT, hfaith, hr⟩ := z35_offender h
  obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hAQ
  obtain ⟨hML, hAV⟩ := z35_stab hB56 hB51 hA21 i1 i2 h hAT hA2.2.2 hA2.2.1 hfaith hr
  have hO : orbSup A Vb = Vb := orbSup_eq_of_stab (fun a ha => hAV ha)
  rw [hO] at hfaith hr
  exact z35_final hB42 hA21 i3 i4 h hML hAQ hAT hAV hfaith hr

theorem d35_of_inputs (hB42 : AsB42) (hB51 : AsB51) (hB56 : AsB56) (hA21 : AsA21SQTKSection)
    (hNC : AsA36NoOddCover) (i1 : D35InspTwo) (i2 : D35InspSum) (i3 : D35InspUniq)
    (i4 : D35InspB42) : D35 :=
  d35_of_z35Main (z35Main_of_inputs hB42 hB51 hB56 hA21 i1 i2 i3 i4) hA21 hNC

end CFSG.Quasithin
