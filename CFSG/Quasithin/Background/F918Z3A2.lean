module

public import CFSG.Quasithin.Background.F918Z3A2Sec
public import CFSG.Quasithin.Background.F918J4
public import CFSG.Quasithin.Background.SmithB45SzRow

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

theorem caseII_shape (h45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) {V : Type} [CommGroup V] [Finite V] (hexp : ∀ v : V, v ^ 2 = 1)
    {D : Subgroup (MulAut V)} (hsimp : IsSimpleGroup ↥D) (hnonab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a)
    (htype : A38Types ↥D) (hsqtk : SQTKGroup ↥D)
    {A : Subgroup (MulAut V)} (hA2 : IsPGroup 2 ↥A) (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D)
    {I : Subgroup V} (hI : I ≠ ⊥) (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I)
    (hIA : ∀ a ∈ A, ∀ v ∈ I, a v ∈ I) (hnt : ∃ y ∈ D, ∃ v ∈ I, y v ≠ v)
    (hq : qhatOf (autSub (D ⊔ A) I) < ((2 : ℚ) : WithTop ℚ)) :
    (∃ n, 2 ≤ n ∧ BinaryNaturalSL (autSub D I) ⊤ ⊥ 2 n) ∨ BinaryNaturalSL (autSub D I) ⊤ ⊥ 3 1 ∨
      AlternatingNatural (autSub D I) ⊤ ⊥ 5 ∨
      (∃ m, 1 ≤ m ∧ BinaryOrthogonalFour (autSub D I) ⊤ ⊥ m) := by
  have hQ := CaseIISec.qsec hsimp hnonab hA2 hAD hI hID hImin hIA hnt
  obtain ⟨e⟩ := CaseIISec.equiv hsimp hID hnt
  have : IsSimpleGroup ↥(autSub D I) := e.symm.isSimpleGroup
  have hS : SQTKGroup ↥(autSub D I) := B5.sqtk_of_mulEquiv e.symm hsqtk
  have hAK : A38Types ↥(autSub D I) := a38Types_congr e htype
  have hexp' : ∀ u : ↥I, u ^ 2 = 1 := fun u => Subtype.ext (hexp u)
  obtain ⟨-, hmods⟩ := insp5a_rows h45 hF hX hexp' hQ hS hq.le hAK
  rcases hmods with (⟨n, hn, h⟩ | h | h) | (⟨m, hm, h⟩ | ⟨f, h⟩)
  · exact Or.inl ⟨n, hn, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨m, hm, h⟩))
  · exfalso
    have hqq := (B45Sz.qOf_qhatOf_eq_two hQ.le
      (fun x hx => CaseIISec.mem_normalizer_of_normal hQ.normal hx) h).2
    rw [hqq] at hq
    exact lt_irrefl _ hq

end CFSG.Quasithin
