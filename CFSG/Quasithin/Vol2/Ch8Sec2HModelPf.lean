module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsB
public import CFSG.Quasithin.Background.HModelType
public import CFSG.Quasithin.Background.E2TwoLieQuotBlocks

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H.ModelType

theorem hType82_holds :
    HType82 := fun _ _ _ _ =>
  ⟨isPSL_of_binaryNine, isSporadic_m22_of_code22,
    fun h => h.elim isSporadic_m24_of_code24 isSporadic_m24_of_cocode24⟩

theorem hCent82_holds :
    HCent82 := by
  intro V _ _ H h
  rcases h with h | h | h | h
  · exact centralizer_eq_bot_of_binaryNine h
  · exact centralizer_eq_bot_of_code22 h
  · exact centralizer_eq_bot_of_code24 h
  · exact centralizer_eq_bot_of_cocode24 h

theorem isSimpleGroup_and_noncomm_of_equiv {X Y : Type} [Group X] [Group Y] [Finite Y]
    [IsSimpleGroup Y] (e : X ≃* Y) (h2 : 2 ∣ Nat.card Y) (hgt : 2 < Nat.card Y) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hs : IsSimpleGroup X := e.isSimpleGroup
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hc : Nat.card X = Nat.card Y := Nat.card_congr e.toEquiv
  exact ⟨hs, E2.exists_noncomm_of_isSimpleGroup (hc ▸ h2) (hc ▸ hgt)⟩

theorem hSimple82_holds :
    HSimple82 := by
  intro V _ _ H h
  rcases h with h | h | h | h
  · have hp := isPSL_of_binaryNine h
    have := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hp).2
    have : Finite ↥H := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hp
    have hc : Nat.card ↥H = 20160 := by
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hp).1 rfl]
      decide
    exact isSimpleGroup_and_noncomm_of_equiv (MulEquiv.refl ↥H) (by rw [hc]; norm_num)
      (by rw [hc]; norm_num)
  · obtain ⟨e⟩ := isSporadic_m22_of_code22 h
    have e' : ↥H ≃* CFSG.Blueprint.NativeSporadic.M22 := e
    have := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).1
    have := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
    exact isSimpleGroup_and_noncomm_of_equiv e'
      (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num)
      (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num)
  · obtain ⟨e⟩ := isSporadic_m24_of_code24 h
    have e' : ↥H ≃* CFSG.Blueprint.NativeSporadic.M24 := e
    have := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).1
    have := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
    exact isSimpleGroup_and_noncomm_of_equiv e'
      (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
      (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
  · obtain ⟨e⟩ := isSporadic_m24_of_cocode24 h
    have e' : ↥H ≃* CFSG.Blueprint.NativeSporadic.M24 := e
    have := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).1
    have := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
    exact isSimpleGroup_and_noncomm_of_equiv e'
      (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
      (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)

end CFSG.Quasithin.H13
