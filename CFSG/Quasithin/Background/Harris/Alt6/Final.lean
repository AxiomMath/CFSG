module

public import CFSG.Quasithin.Background.Harris.Alt6.Setup
public import CFSG.Quasithin.Background.Harris.Alt6.Module
public import CFSG.Quasithin.Background.Harris.Alt6.Form
public import CFSG.Quasithin.Background.Harris.Alt6.SpNatural
public import CFSG.Quasithin.Background.Harris.Alt6.End

public section

namespace CFSG.Quasithin.G11.Harris.Alt6

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspSp Equiv
  CFSG.CharacterTheory.SteinbergBY AlternatingSix

theorem oneCompFor_famAlt6 : OneCompFor (FamAlt 6) := by
  rintro V _ _ _ Γ A L m hs ⟨-, ⟨e⟩⟩
  have hm : m ≤ 3 := m_le_three hs e
  have hb := hs.bound
  obtain ⟨hd4, T, hT⟩ := exists_heart_equiv hs.L_irr e (by omega)
  have hsymp := transportForm_isSymplectic T
  have hLB : L ≤ spSub (transportForm T) := by
    rcases hT with hT | hT
    · exact transportForm_invariant T (fun l => (e l : Perm (Fin 6))) hT
    · exact transportForm_invariant T (fun l => totalPermHom (e l : Perm (Fin 6))) hT
  have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  have hperf : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have hcard : Nat.card L = 360 := (Nat.card_congr e.toEquiv).trans card_alt_six
  have hcomm := (eq_commutator_spSub hsymp (hd4.trans rfl) hLB (Subgroup.isPerfect_iff.1 hperf)
    hcard).1
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨1, ⟨le_rfl, by omega, by omega, by omega, isNatural_of_symplectic hsymp hd4 hcomm,
      fun _ => permCore_of_symplectic hsymp hd4 hLB hs.L_irr hperf hcard⟩,
      endIsField_one hs.L_irr e T hT,
      selfDual_of_invariant_form (p4inspsp_nondeg hsymp) fun l hl x y => hLB hl x y⟩)))))))))

end CFSG.Quasithin.G11.Harris.Alt6
