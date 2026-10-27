module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeF4Three
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.AGLEmbeddingD2 CFSG.Open

theorem planeGen_outer_reeF4_three
    (hpair : SEITZRF.SubfieldPairReeF4Three) {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    {E : Subgroup (MulAut (Cat ⟨.reeF4 m, hv⟩))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hout : ¬ InnerPlane ⟨.reeF4 m, hv⟩ 3 E) : PlaneGen E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, _, _, _, hm1, hX, hsimple, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have hd : FieldAutData (ReeTag.F4.reeGamma X m) 3 :=
    SEITZRF.fieldAutData_reeF4_three hpair Nat.prime_three rfl hm1 hX
  have : Finite (ModGL ReeTag.F4.tag X) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma X m) := Subtype.finite
  have : IsSimpleGroup (ReeTag.F4.reeGamma X m) := MulEquiv.isSimpleGroup e.symm
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h'
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h' φ hφ).imp fun g hg => hg.symm
  have hnab : ∃ a b : ReeTag.F4.reeGamma X m, a * b ≠ b * a :=
    exists_noncommuting_of_isElementaryAbelian_aut hEi hc'
  have hclos := closure_fixUnion_eq_top_of_fieldAutData hnab Nat.prime_three hd
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  exact planeGen_of_outer_model e ((planeGen_iff_closure_fixUnion _).mpr hclos)

theorem seitzReeF4NoninnerTwo :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsReeF4Index d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, rfl, m, hd⟩
  subst hd
  exact planeGen_outer_reeF4_three SEITZRF.subfieldPairReeF4Three_holds hv hE hc hout

end CFSG.RankThree.PartTwo.Sec19
