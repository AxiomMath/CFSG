module

public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4G2Pair
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.LieType.SeitzGeneration.ExtSeitzBridge

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2
  CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.Open

theorem fieldAutData_G2_three
    (hpair : SubfieldPairG2EvenThree) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) : FieldAutData (adjointGroup .G2 K) 3 := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine fieldAutData_of_standard (MulAut.conj : adjointGroup .G2 K →* MulAut _).range
    {g | ∃ σ : K ≃+* K, orderOf σ = 3 ∧ g = entrywiseAdjointAut .G2 σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane Nat.prime_three hf hK E hEc
  · intro α hα
    obtain ⟨h0, σ, hσ, h⟩ := exists_conj_entrywise Nat.prime_three hf hK α hα
    refine ⟨(MulAut.conj h0)⁻¹, ?_, entrywiseAdjointAut .G2 σ, ⟨σ, hσ, rfl⟩, ?_⟩
    · exact (MulAut.conj : adjointGroup .G2 K →* MulAut _).range.inv_mem ⟨h0, rfl⟩
    · rw [← h]
      group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [fixedSubgroup_entrywise_eq, fixedSubgroup_entrywise_eq]
    exact g2Fixed_congr (fixedField_eq_of_orderOf Nat.prime_two (by omega) hK hσ hτ)
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    rw [fixedSubgroup_entrywise_eq] at hx hc
    exact eq_one_of_central_g2Fixed σ hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d ⟨g, rfl⟩ hne
    rw [fixedSubgroup_entrywise_eq] at hne ⊢
    exact Or.inl (hpair K ‹CharP K 2› σ hσ g hne)

theorem planeGen_outer_G2_three
    (hpair : SubfieldPairG2EvenThree) {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {E : Subgroup (MulAut (Cat ⟨.G2 q, hv⟩))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hout : ¬ InnerPlane ⟨.G2 q, hv⟩ 3 E) : PlaneGen E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hK, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have hf : 2 ≤ q.exponent := by
    have h3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rw [TauCeti.PrimePower.card_def, hq2] at h3
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [h1] at h3
    norm_num at h3
  have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def, hq2]
  have hd : FieldAutData (adjointGroup .G2 K) 3 := fieldAutData_G2_three hpair hf hK2
  obtain ⟨hfin, hsimple⟩ := finite_isSimpleGroup_cat_G2 hv
  have : Finite (adjointGroup .G2 K) := Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup (adjointGroup .G2 K) := MulEquiv.isSimpleGroup e.symm
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h'
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h' φ hφ).imp fun g hg => hg.symm
  have hnab : ∃ a b : adjointGroup .G2 K, a * b ≠ b * a :=
    exists_noncommuting_of_isElementaryAbelian_aut hEi hc'
  have hclos := closure_fixUnion_eq_top_of_fieldAutData hnab Nat.prime_three hd
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  exact planeGen_of_outer_model e ((planeGen_iff_closure_fixUnion _).mpr hclos)

theorem seitzG2NoninnerTwo :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsG2Index d.1 ∧
      d.1.characteristic = 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, rfl, ⟨q, hd⟩, hch⟩
  subst hd
  have hq2 : q.p = 2 := by
    simpa [TauCeti.LieTypeIndex.characteristic_G2] using hch
  exact planeGen_outer_G2_three subfieldPairG2EvenThree_holds hq2 hv hE hc hout

end CFSG.RankThree.PartTwo.Sec19
