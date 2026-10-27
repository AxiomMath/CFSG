module

public import CFSG.LocalAnalysis.StandardType.SpSixSylowOvergroup
public import CFSG.LocalAnalysis.StandardType.UFourTwoSylowFive
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcGenuine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalInSitu
public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSp6
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.StandardType

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.Blueprint CFSG.StandardType.UFourTwoSylow CFSG.StandardType.SpSixSylow

namespace SpSixOvergroup

@[expose] def UFourTwoLike (A : Type) [Group A] : Prop :=
  Group.IsSolvable A ∨ (IsSimpleGroup ↥(commutator A) ∧ LieModel ↥(commutator A) .PSU 4 2 1)

theorem UFourTwoLike.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : UFourTwoLike A) : UFourTwoLike B := by
  rcases h with h | ⟨hs, hl⟩
  · exact Or.inl (SylowOvergroup.isSolvable_of_mulEquiv e.symm h)
  · haveI := hs
    let c := SylowOvergroup.commutatorEquiv e
    exact Or.inr ⟨c.symm.isSimpleGroup, LieModel.of_mulEquiv c hl⟩

theorem uFourTwoLike_of_commutator_equiv
    {A : Type} [Group A] (c : ↥(commutator A) ≃* ↥V0) : UFourTwoLike A := by
  obtain ⟨e⟩ := nonempty_V0_mulEquiv_catGroup
  haveI := isSimpleGroup_V0
  exact Or.inr ⟨c.isSimpleGroup, LieModel.of_mulEquiv (c.trans e).symm lieModel_u42⟩

theorem commutator_W0_eq :
    commutator ↥W0 = V0.subgroupOf W0 := by
  haveI : (V0.subgroupOf W0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer V0_le_W0).2 W0_le_normalizer_V0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hcard : Nat.card (↥W0 ⧸ V0.subgroupOf W0) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact relIndex_V0_W0
    haveI : IsCyclic (↥W0 ⧸ V0.subgroupOf W0) := isCyclic_of_prime_card hcard
    have h := Abelianization.commutator_subset_ker (QuotientGroup.mk' (V0.subgroupOf W0))
    rwa [QuotientGroup.ker_mk'] at h
  · have h1 : (commutator ↥V0).map (Subgroup.inclusion V0_le_W0) ≤ commutator ↥W0 := by
      rw [commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    rw [commutator_V0_eq_top, Subgroup.map_top, Subgroup.inclusion_range] at h1
    exact h1

theorem uFourTwoLike_V0 :
    UFourTwoLike ↥V0 :=
  uFourTwoLike_of_commutator_equiv
    ((MulEquiv.subgroupCongr commutator_V0_eq_top).trans Subgroup.topEquiv)

theorem uFourTwoLike_W0 :
    UFourTwoLike ↥W0 :=
  uFourTwoLike_of_commutator_equiv
    ((MulEquiv.subgroupCongr commutator_W0_eq).trans (Subgroup.subgroupOfEquivOfLe V0_le_W0))

theorem uFourTwoLike_of_le_W0
    {Y : Subgroup H6} (hT : T0 ≤ Y) (hYW : Y ≤ W0) : UFourTwoLike ↥Y := by
  by_cases hV : V0 ≤ Y
  · have hcard : Nat.card V0 = Nat.card Y ∨ Nat.card Y = Nat.card W0 := by
      have h1 : Nat.card V0 ∣ Nat.card Y := Subgroup.card_dvd_of_le hV
      have h2 : Nat.card Y ∣ Nat.card W0 := Subgroup.card_dvd_of_le hYW
      rw [card_V0] at h1 ⊢
      rw [card_W0] at h2 ⊢
      obtain ⟨k, hk⟩ := h1
      rw [hk] at h2 ⊢
      have hk2 : k ∣ 2 := by
        have : 25920 * k ∣ 25920 * 2 := by simpa using h2
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
      · left
        norm_num
      · right
        norm_num
    rcases hcard with h | h
    · have hY : V0 = Y := Subgroup.eq_of_le_of_card_ge hV h.ge
      rw [← hY]
      exact uFourTwoLike_V0
    · have hY : Y = W0 := Subgroup.eq_of_le_of_card_ge hYW h.ge
      rw [hY]
      exact uFourTwoLike_W0
  · left
    haveI : (V0.subgroupOf W0).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer V0_le_W0).2 W0_le_normalizer_V0
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hN : Group.IsSolvable ↥(Y ⊓ V0) :=
      isSolvable_of_le_V0 (le_inf hT T0_le_V0) inf_le_right fun h =>
        hV (h.symm.le.trans inf_le_left)
    have hcard : Nat.card (↥W0 ⧸ V0.subgroupOf W0) = 2 := by
      rw [← Subgroup.index_eq_card]
      exact relIndex_V0_W0
    haveI : IsCyclic (↥W0 ⧸ V0.subgroupOf W0) := isCyclic_of_prime_card hcard
    let f : ↥(Y ⊓ V0) →* ↥Y := Subgroup.inclusion inf_le_left
    let g : ↥Y →* ↥W0 ⧸ V0.subgroupOf W0 :=
      (QuotientGroup.mk' (V0.subgroupOf W0)).comp (Subgroup.inclusion hYW)
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyV : (Subgroup.inclusion hYW y) ∈ V0.subgroupOf W0 := (QuotientGroup.eq_one_iff _).1 hy
    exact ⟨⟨y.1, Subgroup.mem_inf.2 ⟨y.2, Subgroup.mem_subgroupOf.1 hyV⟩⟩, rfl⟩

theorem uFourTwoLike_of_not_dvd_index
    {Y : Subgroup H6}
    (hY : Y ≠ ⊤) (h3 : ¬ 3 ∣ Y.index) : UFourTwoLike ↥Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine SylowOvergroup.forall_of_sylow_le T0S (fun Y => UFourTwoLike ↥Y)
    (fun g Y h => UFourTwoLike.of_mulEquiv
      (Subgroup.equivMapOfInjective Y (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm h)
    ?_ hY h3
  intro Y hTY hYtop
  have hT : T0 ≤ Y := by
    rw [← coe_T0S]
    exact hTY
  exact uFourTwoLike_of_le_W0 hT (le_W0_of_ne_top hT hYtop)

end SpSixOvergroup

theorem ggSeitzExcSpSixOvergroupInput_holds :
    GGSeitzExcSpSixOvergroupInput := by
  intro K _ _ d q hq2 hq1 hd he X hX1 h3
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := CFSG.LocalAnalysis.EvenBN.Tits.R2.nonempty_mulEquiv_H6_of_lieModel
    (ggLieModel_symplectic_two d q hq2 hq1 3 le_rfl hd e)
  exact SylowOvergroup.forall_of_mulEquiv e' (fun A _ => SpSixOvergroup.UFourTwoLike A)
    (fun A B _ _ f h => SpSixOvergroup.UFourTwoLike.of_mulEquiv f h)
    (fun Y hY h3 => SpSixOvergroup.uFourTwoLike_of_not_dvd_index hY h3) X hX1 h3

end CFSG.StandardType
