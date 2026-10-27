module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData
public import CFSG.LocalAnalysis.StandardType.SylowOvergroupReduction
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcSolv
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalViso
public import Certificates.Certificate465001
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.L32NKGSp6Group
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Recognition.RuTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType.UFourTwoSylow

open CFSG.KGroups.Sp6 CFSG.Quasithin.G2U CFSG.AGLEmbedding.KFactProofs.Sp62Local
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem order5_cover
    {x : H6} (hx : x ∈ V0) (hx1 : x ≠ 1) (hx5 : x ^ 5 = 1) :
    V0 ≤ T0 ⊔ Subgroup.zpowers x :=
  Certificates.certificate465001 x hx hx1 hx5

theorem isSolvable_of_le_V0
    {Y : Subgroup H6} (hT : T0 ≤ Y) (hV : Y ≤ V0)
    (hne : Y ≠ V0) : Group.IsSolvable ↥Y := by
  have hcardV : Nat.card V0 = 2 ^ 6 * 3 ^ 4 * 5 := by rw [card_V0]; norm_num
  have hdvd : Nat.card Y ∣ 2 ^ 6 * 3 ^ 4 * 5 := hcardV ▸ Subgroup.card_dvd_of_le hV
  refine CFSG.StandardType.SylowOvergroup.isSolvable_of_coprime hdvd ?_
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 fun h5 => ?_)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hx5 : (y : H6) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    exact congrArg Subtype.val h
  have hx1 : (y : H6) ≠ 1 := by
    intro h
    have hy1 : y = 1 := Subtype.ext h
    rw [hy1, orderOf_one] at hy
    omega
  have hcov := order5_cover (hV y.2) hx1 hx5
  refine hne (le_antisymm hV (hcov.trans (sup_le hT ?_)))
  rw [Subgroup.zpowers_le]
  exact y.2

end CFSG.StandardType.UFourTwoSylow

namespace CFSG.StandardType

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.StandardType.UFourTwoSylow

theorem isSolvable_of_not_dvd_index_V0
    {X : Subgroup ↥V0} (hX : X ≠ ⊤) (h3 : ¬ 3 ∣ X.index) :
    Group.IsSolvable ↥X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : T0 ≤ V0 := T0_le_V0
  have hcardP : Nat.card (T0.subgroupOf V0) = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv, card_T0]
  have hidx : ¬ 3 ∣ (T0.subgroupOf V0).index := by
    have h := Subgroup.card_mul_index (T0.subgroupOf V0)
    rw [hcardP, card_V0] at h
    omega
  let P : Sylow 3 ↥V0 := (IsPGroup.of_card hcardP).toSylow hidx
  have hP : (P : Subgroup ↥V0) = T0.subgroupOf V0 := IsPGroup.toSylow_coe _ _
  refine CFSG.StandardType.SylowOvergroup.forall_of_sylow_le P (fun Y => Group.IsSolvable ↥Y)
    ?_ ?_ hX h3
  · intro g Y hY
    exact CFSG.StandardType.SylowOvergroup.isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective Y (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hY
  · intro Y hPY hYtop
    rw [hP] at hPY
    have hTY : T0 ≤ Y.map V0.subtype := by
      intro t ht
      exact ⟨⟨t, hT ht⟩, hPY (Subgroup.mem_subgroupOf.2 ht), rfl⟩
    have hYV : Y.map V0.subtype ≤ V0 := Subgroup.map_subtype_le Y
    have hne : Y.map V0.subtype ≠ V0 := by
      intro heq
      refine hYtop (eq_top_iff.2 fun g _ => ?_)
      have hg : (g : H6) ∈ Y.map V0.subtype := by
        rw [heq]
        exact g.2
      obtain ⟨y, hy, hyg⟩ := hg
      rwa [← Subtype.ext hyg]
    exact CFSG.StandardType.SylowOvergroup.isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective Y V0.subtype V0.subtype_injective)
      (isSolvable_of_le_V0 hTY hYV hne)

theorem ggSeitzExcUFourTwoInput_holds :
    GGSeitzExcUFourTwoInput := by
  intro K _ _ d q hq2 hq1 hd he
  obtain ⟨e⟩ := he
  obtain rfl : d = u42Index := Subtype.ext (hd.trans (by
    rw [TauCeti.PrimePower.ext (y := q2) hq2 hq1]; rfl))
  obtain ⟨e'⟩ := nonempty_V0_mulEquiv_catGroup
  exact CFSG.StandardType.SylowOvergroup.forall_isSolvable_of_mulEquiv (e.trans e'.symm)
    fun X hX h3 => isSolvable_of_not_dvd_index_V0 hX h3

end CFSG.StandardType
