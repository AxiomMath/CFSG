module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIOuterE9
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.LieType.Ree CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


namespace Item434RowsProof

section Model

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem isElemAbelian_stdU1 :
    CFSG.Assembly.IsElemAbelian 3 (ReeModel.stdU1 a K) := by
  have hU := ReeTag.isElementaryAbelian_smallReeU1 (a := a) (K := K)
  refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · have h1 := hU.toIsMulCommutative.is_comm.comm
      ⟨((x : ReeTag.G2.reeGamma K a) : CFSG.Blueprint.Chevalley.ModGL ReeTag.G2.tag K), x.2⟩
      ⟨((y : ReeTag.G2.reeGamma K a) : CFSG.Blueprint.Chevalley.ModGL ReeTag.G2.tag K), y.2⟩
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · have hx' : ((x : ReeTag.G2.reeGamma K a) : CFSG.Blueprint.Chevalley.ModGL ReeTag.G2.tag K) ∈
        ReeTag.smallReeU1 a K := hx
    have h1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := ReeTag.smallReeU1 a K)
      _ hx'
    simpa using h1

theorem exists_elemAbelian_centralizing (hK : Nat.card K = 3 ^ (2 * a + 1))
    (E : Subgroup (ReeTag.G2.reeGamma K a)) (hE : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ D : Subgroup (ReeTag.G2.reeGamma K a), CFSG.Assembly.IsElemAbelian 3 D ∧
      Nat.card D = (3 ^ (2 * a + 1)) ^ 2 ∧ ∀ x ∈ E, ∀ d ∈ D, x * d = d * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE x x.2)⟩
  obtain ⟨T, hET⟩ := hE3.exists_le_sylow
  obtain ⟨⟨P, hP⟩, -, -, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq (MulEquiv.refl _) T P
  have hT : (T : Subgroup _).map e'.toMonoidHom = ReeModel.stdU a K := he'.trans hP
  have hU1 := isElemAbelian_stdU1 (a := a) (K := K)
  refine ⟨(ReeModel.stdU1 a K).map e'.symm.toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hU1, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e'.symm.injective, ReeModel.card_stdU1 hK]
  · rintro x hx _ ⟨u, hu, rfl⟩
    have hxU : e' x ∈ ReeModel.stdU a K := by
      rw [← hT]
      exact ⟨x, hET hx, rfl⟩
    have hx3 : e' x ^ 3 = 1 := by rw [← map_pow, hE x hx, map_one]
    have hxU1 := ReeModel.mem_stdU1_of_pow_three hK hxU hx3
    have hcomm : e' x * u = u * e' x :=
      congrArg Subtype.val (hU1.1.is_comm.comm ⟨_, hxU1⟩ ⟨u, hu⟩)
    apply e'.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
    exact hcomm

end Model

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_ree
    (h : Ctx434Core G A M Q) (hL : IsCharThreeRee (layer G ⧸ Subgroup.center (layer G))) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hr, ⟨e₀⟩⟩ := hL
  set d : TauCeti.ValidLieTypeIndex := ⟨.reeG2 1, hr⟩ with hd_def
  have hd : IsReeGTwoIndex 3 d := ⟨rfl, 1, rfl⟩
  obtain ⟨a, ha, hfe, ⟨θ₀⟩⟩ := ReeModel.exists_equiv_reeGamma hd ⟨e₀⟩
  have ha1 : a = 1 := by
    have h1 : d.1.fieldExponent = 2 * 1 + 1 := TauCeti.LieTypeIndex.fieldExponent_reeG2 1
    omega
  subst ha1
  set K := GaloisField 3 (2 * 1 + 1) with hK_def
  have hK : Nat.card K = 3 ^ (2 * 1 + 1) := GaloisField.card 3 (2 * 1 + 1) (by omega)
  set Γ := ReeTag.G2.reeGamma K 1 with hΓ
  set θ : layer G ⧸ Subgroup.center (layer G) ≃* Γ := θ₀ with hθ
  have hq : CFSG.Open.IsQuasisimple (layer G) :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).mp h.isQuasisimple
  have hZ : Subgroup.center (layer G) = ⊥ :=
    kFactReeSchur (layer G) d hd hq h.isPGroup_center_layer ⟨e₀⟩
  have hU1 := isElemAbelian_stdU1 (a := 1) (K := K)
  have hU1c := ReeModel.card_stdU1 (a := 1) hK
  obtain ⟨D₀, hD₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := ReeModel.stdU1 1 K) (n := 3)
    (by rw [hU1c]; norm_num)
  have hD : CFSG.Assembly.IsElemAbelian 3 (D₀.map (ReeModel.stdU1 1 K).subtype) :=
    Source.isElemAbelian_of_le hU1 (Subgroup.map_subtype_le D₀)
  have hD27 : Nat.card (D₀.map (ReeModel.stdU1 1 K).subtype) = 27 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hD₀]
    norm_num
  have hCA := Item434Kit.inf_centralizer_layer_eq_bot h hZ θ hD hD27
  have hA27 := Item434Kit.card_map_quotConj h hCA θ
  have hAe := Item434Kit.isElemAbelian_map_quotConj h θ
  have hZΓ : Subgroup.center Γ = ⊥ := ReeTag.center_reeGamma_G2_eq_bot hK
  have hO : Nat.card (Outer Γ) < 9 := by
    rw [(CFSG.ComponentClassification.LiteratureLocal.SmallRee.outer_reeGamma_cyclic
      (a := 1) (K := K) le_rfl hK).2]
    norm_num
  obtain ⟨E, hEe, hE9, hEA⟩ :=
    Item434SmallTwoIII.exists_map_conj_le_of_card_27 hZΓ hO hAe hA27
  obtain ⟨D, hDe, hDc, hDcomm⟩ := exists_elemAbelian_centralizing hK E hEe.2
  set F : Subgroup (MulAut Γ) := E.map (MulAut.conj : Γ →* MulAut Γ) with hF
  have hF9 : 9 ≤ Nat.card F := by
    rw [hF, Subgroup.card_map_of_injective (Item434Kit.conj_injective_of_center_eq_bot hZΓ),
      hE9]
  have hB9 := hF9.trans (Item434Kit.card_le_card_inf_comap θ hEA)
  refine Item434Kit.false_of_fixed h hZ θ inf_le_left hB9 hDe (by rw [hDc]; norm_num) ?_
  rintro b ⟨-, x, hx, hxb⟩ y hy
  rw [← hxb, MulAut.conj_apply, hDcomm x hx y hy, mul_inv_cancel_right]

end Item434RowsProof

open Item434RowsProof

section Families


theorem item434CharThreeRee : Item434CharThreeRee := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  exact (false_of_ree hc hL).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
