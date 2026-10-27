module

public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensusJ2
import CFSG.RankThree.PartTwo.KFacts.KS10L27
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GorensteinWalter (PSL2 psl2UpperUnipotentSubgroup)

namespace Res423L29

theorem eq_two_of_maximal {e : ℕ} (he : 1 ≤ e) {X : Type} [Group X] [Finite X]
    (φ : X ≃* PSL2 (GaloisField 3 e)) {D : Subgroup X}
    (hD : Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D)
    (hD9 : Nat.card D = 9) : e = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 e) = 3 ^ e := GaloisField.card 3 e (by omega)
  have hD'p : IsPGroup 3 (D.map φ.toMonoidHom) :=
    (Sec5.isPGroup_of_isElemAbelian hD.prop).map _
  obtain ⟨c, hc⟩ := KFacts.exists_map_conj_le_psl2UpperUnipotentSubgroup hK hD'p
  set U := psl2UpperUnipotentSubgroup (GaloisField 3 e) with hU
  set U' := (U.map (MulAut.conj c⁻¹).toMonoidHom).map φ.symm.toMonoidHom with hU'
  have hDU' : D ≤ U' := by
    intro x hx
    have h1 : c * φ x * c⁻¹ ∈ U := hc ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨c⁻¹ * (c * φ x * c⁻¹) * c⁻¹⁻¹, ⟨_, h1, rfl⟩, ?_⟩
    change φ.symm (c⁻¹ * (c * φ x * c⁻¹) * c⁻¹⁻¹) = x
    rw [show c⁻¹ * (c * φ x * c⁻¹) * c⁻¹⁻¹ = φ x by group, MulEquiv.symm_apply_apply]
  have hUe : CFSG.Assembly.IsElemAbelian 3 U := by
    refine ⟨⟨⟨fun a b => Subtype.ext (KFacts.psl2Upper_mul_comm a.2 b.2)⟩⟩, fun x hx => ?_⟩
    exact KFacts.psl2Upper_pow_three hx
  have hU'e : CFSG.Assembly.IsElemAbelian 3 U' :=
    isElemAbelian_map _ (isElemAbelian_map _ hUe)
  have heq : D = U' := le_antisymm hDU' (hD.2 hU'e hDU')
  have hU'card : Nat.card U' = 3 ^ e := by
    rw [hU', Subgroup.card_map_of_injective φ.symm.injective,
      Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hU,
      GorensteinWalter.psl2UpperUnipotentSubgroup_card, hK]
  rw [← heq, hD9] at hU'card
  have h32 : 3 ^ e = 3 ^ 2 := by rw [← hU'card]; norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h32

end Res423L29

open Res423L29

theorem k423Inner46OneThree_of (h4 : K423Inner46Four) : K423Inner46OneThree := by
  rintro X _ _ ⟨e, he, ⟨φ⟩⟩ hq hZ hSL D hD hD9 Y hY hα
  have he2 := eq_two_of_maximal he (φ.trans (projSLEquivPSL _)) hD hD9
  subst he2
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  obtain ⟨e6⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      (GaloisField 3 2) (by
        rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
        norm_num)
  exact h4 X (Or.inl ⟨6, by norm_num, ⟨(φ.trans (projSLEquivPSL _)).trans e6⟩⟩) hq hZ hSL D hD
    hD9 Y hY hα

theorem k423InnerCensus_of_rest''
    (h3 : K423Inner46Three) (h4 : K423Inner46Four) (h5 : K423Inner46FiveRest)
    (h6 : K423Inner46SixRest) (h7 : K423Inner46Seven) (h8 : K423Inner46Eight) :
    K423InnerCensus :=
  k423InnerCensus_of_rest' (k423Inner46OneThree_of h4) h3 h4 h5 h6 h7 h8

end CFSG.RankThree.PartTwo.Sec4
