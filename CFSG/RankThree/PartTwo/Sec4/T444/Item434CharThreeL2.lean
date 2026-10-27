module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL2Tools
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Matrix
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.GorensteinWalter (PSL2 PGL2)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction)
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

namespace Item434CharThree

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_isQuasisimple_of_isSolvable {X : Type} [Group X] (hq : IsQuasisimple X)
    (hs : Group.IsSolvable (X ⧸ Subgroup.center X)) : False := by
  have : Group.IsPerfect X := hq.1
  have : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have : Nontrivial (X ⧸ Subgroup.center X) := IsSimpleGroup.toNontrivial
  exact Group.IsPerfect.not_isSolvable (X ⧸ Subgroup.center X) hs

theorem false_of_projSL_two_three (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSL 2 (GaloisField 3 1)) : False := by
  have hs : Group.IsSolvable (ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 1)) :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_psl2_galoisField_three_one
  set θ := e₀.trans (projSLEquivPSL (GaloisField 3 1))
  exact false_of_isQuasisimple_of_isSolvable h.isQuasisimple
    (Group.isSolvable_of_surjective (f := θ.symm.toMonoidHom) θ.symm.surjective)

theorem false_of_projSL_two_nine (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSL 2 (GaloisField 3 2)) : False := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨ψ⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
    (GaloisField 3 2) hK
  exact Item434Alt.false_of_alt_six h ((e₀.trans (projSLEquivPSL (GaloisField 3 2))).trans ψ)

theorem isElemAbelian_comap_map_conj_unipPGL {e : ℕ} (he : e ≠ 0) (h₀ : PGL2 (GaloisField 3 e)) :
    CFSG.Assembly.IsElemAbelian 3 (((unipPGL (GaloisField 3 e)).map
        (MulAut.conj h₀).toMonoidHom).comap ProjectiveSpecialLinearGroup.toPGL) ∧
      Nat.card (((unipPGL (GaloisField 3 e)).map
        (MulAut.conj h₀).toMonoidHom).comap ProjectiveSpecialLinearGroup.toPGL) = 3 ^ e := by
  set W' := (unipPGL (GaloisField 3 e)).map (MulAut.conj h₀).toMonoidHom with hW'
  have hmap : (W'.comap ProjectiveSpecialLinearGroup.toPGL).map
      ProjectiveSpecialLinearGroup.toPGL = W' :=
    Subgroup.map_comap_eq_self (map_conj_unipPGL_le_range h₀)
  have hW'e : CFSG.Assembly.IsElemAbelian 3 W' :=
    ⟨⟨⟨fun a b => Subtype.ext (map_conj_unipPGL_commute a.2 b.2)⟩⟩,
      fun x hx => pow_three_eq_one_of_mem_map_conj hx⟩
  refine ⟨Item434Kit.isElemAbelian_of_map_injective
    ProjectiveSpecialLinearGroup.toPGL_injective (by rw [hmap]; exact hW'e), ?_⟩
  rw [← Subgroup.card_map_of_injective ProjectiveSpecialLinearGroup.toPGL_injective, hmap, hW',
    Subgroup.card_map_of_injective (MulAut.conj h₀).injective, card_unipPGL_galois he]

theorem false_of_projSL_two_large (h : Ctx434Core G A M Q) {e : ℕ} (he : 3 ≤ e)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSL 2 (GaloisField 3 e)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := GaloisField 3 e with hK
  set θ : layer G ⧸ Subgroup.center (layer G) ≃* PSL2 K := e₀.trans (projSLEquivPSL K) with hθ
  have h27 : 3 ^ 3 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have h9 : 3 ^ e ≠ 9 := by omega
  have hq : CFSG.Open.IsQuasisimple (layer G) :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).mp h.isQuasisimple
  have hZ := AGLEmbedding.center_eq_bot_of_center_quotient_psl2 (p := 3) (n := e) (by norm_num)
    (by omega) h9 hq h.isPGroup_center_layer θ
  obtain ⟨U⟩ : Nonempty (Sylow 3 (PSL2 K)) := inferInstance
  obtain ⟨hUe, hUc⟩ := AGLEmbedding.psl2GF_sylow 3 e (by omega) U
  obtain ⟨D₀, hD₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := (U : Subgroup (PSL2 K)))
    (n := 3) (by rw [hUc]; exact pow_dvd_pow 3 he)
  have hD : CFSG.Assembly.IsElemAbelian 3 (D₀.map (U : Subgroup (PSL2 K)).subtype) :=
    Source.isElemAbelian_of_le ⟨hUe.1, hUe.2⟩ (Subgroup.map_subtype_le D₀)
  have hD27 : Nat.card (D₀.map (U : Subgroup (PSL2 K)).subtype) = 27 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hD₀]
    norm_num
  have hCA := Item434Kit.inf_centralizer_layer_eq_bot h hZ θ hD hD27
  have hA27 := Item434Kit.card_map_quotConj h hCA θ
  have hAe := Item434Kit.isElemAbelian_map_quotConj h θ
  rcases (show e = 3 ∨ 4 ≤ e by omega) with rfl | he4
  ·
    exact Item434Kit.false_of_normalizer h θ fun Y hY3 hAY =>
      eq_bot_of_le_normalizer_twentySeven hAe hA27 hY3 hAY
  ·
    obtain ⟨P, h₀, hPW, hP9, hPE⟩ := exists_pgl_part (by omega) hAe hA27
    have hF9 : 9 ≤ Nat.card (P.map (pglAction K)) := by
      rw [Subgroup.card_map_of_injective (pglAction_injective K)]
      exact hP9
    have hB9 := hF9.trans (Item434Kit.card_le_card_inf_comap θ hPE)
    obtain ⟨hDe, hDc⟩ := isElemAbelian_comap_map_conj_unipPGL (by omega) h₀
    have h81 : 3 ^ 4 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he4
    refine Item434Kit.false_of_fixed h hZ θ inf_le_left hB9 hDe (by rw [hDc]; omega) ?_
    rintro b ⟨-, g, hgP, hg⟩ d hd
    rw [← hg]
    apply ProjectiveSpecialLinearGroup.toPGL_injective
    rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.toPGL_pglAction,
      map_conj_unipPGL_commute (hPW hgP) hd, mul_inv_cancel_right]

end Item434CharThree

open Item434CharThree

section Families


theorem item434CharThreeL2Three : Item434CharThreeL2Three := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (false_of_projSL_two_three hc e₀).elim

theorem item434CharThreeL2Nine : Item434CharThreeL2Nine := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (false_of_projSL_two_nine hc e₀).elim

theorem item434CharThreeL2Large : Item434CharThreeL2Large := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e, he, ⟨e₀⟩⟩ := hL
  exact (false_of_projSL_two_large hc he e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
