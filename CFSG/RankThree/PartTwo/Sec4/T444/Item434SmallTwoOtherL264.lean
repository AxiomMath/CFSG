module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL264Tools
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIKit
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearCover
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L264

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores CFSG.GorensteinWalter
open CFSG.Open (signalizerFixedSubgroup)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedScalars StatedSL)
open Item434Kit Item434Alt

theorem card_eq_nine_and_closure_fixed_eq_top
    {E : Subgroup (MulAut (PSL2 (GaloisField 2 6)))} (hE : ∀ α ∈ E, α ^ 3 = 1)
    (h9 : 9 ≤ Nat.card E) :
    Nat.card E = 9 ∧
      Subgroup.closure {x : PSL2 (GaloisField 2 6) | ∃ ψ ∈ E, ψ ≠ 1 ∧ ψ x = x} = ⊤ := by
  set ψ : MulAut (PSL2 (GaloisField 2 6)) →* (GaloisField 2 6 ≃+* GaloisField 2 6) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut (GaloisField 2 6)).symm.toMonoidHom
  have hker : Nat.card (E ⊓ ψ.ker : Subgroup _) ≤ 3 :=
    card_le_three_of_le_range_pglAction (fun α hα => hE α hα.1) fun α hα =>
      CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hα.2
  have himg : Nat.card (E.map ψ) ≤ 3 := card_map_rightHom_le_three hE
  have hcard := card_eq_card_inf_ker_mul_card_map ψ E
  have hE9 : Nat.card E = 9 := by
    have : Nat.card E ≤ 3 * 3 := by rw [hcard]; exact Nat.mul_le_mul hker himg
    omega
  have hker3 : 3 ≤ Nat.card (E ⊓ ψ.ker : Subgroup _) := by
    by_contra hlt
    have : Nat.card E ≤ 2 * 3 := by rw [hcard]; exact Nat.mul_le_mul (by omega) himg
    omega
  refine ⟨hE9, ?_⟩
  obtain ⟨c, hcE, hc1⟩ : ∃ c ∈ E ⊓ ψ.ker, c ≠ 1 := by
    rcases (E ⊓ ψ.ker).bot_or_exists_ne_one with hbot | h
    · rw [hbot, Subgroup.card_bot] at hker3
      omega
    · exact h
  obtain ⟨t, rfl⟩ : c ∈ (MulAut.conj : PSL2 (GaloisField 2 6) →* _).range :=
    CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_mem_inndiag_of_pow_three
      (CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one hcE.2) (hE _ hcE.1)
  have ht3 : t ^ 3 = 1 := conj_injective_psl2 _ (by rw [map_pow, map_one]; exact hE _ hcE.1)
  obtain ⟨φ, hφE, hφ⟩ : ∃ φ ∈ E, φ ∉ (pglAction (GaloisField 2 6)).range := by
    by_contra hcon
    push Not at hcon
    have := card_le_three_of_le_range_pglAction hE fun α hα => hcon α hα
    omega
  have hφ1 : φ ≠ 1 := fun h => hφ (h ▸ Subgroup.one_mem _)
  obtain ⟨hcoat, h60⟩ := isCoatom_and_card_fixed (hE φ hφE) hφ
  have hfixH : signalizerFixedSubgroup φ ≤
      Subgroup.closure {x : PSL2 (GaloisField 2 6) | ∃ ψ ∈ E, ψ ≠ 1 ∧ ψ x = x} := fun x hx =>
    Subgroup.subset_closure ⟨φ, hφE, hφ1, hx⟩
  obtain ⟨R, hR9, hRt⟩ := exists_sylow_commute ht3
  have hRH : R ≤ Subgroup.closure {x : PSL2 (GaloisField 2 6) | ∃ ψ ∈ E, ψ ≠ 1 ∧ ψ x = x} :=
    fun r hr => Subgroup.subset_closure ⟨MulAut.conj t, hcE.1, hc1, by
      rw [MulAut.conj_apply, ← hRt r hr, mul_inv_cancel_right]⟩
  have hne : signalizerFixedSubgroup φ ≠
      Subgroup.closure {x : PSL2 (GaloisField 2 6) | ∃ ψ ∈ E, ψ ≠ 1 ∧ ψ x = x} := by
    intro heq
    have hdvd := Subgroup.card_dvd_of_le (hRH.trans heq.symm.le)
    rw [h60] at hdvd
    have := hR9.trans hdvd
    omega
  exact hcoat.lt_iff.mp (lt_of_le_of_ne hfixH hne)

theorem statedScalars_subgroupOf_eq_bot :
    (StatedScalars (Fin 2) (GaloisField 2 6)).subgroupOf (StatedSL 2 (GaloisField 2 6)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hdet : Matrix.GeneralLinearGroup.det (x : GL (Fin 2) (GaloisField 2 6)) = 1 :=
    MonoidHom.mem_ker.mp
      ((CFSG.RankThree.PartTwo.Census.statedSL_eq_ker_det 2 (GaloisField 2 6)).le x.2)
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hc2 : ((c : GaloisField 2 6)) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hdet, Units.val_one]
  have hc1 : c = 1 := Units.ext (CharTwo.sq_injective (by simpa using hc2))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot
    (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL 2 (GaloisField 2 6)) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨φ, -, -, hD⟩ := CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map
    (K := GaloisField 2 6) (n := 2) le_rfl hodd
    (e.trans ((MulEquiv.subgroupCongr
      (CFSG.RankThree.PartTwo.Census.projImage_statedSL 2 (GaloisField 2 6))).symm.trans
      (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
        (StatedSL 2 (GaloisField 2 6))).symm))
  rw [← hD, statedScalars_subgroupOf_eq_bot, Subgroup.map_bot]

theorem false_of_ctx
    (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL 2 (GaloisField 2 6)) : False := by
  have hZ := center_layer_eq_bot h e
  set e₀ := e.trans (Sec4.projSLEquivPSL (GaloisField 2 6))
  have hEcard : Nat.card (A.map (quotConj e₀)) = Nat.card h.layerStar :=
    Item434Spor.card_map_quotConj h e₀
  have h9le : 9 ≤ Nat.card (A.map (quotConj e₀)) := by
    rw [hEcard]
    rcases h.card_layerStar with h9 | ⟨h27, -⟩ <;> omega
  obtain ⟨hE9, hgen⟩ := card_eq_nine_and_closure_fixed_eq_top
    (isElemAbelian_map_quotConj h e₀).2 h9le
  have h9 : Nat.card (A.map (layerConj G)) = 9 := by
    rw [← hE9, hEcard]
  apply h.not_le
  refine Item434SmallTwoIII.layer_le_of_closure_fixed h h9 ?_
  set ι := layerEquiv e₀ hZ
  have hsub : {x : PSL2 (GaloisField 2 6) | ∃ ψ ∈ A.map (quotConj e₀), ψ ≠ 1 ∧ ψ x = x} ⊆
      ι.toMonoidHom '' {y : layer G | ∃ φ ∈ A.map (layerConj G), φ ≠ 1 ∧ φ y = y} := by
    rintro x ⟨_, ⟨a, ha, rfl⟩, hψ1, hψx⟩
    refine ⟨ι.symm x, ⟨layerConj G a, ⟨a, ha, rfl⟩, fun h1 => hψ1 ?_, ?_⟩,
      ι.apply_symm_apply x⟩
    · exact (quotConj_eq_one_iff h.isQuasisimple e₀).mpr (layerConj_eq_one_iff.mp h1)
    · apply layerQuot_injective e₀ hZ
      rw [← quotConj_layerQuot]
      have hx' : layerQuot e₀ (ι.symm x) = x := ι.apply_symm_apply x
      rw [hx', hψx]
  have htop : (⊤ : Subgroup (PSL2 (GaloisField 2 6))) ≤ (Subgroup.closure
      {y : layer G | ∃ φ ∈ A.map (layerConj G), φ ≠ 1 ∧ φ y = y}).map ι.toMonoidHom := by
    rw [← hgen, MonoidHom.map_closure]
    exact Subgroup.closure_mono hsub
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := htop (Subgroup.mem_top (ι y))
  rwa [ι.injective hzy] at hz

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L264

namespace CFSG.RankThree.PartTwo.Sec4

section Families


theorem item434SmallTwoOtherAtL264 : Item434SmallTwoOtherAtL264 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.L264.false_of_ctx hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
